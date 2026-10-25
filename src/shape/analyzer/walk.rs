use super::*;
impl Analyzer {
    pub(super) fn probe(&mut self, rec: Gate, slot: u8) {
        if rec.on() {
            trace::compiler_trace_signal(slot);
        } else {
            self.walk.conv_fires.insert(slot);
        }
    }

    pub(super) fn note_adopt(&mut self, site: usize, line: usize) {
        match self.lattice.adopt_witness.entry(site) {
            std::collections::btree_map::Entry::Occupied(mut e) => {
                if line < *e.get() {
                    e.insert(line);
                }
            }
            std::collections::btree_map::Entry::Vacant(e) => {
                e.insert(line);
            }
        }
    }

    pub(super) fn note_adopt_if_flipping(
        &mut self,
        rec: Gate,
        site: usize,
        vt: &Ty,
        line: Option<usize>,
    ) {
        let cur = self.lattice.site_elem[site].clone();
        if !matches!(cur, Any) && matches!(join_ty(&cur, vt), Any) {
            self.probe(rec, trace::TRACE_ANY_NAME_ADOPTED);
            if let Some(l) = line {
                self.note_adopt(site, l);
            }
        }
    }

    pub(super) fn walk_stmts(&mut self, rec: Gate, stmts: &[Stmt]) {
        for s in stmts {
            if let Err(err) = self.walk_stmt(rec, s) {
                signal!(rec.on(), trace::TRACE_GHOST_BAIL);
                let line = self.stmt_lines.get(&(s as *const Stmt)).copied();
                self.ledger.diagnostics.push(match line {
                    Some(l) => format!("line {l}: {}", err.0),
                    None => err.0,
                });
                return;
            }
        }
    }

    pub(super) fn walk_stmt(&mut self, rec: Gate, stmt: &Stmt) -> Result<(), ShapeError> {
        match stmt {
            Stmt::LocalDecl { names, exprs } => {
                let mut sets = Vec::with_capacity(names.len());
                let mut moved_srcs: Vec<(usize, String)> = Vec::new();
                for (name, expr) in names.iter().zip(exprs.iter()) {
                    let ptr = match expr {
                        Expr::Function { .. } => Some(expr as *const Expr),
                        _ => None,
                    };
                    self.declare_fn_binding(name, ptr);
                }
                for name in &names[exprs.len()..] {
                    self.declare_fn_binding(name, None);
                }
                let note_move = |an: &mut Self,
                                 src: &str,
                                 target: &str,
                                 moved: &mut Vec<(usize, String)>|
                 -> Result<(), ShapeError> {
                    if src == target {
                        return Ok(());
                    }
                    let (d, bind) = an.resolve(rec, src)?;
                    an.record_moved_param(src);
                    an.check_boundary_pin(&bind, src)?;
                    if matches!(bind.ty, Tbl(_)) {
                        if moved.iter().any(|(_, m)| m == src) {
                            return Err(ShapeError(format!(
                                "Lifetime Error: '{src}' is moved more than once — one table \
                                 value has exactly one receiving binding"
                            )));
                        }
                        moved.push((d, src.to_string()));
                    }
                    Ok(())
                };
                for (name, expr) in names.iter().zip(exprs.iter()) {
                    if let Expr::Identifier(src) = expr {
                        note_move(self, src, name, &mut moved_srcs)?;
                    }
                }
                for (idx, expr) in exprs.iter().enumerate() {
                    // the scalar-node bookkeeping mirrors the checker's
                    // scope entry: an RHS riding a shared unknown node
                    // (bare alias, boundary cell, pending-site read, fn
                    // return) binds that node to the name
                    self.note_decl_scalar_node(&names[idx], expr);
                    if matches!(expr, Expr::Nil) {
                        signal!(rec.on(), trace::TRACE_BIND_SCALAR);
                        sets.push(TableShape {
                            ty: Pending,
                            layout: LayoutVerdict::default(),
                            aliases: BTreeSet::from([NULL_ROOT]),
                            lineage: BTreeMap::new(),
                        });
                    } else if let Expr::Function { params, body } = expr {
                        self.walk_fn_def(
                            rec,
                            expr as *const Expr,
                            params,
                            body,
                            (stmt as *const Stmt, 2 + idx as u8),
                        )?;
                        sets.push(TableShape {
                            ty: Pending,
                            layout: LayoutVerdict::default(),
                            aliases: BTreeSet::new(),
                            lineage: BTreeMap::new(),
                        });
                    } else {
                        let bind = self.infer_bind(rec, expr)?;
                        if matches!(expr, Expr::Field { .. } | Expr::Index { .. })
                            && matches!(bind.ty, Conflict)
                        {
                            crate::alm_dbgln!(
                                "[localdecl] '{}' bound to Conflict aliases={:?}",
                                names[idx],
                                bind.aliases
                            );
                        }
                        self.check_uses(rec, expr)?;
                        self.collect_entry_moves(rec, expr, &mut moved_srcs)?;
                        if value_kind(&bind.ty) {
                            signal!(rec.on(), trace::TRACE_BIND_SCALAR);
                        } else if matches!(expr, Expr::TableCtor(_)) {
                            signal!(rec.on(), trace::TRACE_BIND_HEAP);
                        }
                        sets.push(bind);
                    }
                }
                while sets.len() < names.len() {
                    signal!(rec.on(), trace::TRACE_BIND_SCALAR);
                    // anchor the bare declaration's identity node in the
                    // lattice's unknown store — the checking half's
                    // declare reads (and, defensively, mints) the same
                    // node, one per declaration across every pass. Bare
                    // decls do NOT register in scalar_nodes: the
                    // nil-poison law rejects every read through a bare
                    // name before a use-site pin could fire, so the node
                    // only ever closes via assignment unification.
                    self.lattice
                        .unknowns
                        .ensure_bare_node(stmt, &names[sets.len()]);
                    sets.push(TableShape {
                        ty: Pending,
                        layout: LayoutVerdict::default(),
                        aliases: BTreeSet::from([NULL_ROOT]),
                        lineage: BTreeMap::new(),
                    });
                }

                for (name, expr) in names.iter().zip(exprs.iter()) {
                    self.holds
                        .num_assigns
                        .insert(name.clone(), vec![num_of(expr)]);
                }

                let depth = self.walk.scopes.len() - 1;
                for (idx, (name, set)) in names.iter().zip(sets).enumerate() {
                    if let Some(old) = self.walk.scopes.last().and_then(|s| s.get(name)).cloned() {
                        self.rebind_death(rec, name, depth, stmt, &old, &set.aliases)?;
                    }
                    // a fresh declaration is a fresh name: no severed
                    // elem history carries over the shadowing
                    self.holds.nil_severed.remove(name);
                    self.holds.moved_severed.remove(name);
                    self.check_row_ownership(name, depth, &set, &moved_srcs)?;
                    let prov = self.prov_for_bind(exprs.get(idx), &set);
                    let scope = self.walk.scopes.last_mut().unwrap();
                    scope.insert(name.clone(), set);
                    self.walk.prov[depth].insert(name.clone(), prov);
                }
                for (d, src) in &moved_srcs {
                    self.poison_moved(*d, src);
                }
                if rec.on() {
                    let entry = self
                        .own
                        .move_poisons
                        .entry(stmt as *const Stmt)
                        .or_default();
                    for (_, src) in &moved_srcs {
                        entry.insert(src.clone());
                    }
                }
            }

            Stmt::Assignment { name, expr } => {
                let entry = self.holds.num_assigns.entry(name.clone()).or_default();
                let shape = num_of(expr);
                if !entry.contains(&shape) {
                    entry.push(shape);
                }
                if let Expr::Function { params, body } = expr {
                    self.assign_fn_binding(name, Some(expr as *const Expr));
                    self.walk_fn_def(
                        rec,
                        expr as *const Expr,
                        params,
                        body,
                        (stmt as *const Stmt, 2),
                    )?;
                } else {
                    self.assign_fn_binding(name, None);
                }
                if matches!(expr, Expr::Nil) {
                    signal!(rec.on(), trace::TRACE_STMT_ASSIGN_NIL);
                    self.note_assign_scalar_node(name, expr);
                    self.drop_reference(rec, name, stmt)?;
                    return Ok(());
                }
                let bind = self.infer_bind(rec, expr)?;
                self.note_assign_scalar_node(name, expr);
                self.check_uses(rec, expr)?;
                let mut moved_srcs: Vec<(usize, String)> = Vec::new();
                if let Expr::Identifier(src) = expr {
                    if src != name {
                        self.record_moved_param(src);
                        self.check_boundary_pin(&bind, src)?;
                        if matches!(bind.ty, Tbl(_)) {
                            let (d, _) = self.resolve(rec, src)?;
                            moved_srcs.push((d, src.clone()));
                        }
                    }
                } else {
                    self.collect_entry_moves(rec, expr, &mut moved_srcs)?;
                }
                if value_kind(&bind.ty) {
                    signal!(rec.on(), trace::TRACE_BIND_SCALAR);
                } else if matches!(expr, Expr::TableCtor(_)) {
                    signal!(rec.on(), trace::TRACE_BIND_HEAP);
                }

                if matches!(bind.ty, Tbl(_)) {
                    signal!(rec.on(), trace::TRACE_STMT_ASSIGN_TBL);
                    let mut incoming = Pending;
                    for s in &bind.aliases {
                        if !is_root(s) && !is_ghost(s) {
                            signal!(rec.on(), trace::TRACE_STMT_ASSIGN_TBL_VALID);
                            incoming = join_ty(&incoming, &self.lattice.site_elem[*s]);
                        }
                    }
                    let line = self.stmt_lines.get(&(stmt as *const Stmt)).copied();
                    let mut old: BTreeSet<usize> = self
                        .resolve_aliases(rec, name)?
                        .into_iter()
                        .filter(|s| !is_root(s) && !is_ghost(s))
                        .collect();
                    // the sites a `t = nil` severed from the name ride
                    // along: the type slot survives the nil, so adoption
                    // bridges the elem history both ways across it. A
                    // move (`local u = t`) severs the same way — the
                    // slot survives the move, the history bridges.
                    old.extend(
                        self.holds
                            .nil_severed
                            .get(name)
                            .into_iter()
                            .flatten()
                            .copied(),
                    );
                    old.extend(
                        self.holds
                            .moved_severed
                            .get(name)
                            .into_iter()
                            .flatten()
                            .copied(),
                    );
                    let old: Vec<usize> = old.into_iter().collect();
                    let mut old_sum = Pending;
                    for s in &old {
                        old_sum = join_ty(&old_sum, &self.lattice.site_elem[*s]);
                    }
                    // The scalar adoption: a scalar (or Any) mix joins
                    // the name's site history to the incoming kind —
                    // every flat program replays this exactly.
                    // NESTED-table mixes (the elem history rides one
                    // level down — `t = {{1}}; t = {{2.5}}` joins
                    // Tbl(Int) with Tbl(Flt) to Tbl(Any) on both sites,
                    // the ctor arm's mixed-rows promotion carries Any
                    // into the inner sites on the next pass) adopt under
                    // two hard guards: the elem must be FULLY DECIDED (a
                    // Pending inside means a self-referential ctor is
                    // still forming — adopting it grows the nesting one
                    // level per pass and the fixpoint never converges;
                    // the cyclic_ctor_assign_rejected case), and each
                    // site's join must be CLEAN (a shape mismatch —
                    // scalar elem vs table elem — stays the site
                    // Conflict / the checker's unify refusal, not ours
                    // to preempt).
                    let nested = |t: &Ty| matches!(t, Tbl(_) if decided(t));
                    let joins_clean = |cur: &Ty, vt: &Ty| !matches!(join_ty(cur, vt), Conflict);
                    if value_kind(&incoming) {
                        signal!(rec.on(), trace::TRACE_STMT_ASSIGN_TBL_SCALAR);
                        for s in old {
                            signal!(rec.on(), trace::TRACE_STMT_ASSIGN_TBL_SCALAR_VALID);
                            self.note_adopt_if_flipping(rec, s, &incoming, line);
                            self.decide(rec, s, &incoming);
                        }
                    } else if nested(&incoming) {
                        for s in old {
                            if joins_clean(&self.lattice.site_elem[s], &incoming) {
                                signal!(rec.on(), trace::TRACE_STMT_ASSIGN_TBL_SCALAR);
                                signal!(rec.on(), trace::TRACE_STMT_ASSIGN_TBL_SCALAR_VALID);
                                self.note_adopt_if_flipping(rec, s, &incoming, line);
                                self.decide(rec, s, &incoming);
                            }
                        }
                    }
                    if value_kind(&old_sum) {
                        for s in &bind.aliases {
                            if !is_root(s) && !is_ghost(s) {
                                self.note_adopt_if_flipping(rec, *s, &old_sum, line);
                                self.decide(rec, *s, &old_sum);
                            }
                        }
                    } else if nested(&old_sum) {
                        for s in &bind.aliases {
                            if !is_root(s)
                                && !is_ghost(s)
                                && joins_clean(&self.lattice.site_elem[*s], &old_sum)
                            {
                                self.note_adopt_if_flipping(rec, *s, &old_sum, line);
                                self.decide(rec, *s, &old_sum);
                            }
                        }
                    }
                }

                let target = self.walk.scopes.iter().rposition(|s| s.contains_key(name));
                if let Some(depth) = target {
                    signal!(rec.on(), trace::TRACE_STMT_ASSIGN_RESOLVED);
                    let old = self.walk.scopes[depth]
                        .get(name)
                        .cloned()
                        .expect("just checked");
                    self.rebind_death(rec, name, depth, stmt, &old, &bind.aliases)?;
                    self.check_row_ownership(name, depth, &bind, &moved_srcs)?;
                    let prov = self.prov_for_bind(Some(expr), &bind);
                    self.walk.scopes[depth].insert(name.clone(), bind);
                    self.walk.prov[depth].insert(name.to_string(), prov);
                    for (d, src) in &moved_srcs {
                        self.poison_moved(*d, src);
                    }
                    if rec.on() {
                        let entry = self
                            .own
                            .move_poisons
                            .entry(stmt as *const Stmt)
                            .or_default();
                        for (_, src) in &moved_srcs {
                            entry.insert(src.clone());
                        }
                    }
                    return Ok(());
                }
                return Err(ShapeError(format!(
                    "Scope Error: assignment to undeclared variable '{}'",
                    name
                )));
            }

            Stmt::IndexAssign { obj, key, value } => {
                let (t, obj_sites, _) = self.infer_expr(rec, obj)?;
                let (kty, _, _) = self.infer_expr(rec, key)?;
                // the key discipline: an unresolved key the walk can
                // see pins to Integer
                self.pin_int_use(rec, key, &kty);
                self.check_table_use(rec, obj)?;
                self.check_uses(rec, obj)?;
                self.check_uses(rec, key)?;

                let (vt, vsites, vlineage) = self.infer_expr(rec, value)?;
                self.check_uses(rec, value)?;

                if matches!(vt, Pending)
                    && vsites.iter().all(|s| is_root(s) || is_ghost(s))
                    && self.walk.scopes.len() == 1
                {
                    for &s in &obj_sites {
                        if !is_root(&s) && !is_ghost(&s) {
                            self.reads.boundary_fed.insert(s);
                        }
                    }
                }

                let value_ghosts: Vec<usize> = vsites.iter().copied().filter(is_ghost).collect();
                let mut stored_ghosts: Vec<usize> = Vec::new();
                if matches!(vt, Tbl(_)) {
                    if !value_ghosts.is_empty() {
                        signal!(rec.on(), trace::TRACE_ROW_HOUSING);
                        let targets: Vec<usize> = obj_sites
                            .iter()
                            .copied()
                            .filter_map(|s| self.proj_node(s))
                            .collect();
                        if targets.is_empty() {
                            signal!(rec.on(), trace::TRACE_FAIL_ROW_STORE);
                            return Err(ShapeError(
                                "Lifetime Error: a row read cannot be stored into an \
                                 unresolved or host-owned table — cells can only house \
                                 rows whose base the lattice can see"
                                    .to_string(),
                            ));
                        }
                        for &g in &value_ghosts {
                            let Some(&birth) = self.lattice.ghost_site.get(&g) else {
                                signal!(rec.on(), trace::TRACE_FAIL_ROW_STORE);
                                return Err(ShapeError(
                                    "Lifetime Error: a row read with a dynamic or unproven \
                                     key cannot be stored — its birth site is not visible \
                                     to the lattice; store a row read through a literal \
                                     key instead"
                                        .to_string(),
                                ));
                            };
                            for &s in &targets {
                                if s == birth || self.birth_closure(s).contains(&birth) {
                                    signal!(rec.on(), trace::TRACE_FAIL_ROW_STORE);
                                    return Err(ShapeError(
                                        "Lifetime Error: cyclic row store — the row read \
                                         would be stored into a table that already contains \
                                         it (alm's element types are finite)"
                                            .to_string(),
                                    ));
                                }
                            }
                            self.check_row_housing(g, value)?;
                            stored_ghosts.push(g);
                        }
                        if let Some(k) = const_key_value(key) {
                            for &s in &targets {
                                if let Some(&existing) =
                                    self.lattice.site_slots.get(&s).and_then(|m| m.get(&k))
                                    && is_ghost(&existing)
                                    && !value_ghosts.iter().any(|&vg| self.same_row(vg, existing))
                                {
                                    signal!(rec.on(), trace::TRACE_FAIL_ROW_STORE);
                                    return Err(ShapeError(
                                        "Lifetime Error: the destination cell already houses \
                                         a row — free it through its housing before storing \
                                         another (the displaced row would leak unnamed)"
                                            .to_string(),
                                    ));
                                }
                            }
                        }
                    } else if vsites.iter().all(is_root) && !vlineage.is_empty() {
                        signal!(rec.on(), trace::TRACE_FAIL_BORROW_ESCAPE);
                        return Err(ShapeError(
                            "Lifetime Error: a row read cannot be stored — borrows hold no \
                             ownership, and cells own exactly the headers they are given"
                                .to_string(),
                        ));
                    }
                }

                for &s in &obj_sites {
                    if !is_root(&s) && !is_ghost(&s) {
                        self.reads.user_store_sites.insert(s);
                    }
                }

                let mut base_obj = obj;
                let mut expected_ty = vt.clone();
                let mut nested = false;

                while let Expr::Index {
                    obj: parent_obj, ..
                } = base_obj
                {
                    signal!(rec.on(), trace::TRACE_STMT_IDX_NESTED);
                    expected_ty = Tbl(Box::new(expected_ty));
                    base_obj = parent_obj.as_ref();
                    nested = true;
                }

                let (_, base_sites, _) = self.infer_expr(rec, base_obj)?;

                if nested {
                    for &s in &base_sites {
                        if !is_root(&s) && !is_ghost(&s) {
                            self.reads.user_store_sites.insert(s);
                        }
                    }
                }

                if nested && let Some(name) = get_base_identifier(base_obj) {
                    for &s in &base_sites {
                        if !is_root(&s) && !is_ghost(&s) {
                            self.reads.nested_store_bases.insert(s, name.clone());
                        }
                    }
                }

                let mut value_sites: BTreeSet<usize> = BTreeSet::new();
                if matches!(vt, Tbl(_)) {
                    if rec.on() {
                        signal!(rec.on(), trace::TRACE_STMT_IDX_TBL_VALUE);
                    }
                    value_sites.extend(
                        vsites
                            .iter()
                            .copied()
                            .filter(|c| !is_root(c) && !is_ghost(c)),
                    );
                    for &g in &value_ghosts {
                        if let Some(b) = self.lattice.ghost_site.get(&g) {
                            value_sites.insert(*b);
                        }
                    }
                    if value_ghosts.is_empty() {
                        for (&origin, (_, d)) in &vlineage {
                            value_sites.extend(self.reachable_rows(origin, *d));
                        }
                    }
                    let targets: Vec<usize> = obj_sites
                        .iter()
                        .copied()
                        .filter_map(|s| self.proj_node(s))
                        .collect();
                    for &s in &targets {
                        self.reads.tbl_value_stores.insert(s);
                        for &c in &value_sites {
                            self.reads.row_links.entry(s).or_default().insert(c);
                        }
                    }
                }

                if matches!(vt, Tbl(_)) {
                    let proj_bases: Vec<usize> = base_sites
                        .iter()
                        .copied()
                        .filter_map(|x| self.proj_node(x))
                        .collect();
                    for s in proj_bases {
                        self.own.stored_ctor_parents.insert(s);
                        signal!(rec.on(), trace::TRACE_STMT_IDX_STORED_CTOR);
                    }
                }

                let mut cyclic_sites: BTreeSet<usize> = BTreeSet::new();
                let mut cyc_sources: BTreeSet<usize> = value_sites.clone();
                if matches!(value, Expr::TableCtor(_)) {
                    self.expr_named_sites(rec, value, &mut cyc_sources);
                }
                if matches!(vt, Tbl(_)) {
                    for (&origin, (_, d)) in &vlineage {
                        if *d >= 2 {
                            cyc_sources.extend(self.reachable_rows(origin, *d));
                        }
                    }
                }
                let lineage_feedback = |s: &usize| {
                    vlineage
                        .iter()
                        .any(|(&origin, (_, d))| origin == *s && (nested || *d >= 2))
                };
                if matches!(vt, Tbl(_)) && !matches!(value, Expr::TableCtor(_)) {
                    let value_name = match value {
                        Expr::Identifier(n) => n.clone(),
                        _ => "<row>".to_string(),
                    };
                    for &s in &base_sites {
                        if is_root(&s) {
                            continue;
                        }
                        let cyclic = lineage_feedback(&s)
                            || cyc_sources
                                .iter()
                                .any(|&v| holds_reaches(&self.holds, v, s));
                        if cyclic {
                            let base_name = get_base_identifier(base_obj)
                                .cloned()
                                .unwrap_or_else(|| "<row>".to_string());
                            cyclic_sites.insert(s);
                            self.holds.cyclic_stores.entry(base_name).or_insert((
                                value_name.clone(),
                                self.stmt_lines[&(stmt as *const Stmt)],
                            ));
                        } else {
                            for &v in &value_sites {
                                self.holds.hold_edges.entry(s).or_default().insert(v);
                            }
                        }
                    }
                } else if matches!(vt, Tbl(_)) && cyc_sources.iter().any(|v| base_sites.contains(v))
                {
                    let base_name = get_base_identifier(base_obj)
                        .cloned()
                        .unwrap_or_else(|| "<row>".to_string());
                    for &s in &base_sites {
                        if !is_root(&s) {
                            cyclic_sites.insert(s);
                            self.holds
                                .cyclic_stores
                                .entry(base_name.clone())
                                .or_insert((
                                    "<constructor>".to_string(),
                                    self.stmt_lines[&(stmt as *const Stmt)],
                                ));
                        }
                    }
                }

                let mut moved_srcs: Vec<(usize, String)> = Vec::new();
                if let Expr::Identifier(src) = value {
                    self.record_moved_param(src);
                    let (d, bind) = self.resolve(rec, src)?;
                    self.check_boundary_pin(&bind, src)?;
                    if matches!(vt, Tbl(_)) {
                        moved_srcs.push((d, src.clone()));
                    }
                } else if let Expr::TableCtor(_) = value {
                    self.collect_entry_moves(rec, value, &mut moved_srcs)?;
                }
                for (d, src) in &moved_srcs {
                    self.poison_moved(*d, src);
                }
                if rec.on() {
                    let entry = self
                        .own
                        .move_poisons
                        .entry(stmt as *const Stmt)
                        .or_default();
                    for (_, src) in &moved_srcs {
                        entry.insert(src.clone());
                    }
                }

                if matches!(t, Tbl(_) | Pending) {
                    signal!(rec.on(), trace::TRACE_STMT_IDX_BASE_TBL);
                    let proj_bases: Vec<usize> = base_sites
                        .iter()
                        .copied()
                        .filter_map(|x| self.proj_node(x))
                        .collect();
                    let line = self.stmt_lines.get(&(stmt as *const Stmt)).copied();
                    if matches!(expected_ty, Conflict) {
                        crate::alm_dbgln!(
                            "[idxassign] line {line:?}: storing Conflict into sites {proj_bases:?} (vt={:?})",
                            vt
                        );
                    }
                    for s in proj_bases
                        .iter()
                        .copied()
                        .filter(|x| !cyclic_sites.contains(x))
                    {
                        signal!(rec.on(), trace::TRACE_STMT_IDX_VALID_ALIAS);
                        self.note_adopt_if_flipping(rec, s, &expected_ty, line);
                        self.decide(rec, s, &expected_ty);
                    }
                }

                if rec.on() {
                    signal!(rec.on(), trace::TRACE_STMT_IDX_CHECK_THRESH);
                    let real_base_sites: BTreeSet<usize> = base_sites
                        .iter()
                        .copied()
                        .filter_map(|s| self.proj_node(s))
                        .collect();
                    self.check_key_threshold(rec, key, &real_base_sites)?;
                }

                if !stored_ghosts.is_empty() {
                    let slot = const_key_value(key);
                    for &g in &stored_ghosts {
                        let birth = self.lattice.ghost_site[&g];
                        let tgt_sites: Vec<usize> = obj_sites
                            .iter()
                            .copied()
                            .filter_map(|x| self.proj_node(x))
                            .collect();
                        for tgt in tgt_sites {
                            self.reads.row_links.entry(tgt).or_default().insert(birth);
                            self.own.stored_ctor_parents.insert(tgt);
                            if let Some(k) = slot {
                                self.lattice.site_slots.entry(tgt).or_default().insert(k, g);
                            }
                        }
                        self.lattice.housed_ghosts.insert(g);
                        if rec.on() {
                            self.own
                                .store_ghost_keeps
                                .entry(stmt as *const Stmt)
                                .or_default()
                                .push(g);
                            signal!(rec.on(), trace::TRACE_ROW_HOUSED);
                        }
                    }
                }
            }

            Stmt::While { condition, body } => {
                let (cty, _, _) = self.infer_expr(rec, condition)?;
                // the condition discipline: an unresolved operand the
                // walk can see pins to Boolean here, before the body
                self.pin_bool_use(rec, condition, &cty);
                self.check_uses(rec, condition)?;

                if rec.on()
                    && let Some(guard) = extract_guard(condition)
                {
                    signal!(rec.on(), trace::TRACE_STMT_WHILE_FILL);
                    self.detect_fill_loop(rec, guard, body);
                }

                let entry = self.walk.scopes.clone();
                let mut head = entry.clone();
                let scope_key = (stmt as *const Stmt, 0);
                // the loop BODY scope index plan_break_exits unwinds down to:
                // with_scope pushes body scopes onto walk.scopes, so entries
                // must be taken BEFORE the first with_scope of the fixpoint.
                self.loop_scope_entries.push(self.walk.scopes.len());
                loop {
                    self.walk.scopes = head.clone();
                    self.check_uses(rec, condition)?;
                    self.with_scope(|an| {
                        an.walk_stmts(rec, body);
                        an.decide_scope_exit(rec, scope_key)
                    })?;
                    let latch = self.walk.scopes.clone();
                    let mut merged = entry.clone();
                    merge_table_scopes(&mut merged, &head, &latch);
                    if merged == head {
                        signal!(rec.on(), trace::TRACE_STMT_WHILE_STABLE);
                        break;
                    }
                    head = merged;
                }
                self.loop_scope_entries.pop();
                self.walk.scopes = head;
                for depth in 0..self.walk.scopes.len() {
                    let names: Vec<String> = self.walk.scopes[depth].keys().cloned().collect();
                    for name in names {
                        let changed = entry
                            .get(depth)
                            .and_then(|s| s.get(&name))
                            .is_some_and(|e| e.aliases != self.walk.scopes[depth][&name].aliases);
                        if changed {
                            self.walk.prov[depth].insert(name, None);
                        }
                    }
                }
            }

            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                signal!(rec.on(), trace::TRACE_STMT_IF);
                let (cty, _, _) = self.infer_expr(rec, condition)?;
                self.pin_bool_use(rec, condition, &cty);
                self.check_uses(rec, condition)?;
                let snapshot = self.walk.scopes.clone();
                let prov_snapshot = self.walk.prov.clone();
                self.with_scope(|an| {
                    an.walk_stmts(rec, then_body);
                    an.decide_scope_exit(rec, (stmt as *const Stmt, 0))
                })?;
                let then_exit = self.walk.scopes.clone();
                self.walk.scopes = snapshot;
                self.walk.prov = prov_snapshot.clone();
                self.with_scope(|an| {
                    an.walk_stmts(rec, else_body);
                    an.decide_scope_exit(rec, (stmt as *const Stmt, 1))
                })?;
                let else_exit = self.walk.scopes.clone();
                merge_table_scopes(&mut self.walk.scopes, &then_exit, &else_exit);
                for depth in 0..self.walk.scopes.len() {
                    let names: Vec<String> = self.walk.scopes[depth].keys().cloned().collect();
                    for name in names {
                        let (Some(tt), Some(et)) = (
                            then_exit.get(depth).and_then(|s| s.get(&name)),
                            else_exit.get(depth).and_then(|s| s.get(&name)),
                        ) else {
                            continue;
                        };
                        if tt.aliases == et.aliases {
                            continue;
                        }
                        let joined = &self.walk.scopes[depth][&name];
                        let mixed = joined.aliases.iter().any(is_ghost)
                            && joined.aliases.iter().any(|x| !is_root(x) && !is_ghost(x));
                        let cur = self.walk.prov[depth].get(&name).copied().flatten();
                        let new_prov = if mixed && cur.is_none() {
                            self.join_arm_shapes.insert(
                                (stmt as *const Stmt, name.clone()),
                                (tt.clone(), et.clone()),
                            );
                            Some(Prov::If(stmt as *const Stmt))
                        } else {
                            None
                        };
                        self.walk.prov[depth].insert(name, new_prov);
                    }
                }
            }

            Stmt::Do { body } => {
                signal!(rec.on(), trace::TRACE_STMT_DO);
                self.with_scope(|an| {
                    an.walk_stmts(rec, body);
                    an.decide_scope_exit(rec, (stmt as *const Stmt, 0))
                })?
            }

            Stmt::Print { exprs } => {
                signal!(rec.on(), trace::TRACE_STMT_PRINT);
                for e in exprs {
                    self.infer_expr(rec, e)?;
                    self.check_uses(rec, e)?;
                }
            }

            Stmt::Expr { expr } => {
                self.infer_expr(rec, expr)?;
                self.check_uses(rec, expr)?;
            }

            Stmt::Break => {
                if rec.on() {
                    self.plan_break_exits(stmt as *const Stmt);
                }
            }

            Stmt::Return { value } => {
                if let Some(v) = value {
                    let (ty, mut aliases, lineage) = self.infer_expr(rec, v)?;
                    self.check_uses(rec, v)?;
                    let frame = self.fn_walk.last().map(|(fp, ps)| (*fp, ps.clone()));
                    if let Some((fn_ptr, params)) = frame {
                        let reaches = self.return_reaches_param(v, &params);
                        if !reaches.is_empty() {
                            self.fn_ret_params
                                .entry(fn_ptr)
                                .or_default()
                                .extend(reaches);
                        }
                    }
                    let mut reach: BTreeSet<usize> = BTreeSet::new();
                    if matches!(ty, Tbl(_) | Pending) {
                        self.ret_reach_sites(v, &mut reach);
                    }
                    if let Some(slot) = self.fn_ret_reaches.last_mut() {
                        slot.extend(reach.iter().copied());
                    }
                    if rec.on() {
                        self.plan_return_exits(Some((v, &ty)), &reach, stmt as *const Stmt);
                    }
                    if let Some(slot) = self.fn_rets.last_mut() {
                        if let Some(&entry) = self.fn_scope_entries.last() {
                            let outer_owned: BTreeSet<usize> = self.walk.scopes[..entry]
                                .iter()
                                .flat_map(|scope| scope.values())
                                .flat_map(|ts| ts.aliases.iter().copied())
                                .filter(|s| !is_root(s))
                                .collect();
                            aliases.retain(|s| is_root(s) || !outer_owned.contains(s));
                        }
                        let shape = TableShape {
                            ty,
                            layout: LayoutVerdict::default(),
                            aliases,
                            lineage,
                        };
                        match slot {
                            None => *slot = Some(shape.clone()),
                            Some(joined) => {
                                joined.join(&shape);
                            }
                        }
                        if let Some(frame) = self.fn_edge_frames.last_mut() {
                            frame.push(shape);
                        }
                    }
                } else if rec.on() {
                    let no_reach = BTreeSet::new();
                    self.plan_return_exits(None, &no_reach, stmt as *const Stmt);
                }
            }
        }
        Ok(())
    }

    pub(super) fn enter_scope(&mut self) {
        self.walk.scopes.push(BTreeMap::new());
        self.walk.fn_scopes.push(BTreeMap::new());
        self.walk.prov.push(BTreeMap::new());
        self.walk.scalar_nodes.push(BTreeMap::new());
    }

    pub(super) fn exit_scope(&mut self) {
        if let Some(dying) = self.walk.scopes.last() {
            for name in dying.keys() {
                self.holds.num_assigns.remove(name);
                self.holds.nil_severed.remove(name);
                self.holds.moved_severed.remove(name);
            }
        }
        self.walk.fn_scopes.pop();
        self.walk.prov.pop();
        self.walk.scalar_nodes.pop();
        self.walk.scopes.pop();
    }

    pub(super) fn with_scope<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.enter_scope();
        let r = f(self);
        self.exit_scope();
        r
    }

    pub(super) fn resolve(&self, rec: Gate, name: &str) -> Result<(usize, TableShape), ShapeError> {
        for (depth, scope) in self.walk.scopes.iter().enumerate().rev() {
            if let Some(bind) = scope.get(name) {
                signal!(rec.on(), trace::TRACE_RESOLVE_FOUND);
                return Ok((depth, bind.clone()));
            }
        }
        Err(ShapeError(format!(
            "Scope Error: reference to undeclared variable '{}'",
            name
        )))
    }

    pub(super) fn resolve_aliases(
        &self,
        rec: Gate,
        name: &str,
    ) -> Result<BTreeSet<usize>, ShapeError> {
        Ok(self.resolve(rec, name)?.1.aliases)
    }

    pub(super) fn prov_for_bind(&self, expr: Option<&Expr>, shape: &TableShape) -> Option<Prov> {
        let has_ghost = shape.aliases.iter().any(is_ghost);
        let has_site = shape.aliases.iter().any(|x| !is_root(x) && !is_ghost(x));
        if !(has_ghost && has_site) {
            return None;
        }
        match expr {
            Some(e @ Expr::Call { .. }) => Some(Prov::Call(e as *const Expr)),
            Some(Expr::Identifier(src)) => self
                .resolve(None, src)
                .ok()
                .and_then(|(d, _)| self.walk.prov.get(d)?.get(src).copied().flatten()),
            _ => None,
        }
    }

    pub(super) fn expr_named_sites(&self, rec: Gate, expr: &Expr, out: &mut BTreeSet<usize>) {
        match expr {
            Expr::Identifier(n) => {
                if let Ok((_, b)) = self.resolve(rec, n) {
                    out.extend(b.aliases.iter().copied().filter(|&s| !is_root(&s)));
                }
            }
            Expr::TableCtor(entries) => {
                for (_, e) in entries {
                    self.expr_named_sites(rec, e, out);
                }
            }
            _ => {}
        }
    }
}
