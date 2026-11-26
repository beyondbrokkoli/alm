use super::*;
impl Analyzer {
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
        _rec: Gate,
        site: usize,
        vt: &Ty,
        line: Option<usize>,
    ) {
        let cur = self.lattice.site_elem[site].clone();
        if !matches!(cur, Any)
            && matches!(join_ty(&cur, vt), Any)
            && let Some(l) = line
        {
            self.note_adopt(site, l);
        }
    }

    pub(super) fn walk_stmts(&mut self, rec: Gate, stmts: &[Stmt]) {
        for s in stmts {
            if let Err(err) = self.walk_stmt(rec, s) {
                self.ledger
                    .diagnostics
                    .push(err.0.with_site(Some(s.loc().line as usize)));
                return;
            }
        }
    }

    pub(super) fn walk_stmt(&mut self, rec: Gate, stmt: &Stmt) -> Result<(), ShapeError> {
        omni::note_stmt(stmt.loc().line as usize);
        self.sever_creation_captures(rec, stmt);
        self.walk_stmt_inner(rec, stmt)
    }

    fn walk_stmt_inner(&mut self, rec: Gate, stmt: &Stmt) -> Result<(), ShapeError> {
        match stmt {
            Stmt::LocalDecl { names, exprs, .. } => {
                let mut sets = Vec::with_capacity(names.len());
                let mut moved_srcs: Vec<(usize, String)> = Vec::new();
                // The pre-statement faces this decl replaces, captured
                // before the pre-binds overwrite the innermost entries:
                // rebind_death must see the binding this statement
                // replaces, not its own placeholder. A repeated target's
                // later slot reads its twin's set instead — `written`
                // below mirrors today's live innermost reads.
                let olds: Vec<Option<TableShape>> = names
                    .iter()
                    .map(|name| {
                        self.walk
                            .scopes
                            .last()
                            .and_then(|s| s.get(name))
                            .map(|b| b.shape.clone())
                    })
                    .collect();
                for (name, expr) in names.iter().zip(exprs.iter()) {
                    // D1: every face is born with its binding — one
                    // pre-bind per target before any initializer walks.
                    // C: only a whole-value function literal is a fn
                    // binding; every other RHS binds a plain name. The
                    // placeholder's shape face carries DECL_PENDING, so
                    // shape reads skip it and resolve outward exactly as
                    // when the binding did not exist
                    // (escape_self_capture), while the fn face rides the
                    // binding and a self-call reaches the recursion law
                    // as before.
                    let ptr = if let Expr::Function { .. } = expr {
                        Some(expr.id())
                    } else {
                        None
                    };
                    self.walk
                        .scopes
                        .last_mut()
                        .unwrap()
                        .insert(name.clone(), Binding::with_fn(decl_pending_shape(), ptr));
                    omni::fn_face_write(
                        name,
                        self.walk.scopes.len() - 1,
                        self.walk.scopes.len() - 1,
                        ptr,
                        "decl-pre-bind",
                    );
                }
                for name in &names[exprs.len()..] {
                    self.walk
                        .scopes
                        .last_mut()
                        .unwrap()
                        .insert(name.clone(), Binding::with_fn(decl_pending_shape(), None));
                }
                let note_move = |an: &mut Self,
                                 src: &str,
                                 target: &str,
                                 moved: &mut Vec<(usize, String)>|
                 -> Result<(), ShapeError> {
                    if src == target {
                        return Ok(());
                    }
                    let (d, bind) = an.resolve(src)?;
                    an.record_moved_param(src);
                    an.check_boundary_pin(&bind, src)?;
                    if matches!(bind.ty, Tbl(_)) {
                        if moved.iter().any(|(_, m)| m == src) {
                            return Err(ShapeError(Diagnostic::lifetime(format!(
                                "'{src}' is moved more than once — one table \
                                 value has exactly one receiving binding"
                            ))));
                        }
                        moved.push((d, src.to_string()));
                    }
                    Ok(())
                };
                for (name, expr) in names.iter().zip(exprs.iter()) {
                    if let Expr::Identifier { name: src, .. } = expr {
                        note_move(self, src, name, &mut moved_srcs)?;
                    }
                }
                for (idx, expr) in exprs.iter().enumerate() {
                    self.note_decl_scalar_node(&names[idx], expr);
                    if matches!(expr, Expr::Nil { .. }) {
                        sets.push(TableShape {
                            ty: Pending,
                            layout: LayoutVerdict::default(),
                            aliases: BTreeSet::from([NULL_ROOT]),
                            lineage: BTreeMap::new(),
                        });
                    } else if let Expr::Function { params, body, .. } = expr {
                        self.walk_fn_def(rec, expr.id(), params, body, (stmt.id(), 2 + idx as u8))?;
                        sets.push(TableShape {
                            ty: Pending,
                            layout: LayoutVerdict::default(),
                            aliases: BTreeSet::new(),
                            lineage: BTreeMap::new(),
                        });
                    } else {
                        let bind = self.infer_bind(rec, expr)?;
                        if self.rhs_pin_derived(expr) {
                            self.pin_justified_names.insert(names[idx].clone());
                        }
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
                        sets.push(bind);
                    }
                }
                while sets.len() < names.len() {
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
                let mut written: BTreeMap<String, TableShape> = BTreeMap::new();
                for (idx, (name, set)) in names.iter().zip(sets).enumerate() {
                    let old = written
                        .get(name.as_str())
                        .cloned()
                        .or_else(|| olds[idx].clone());
                    if let Some(old) = old {
                        self.rebind_death(rec, name, depth, stmt, &old, &set.aliases)?;
                    }
                    self.holds.nil_severed.remove(name);
                    self.holds.moved_severed.remove(name);
                    self.check_row_ownership(name, depth, &set, &moved_srcs)?;
                    let prov = self.prov_for_bind(exprs.get(idx), &set);
                    let twin = set.clone();
                    let slot = self
                        .walk
                        .scopes
                        .last_mut()
                        .unwrap()
                        .get_mut(name)
                        .expect("the pre-bind guarantees the target's slot");
                    slot.shape = set;
                    slot.prov = prov; // fn_ptr / scalar_node preserved —
                    // a decl does not un-declare what
                    // it pre-bound
                    written.insert(name.clone(), twin);
                }
                for (d, src) in &moved_srcs {
                    self.poison_moved(*d, src);
                }
                if rec.on() {
                    let entry = self.own.move_poisons.entry(stmt.id()).or_default();
                    for (_, src) in &moved_srcs {
                        entry.insert(src.clone());
                    }
                }
            }

            Stmt::Assignment { name, expr, .. } => {
                let entry = self.holds.num_assigns.entry(name.clone()).or_default();
                let shape = num_of(expr);
                if !entry.contains(&shape) {
                    entry.push(shape);
                }
                // D1's twin window: the fn face is born before the body
                // walk. A resolved target keeps its shape face — reads
                // during the body walk see the old shape, exactly as
                // when only the rider moved. A name bound nowhere
                // pre-binds a DECL_PENDING placeholder so the fn face
                // has a home; `pre_bound` routes the tail to the
                // graduating write, the way today's undeclared-fn insert
                // stood in for the rider.
                let mut pre_bound = false;
                if let Expr::Function { params, body, .. } = expr {
                    match self.walk.binding_at_mut(name) {
                        Some((home, target)) => {
                            target.fn_ptr = Some(expr.id());
                            omni::fn_face_write(
                                name,
                                home,
                                self.walk.scopes.len() - 1,
                                Some(expr.id()),
                                "assignment",
                            );
                        }
                        None => {
                            pre_bound = true;
                            let depth = self.walk.scopes.len() - 1;
                            self.walk.scopes[depth].insert(
                                name.clone(),
                                Binding::with_fn(decl_pending_shape(), Some(expr.id())),
                            );
                            omni::fn_face_write(
                                name,
                                depth,
                                depth,
                                Some(expr.id()),
                                "pre-bind-placeholder",
                            );
                        }
                    }
                    self.walk_fn_def(rec, expr.id(), params, body, (stmt.id(), 2))?;
                } else {
                    // a non-fn RHS clears the fn face at the binding's
                    // home depth
                    if let Some((home, target)) = self.walk.binding_at_mut(name) {
                        target.fn_ptr = None;
                        omni::fn_face_write(
                            name,
                            home,
                            self.walk.scopes.len() - 1,
                            None,
                            "assignment-clear",
                        );
                    }
                }
                if matches!(expr, Expr::Nil { .. }) {
                    self.note_assign_scalar_node(name, expr);
                    self.drop_reference(rec, name, stmt)?;
                    return Ok(());
                }
                let bind = self.infer_bind(rec, expr)?;
                if self.rhs_pin_derived(expr) {
                    self.pin_justified_names.insert(name.clone());
                }
                self.note_assign_scalar_node(name, expr);
                self.check_uses(rec, expr)?;
                let mut moved_srcs: Vec<(usize, String)> = Vec::new();
                if let Expr::Identifier { name: src, .. } = expr {
                    if src != name {
                        self.record_moved_param(src);
                        self.check_boundary_pin(&bind, src)?;
                        if matches!(bind.ty, Tbl(_)) {
                            let (d, _) = self.resolve(src)?;
                            moved_srcs.push((d, src.clone()));
                        }
                    }
                } else {
                    self.collect_entry_moves(rec, expr, &mut moved_srcs)?;
                }

                if matches!(bind.ty, Tbl(_)) {
                    let mut incoming = Pending;
                    for s in &bind.aliases {
                        if !is_root(s) && !is_ghost(s) {
                            incoming = join_ty(&incoming, &self.lattice.site_elem[*s]);
                        }
                    }
                    let line = Some(stmt.loc().line as usize);
                    let mut old: BTreeSet<usize> = self
                        .resolve_aliases(name)?
                        .into_iter()
                        .filter(|s| !is_root(s) && !is_ghost(s))
                        .collect();
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
                    let nested = |t: &Ty| matches!(t, Tbl(_) if decided(t));
                    let joins_clean = |cur: &Ty, vt: &Ty| !matches!(join_ty(cur, vt), Conflict);
                    if value_kind(&incoming) {
                        for s in old {
                            self.note_adopt_if_flipping(rec, s, &incoming, line);
                            self.decide(rec, s, &incoming);
                        }
                    } else if nested(&incoming) {
                        for s in old {
                            if joins_clean(&self.lattice.site_elem[s], &incoming) {
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

                if pre_bound {
                    // The pre-bind is the declaration: its placeholder
                    // face graduates to the declared Pending face —
                    // today's undeclared-fn insert, fused with the fn
                    // face the pre-bind already wrote.
                    let depth = self.walk.scopes.len() - 1;
                    let slot = self.walk.scopes[depth]
                        .get_mut(name)
                        .expect("the pre-bind guarantees the slot");
                    slot.shape = TableShape {
                        ty: Pending,
                        layout: LayoutVerdict::default(),
                        aliases: BTreeSet::new(),
                        lineage: BTreeMap::new(),
                    };
                    slot.prov = None;
                    return Ok(());
                }
                let target = self.walk.scopes.iter().rposition(|s| s.contains_key(name));
                if let Some(depth) = target {
                    let old = self.walk.scopes[depth]
                        .get(name)
                        .expect("just checked")
                        .shape
                        .clone();
                    self.rebind_death(rec, name, depth, stmt, &old, &bind.aliases)?;
                    self.check_row_ownership(name, depth, &bind, &moved_srcs)?;
                    let prov = self.prov_for_bind(Some(expr), &bind);
                    let slot = self.walk.scopes[depth].get_mut(name).expect("just checked");
                    slot.shape = bind;
                    slot.prov = prov; // fn_ptr / scalar_node preserved —
                    // the faces this statement wrote
                    // above stand
                    for (d, src) in &moved_srcs {
                        self.poison_moved(*d, src);
                    }
                    if rec.on() {
                        let entry = self.own.move_poisons.entry(stmt.id()).or_default();
                        for (_, src) in &moved_srcs {
                            entry.insert(src.clone());
                        }
                    }
                    return Ok(());
                }
                return Err(ShapeError(Diagnostic::scope(format!(
                    "assignment to undeclared variable '{}'",
                    name
                ))));
            }

            Stmt::IndexAssign {
                id,
                obj,
                key,
                value,
                ..
            } => {
                let (t, obj_sites, _) = self.infer_expr(rec, obj)?;
                let (kty, _, _) = self.infer_expr(rec, key)?;
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
                        let targets: Vec<usize> = obj_sites
                            .iter()
                            .copied()
                            .filter_map(|s| self.proj_node(s))
                            .collect();
                        if targets.is_empty() {
                            return Err(ShapeError(Diagnostic::lifetime(
                                "a row read cannot be stored into an \
                                 unresolved or host-owned table — cells can only house \
                                 rows whose base the lattice can see",
                            )));
                        }
                        for &g in &value_ghosts {
                            let Some(&birth) = self.lattice.ghost_site.get(&g) else {
                                return Err(ShapeError(Diagnostic::lifetime(
                                    "a row read with a dynamic or unproven \
                                     key cannot be stored — its birth site is not visible \
                                     to the lattice; store a row read through a literal \
                                     key instead",
                                )));
                            };
                            for &s in &targets {
                                if s == birth || self.birth_closure(s).contains(&birth) {
                                    return Err(ShapeError(Diagnostic::lifetime(
                                        "cyclic row store — the row read \
                                         would be stored into a table that already contains \
                                         it (alm's element types are finite)",
                                    )));
                                }
                            }
                            self.check_row_housing(g, value)?;
                            stored_ghosts.push(g);
                        }
                        if let Some(k) = const_key_value(key, self.surface.index_base()) {
                            for &s in &targets {
                                if let Some(&existing) =
                                    self.lattice.site_slots.get(&s).and_then(|m| m.get(&k))
                                    && is_ghost(&existing)
                                    && !value_ghosts.iter().any(|&vg| self.same_row(vg, existing))
                                {
                                    return Err(ShapeError(Diagnostic::lifetime(
                                        "the destination cell already houses \
                                         a row — free it through its housing before storing \
                                         another (the displaced row would leak unnamed)",
                                    )));
                                }
                            }
                        }
                    } else if vsites.iter().all(is_root) && !vlineage.is_empty() {
                        return Err(ShapeError(Diagnostic::lifetime(
                            "a row read cannot be stored — borrows hold no \
                             ownership, and cells own exactly the headers they are given",
                        )));
                    }
                }

                for &s in &obj_sites {
                    if !is_root(&s) && !is_ghost(&s) {
                        self.reads.user_store_sites.insert(s);
                    }
                }
                // The lane-side row-kind fact: same predicate as the
                // lowerer's contains_tables, minted per store statement
                // so a row store through a non-ctor spelling still
                // marks its base for the fast lane's fresh-slot laws.
                if matches!(vt, Tbl(_)) {
                    self.own.row_value_stores.insert(*id);
                }

                let mut base_obj = obj;
                let mut expected_ty = vt.clone();
                let mut nested = false;

                while let Expr::Index {
                    obj: parent_obj, ..
                } = base_obj
                {
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
                    }
                }

                let mut cyclic_sites: BTreeSet<usize> = BTreeSet::new();
                let mut cyc_sources: BTreeSet<usize> = value_sites.clone();
                if matches!(value, Expr::TableCtor { .. }) {
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
                if matches!(vt, Tbl(_)) && !matches!(value, Expr::TableCtor { .. }) {
                    let value_name = match value {
                        Expr::Identifier { name: n, .. } => n.clone(),
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
                            self.holds
                                .cyclic_stores
                                .entry(base_name)
                                .or_insert((value_name.clone(), stmt.loc().line as usize));
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
                                .or_insert(("<constructor>".to_string(), stmt.loc().line as usize));
                        }
                    }
                }

                let mut moved_srcs: Vec<(usize, String)> = Vec::new();
                if let Expr::Identifier { name: src, .. } = value {
                    self.record_moved_param(src);
                    let (d, bind) = self.resolve(src)?;
                    self.check_boundary_pin(&bind, src)?;
                    if matches!(vt, Tbl(_)) {
                        moved_srcs.push((d, src.clone()));
                    }
                } else if let Expr::TableCtor { .. } = value {
                    self.collect_entry_moves(rec, value, &mut moved_srcs)?;
                }
                for (d, src) in &moved_srcs {
                    self.poison_moved(*d, src);
                }
                if rec.on() {
                    let entry = self.own.move_poisons.entry(stmt.id()).or_default();
                    for (_, src) in &moved_srcs {
                        entry.insert(src.clone());
                    }
                }

                if matches!(t, Tbl(_) | Pending) {
                    let proj_bases: Vec<usize> = base_sites
                        .iter()
                        .copied()
                        .filter_map(|x| self.proj_node(x))
                        .collect();
                    let line = Some(stmt.loc().line as usize);
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
                        self.note_adopt_if_flipping(rec, s, &expected_ty, line);
                        self.decide(rec, s, &expected_ty);
                    }
                }

                if rec.on() {
                    let real_base_sites: BTreeSet<usize> = base_sites
                        .iter()
                        .copied()
                        .filter_map(|s| self.proj_node(s))
                        .collect();
                    self.check_key_threshold(
                        rec,
                        const_key_value(key, self.surface.index_base()),
                        &real_base_sites,
                    )?;
                }

                if !stored_ghosts.is_empty() {
                    // [index-base] Physical like every site_slots writer:
                    // the ctor writers arrive mint-shifted, so this
                    // store-side writer translates through the same
                    // base-aware reader or its slots would silently
                    // never match.
                    let slot = const_key_value(key, self.surface.index_base());
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
                                .entry(stmt.id())
                                .or_default()
                                .push(g);
                        }
                    }
                }
            }

            Stmt::While {
                condition, body, ..
            } => {
                let (cty, _, _) = self.infer_expr(rec, condition)?;
                self.pin_bool_use(rec, condition, &cty);
                self.check_uses(rec, condition)?;

                // [fast-lane] The walk-time half of the lane: recognize
                // the conversion loop and mint its reserve plan (the
                // recorded pass only — the fixpoint's unrecorded trips
                // mint nothing).
                if rec.on()
                    && let Some((guard, bound)) = extract_guard(condition)
                {
                    self.detect_fill_loop(rec, stmt.id(), guard, bound, body);
                }

                let entry = self.walk.scopes.clone();
                let mut head = entry.clone();
                let scope_key = (stmt.id(), 0);
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
                        break;
                    }
                    head = merged;
                }
                self.loop_scope_entries.pop();
                self.walk.scopes = head;
                // The face flip (the judge's law, 2026-11-14): a body's
                // fn and scalar-node writes die with the fixpoint — the
                // head's faces stand past the latch, so a body (live or
                // never-taken) cannot re-point a name's inline
                // expansion. (Prov is the exception: it is latched
                // explicitly below, exactly as before.)
                // The latch's prov tagging: a name whose aliases moved
                // across the loop loses its provenance. The face write
                // lands on the binding (today: a prov rider insert).
                for depth in 0..self.walk.scopes.len() {
                    let names: Vec<String> = self.walk.scopes[depth].keys().cloned().collect();
                    for name in names {
                        let changed =
                            entry
                                .get(depth)
                                .and_then(|s| s.get(&name))
                                .is_some_and(|e| {
                                    e.shape.aliases != self.walk.scopes[depth][&name].shape.aliases
                                });
                        if changed && let Some(bind) = self.walk.scopes[depth].get_mut(&name) {
                            bind.prov = None;
                        }
                    }
                }
            }

            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                let (cty, _, _) = self.infer_expr(rec, condition)?;
                self.pin_bool_use(rec, condition, &cty);
                self.check_uses(rec, condition)?;
                let snapshot = self.walk.scopes.clone();
                self.with_scope(|an| {
                    an.walk_stmts(rec, then_body);
                    an.decide_scope_exit(rec, (stmt.id(), 0))
                })?;
                let then_exit = self.walk.scopes.clone();
                self.walk.scopes = snapshot;
                // The face flip (the judge's law, 2026-11-14): the arms
                // run on the entry snapshot's faces — a branch's fn and
                // scalar-node writes die with its arm (dead or taken),
                // so no arm re-points a name's inline expansion for the
                // other arm's reads or for the join. Prov is the
                // exception: it was snapshotted and restored, and the
                // bindings carry it back exactly.
                self.with_scope(|an| {
                    an.walk_stmts(rec, else_body);
                    an.decide_scope_exit(rec, (stmt.id(), 1))
                })?;
                let else_exit = self.walk.scopes.clone();
                merge_table_scopes(&mut self.walk.scopes, &then_exit, &else_exit);
                // The If join's prov tagging: a name whose aliases split
                // across the arms takes If provenance when the merged
                // aliases mix ghosts with real sites and no provenance
                // stands. The writes land on the bindings — prov rides
                // the snapshot/restore with its scope, so no separate
                // prov snapshot exists anymore.
                for depth in 0..self.walk.scopes.len() {
                    let names: Vec<String> = self.walk.scopes[depth].keys().cloned().collect();
                    for name in names {
                        let (Some(tt), Some(et)) = (
                            then_exit.get(depth).and_then(|s| s.get(&name)),
                            else_exit.get(depth).and_then(|s| s.get(&name)),
                        ) else {
                            continue;
                        };
                        if tt.shape.aliases == et.shape.aliases {
                            continue;
                        }
                        let joined = &self.walk.scopes[depth][&name];
                        let mixed = joined.shape.aliases.iter().any(is_ghost)
                            && joined
                                .shape
                                .aliases
                                .iter()
                                .any(|x| !is_root(x) && !is_ghost(x));
                        let cur = self.walk.scopes[depth].get(&name).and_then(|b| b.prov);
                        let new_prov = if mixed && cur.is_none() {
                            self.join_arm_shapes.insert(
                                (stmt.id(), name.clone()),
                                (tt.shape.clone(), et.shape.clone()),
                            );
                            Some(Prov::If(stmt.id()))
                        } else {
                            None
                        };
                        if let Some(bind) = self.walk.scopes[depth].get_mut(&name) {
                            bind.prov = new_prov;
                        }
                    }
                }
            }

            Stmt::Do { body, .. } => self.with_scope(|an| {
                an.walk_stmts(rec, body);
                an.decide_scope_exit(rec, (stmt.id(), 0))
            })?,

            Stmt::Print { exprs, .. } => {
                for e in exprs {
                    self.infer_expr(rec, e)?;
                    self.check_uses(rec, e)?;
                }
            }

            Stmt::Expr { expr, .. } => {
                self.infer_expr(rec, expr)?;
                self.check_uses(rec, expr)?;
            }

            Stmt::Break { .. } => {
                if let Some(&fn_entry) = self.fn_scope_entries.last()
                    && !self
                        .loop_scope_entries
                        .last()
                        .is_some_and(|&loop_entry| loop_entry > fn_entry)
                {
                    return Err(ShapeError(Diagnostic::ty(
                        "'break' cannot leave an expansion — \
                         write the break inside a loop of the same body",
                    )));
                }
                if rec.on() {
                    self.plan_break_exits(stmt.id());
                }
            }

            Stmt::Return { value, .. } => {
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
                        self.plan_return_exits(Some((v, &ty)), &reach, stmt.id());
                    }
                    if let Some(slot) = self.fn_rets.last_mut() {
                        if let Some(&entry) = self.fn_scope_entries.last() {
                            let outer_owned: BTreeSet<usize> = self.walk.scopes[..entry]
                                .iter()
                                .flat_map(|scope| scope.values())
                                .flat_map(|b| b.shape.aliases.iter().copied())
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
                    self.plan_return_exits(None, &no_reach, stmt.id());
                }
            }
        }
        Ok(())
    }

    pub(super) fn enter_scope(&mut self) {
        omni::scope_push(
            self.walk.scopes.len(),
            &omni::root_faces_of(&self.walk.scopes),
        );
        self.walk.scopes.push(Scope::new());
    }

    pub(super) fn exit_scope(&mut self) {
        if let Some(dying) = self.walk.scopes.last() {
            for name in dying.keys() {
                // The holds family is name-keyed and flat, so cleanup
                // may not key off the dying scope alone: an inner block
                // that shadowed an outer binding would otherwise drag
                // the outer binding's records down with it. A record
                // dies only when the master stack says the name is
                // truly dead — no surviving depth binds it anymore.
                let survived = self.walk.scopes[..self.walk.scopes.len() - 1]
                    .iter()
                    .any(|s| s.contains_key(name));
                if !survived {
                    self.holds.num_assigns.remove(name);
                    self.holds.nil_severed.remove(name);
                    self.holds.moved_severed.remove(name);
                }
            }
        }
        self.walk.scopes.pop();
        omni::scope_pop(
            self.walk.scopes.len(),
            &omni::root_faces_of(&self.walk.scopes),
        );
    }

    pub(super) fn with_scope<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.enter_scope();
        let r = f(self);
        self.exit_scope();
        r
    }

    pub(super) fn resolve(&self, name: &str) -> Result<(usize, TableShape), ShapeError> {
        self.walk.resolve(name)
    }

    /// The severed-read view: what a MOVED_ROOT binding still is. The
    /// creation-capture law moves a captured table into its env;
    /// pre-Finding-B a severed binding's home scope always popped with
    /// its fn before anything read it again, but a depth-0 table
    /// captured by any fn now outlives the severing, so a read must
    /// see the record it still is — its site identity rides the
    /// severed map, not the (moved-erased) aliases. RAW `resolve`
    /// keeps returning the moved state: the move/adoption laws read
    /// it verbatim, and only type-shaped reads (the module-call
    /// surface) go through this view.
    pub(super) fn resolve_severed_view(
        &self,
        name: &str,
    ) -> Result<(usize, TableShape), ShapeError> {
        let (depth, shape) = self.walk.resolve(name)?;
        if shape.aliases.contains(&MOVED_ROOT)
            && let Some(sites) = self.holds.moved_severed.get(name)
        {
            let mut severed = shape;
            severed.ty = Tbl(Box::new(Pending));
            severed.aliases = sites.clone();
            return Ok((depth, severed));
        }
        Ok((depth, shape))
    }

    pub(super) fn resolve_aliases(&self, name: &str) -> Result<BTreeSet<usize>, ShapeError> {
        Ok(self.resolve(name)?.1.aliases)
    }

    pub(super) fn prov_for_bind(&self, expr: Option<&Expr>, shape: &TableShape) -> Option<Prov> {
        let has_ghost = shape.aliases.iter().any(is_ghost);
        let has_site = shape.aliases.iter().any(|x| !is_root(x) && !is_ghost(x));
        if !(has_ghost && has_site) {
            return None;
        }
        match expr {
            Some(e @ Expr::Call { .. }) => Some(Prov::Call(e.id())),
            Some(Expr::Identifier { name: src, .. }) => self
                .resolve(src)
                .ok()
                .and_then(|(d, _)| self.walk.prov_at(d, src)),
            // C: only a call's return or a resolved name lends provenance
            Some(
                Expr::Integer { .. }
                | Expr::Float { .. }
                | Expr::Boolean { .. }
                | Expr::String { .. }
                | Expr::Nil { .. }
                | Expr::TableCtor { .. }
                | Expr::Index { .. }
                | Expr::BinaryOp { .. }
                | Expr::UnaryOp { .. }
                | Expr::SysAllocCount { .. }
                | Expr::SysExecCount { .. }
                | Expr::FfiModule { .. }
                | Expr::AsyncModule { .. }
                | Expr::Field { .. }
                | Expr::Function { .. },
            )
            | None => None,
        }
    }

    pub(super) fn expr_named_sites(&self, _rec: Gate, expr: &Expr, out: &mut BTreeSet<usize>) {
        match expr {
            Expr::Identifier { name: n, .. } => {
                if let Ok((_, b)) = self.resolve(n) {
                    out.extend(b.aliases.iter().copied().filter(|&s| !is_root(&s)));
                }
            }
            // NOTE historical shape: ctor values only — the Expr keys of
            // entries are not named-site reads (kept for the goldens)
            Expr::TableCtor { entries, .. } => {
                for (_, e) in entries {
                    self.expr_named_sites(_rec, e, out);
                }
            }
            // every other form binds no name whose sites could surface
            Expr::Integer { .. }
            | Expr::Float { .. }
            | Expr::Boolean { .. }
            | Expr::String { .. }
            | Expr::Nil { .. }
            | Expr::Index { .. }
            | Expr::BinaryOp { .. }
            | Expr::UnaryOp { .. }
            | Expr::SysAllocCount { .. }
            | Expr::SysExecCount { .. }
            | Expr::FfiModule { .. }
            | Expr::AsyncModule { .. }
            | Expr::Field { .. }
            | Expr::Function { .. }
            | Expr::Call { .. } => {}
        }
    }
}

/// The While-latch / If-join merge: joins `into`'s shape faces with the
/// twin slots' shapes. The other faces stay `into`'s own — a merge
/// never mints or moves a binding, it only refines shapes. Lives here
/// now: its type is the walk's `Scope`, and its only callers are the
/// two loop arms above.
fn merge_table_scopes(into: &mut [Scope], a: &[Scope], b: &[Scope]) {
    for ((into_slot, a_slot), b_slot) in into.iter_mut().zip(a).zip(b) {
        for (name, val) in into_slot.iter_mut() {
            if let Some(x) = a_slot.get(name) {
                val.shape.join(&x.shape);
            }
            if let Some(x) = b_slot.get(name) {
                val.shape.join(&x.shape);
            }
        }
    }
}
