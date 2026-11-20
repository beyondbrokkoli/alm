use super::*;

/// [fast-lane] The arithmetic shape of a numeric expression — sums and
/// products of literals and names. The walk writes it into
/// `holds.num_assigns` at every decl and assignment; L5's fill-loop
/// detector is the read side (guard nonneg / lower-bound / ascends
/// facts over exactly this grammar).
#[derive(Clone, Debug, PartialEq)]
pub(super) enum NumExpr {
    Lit(i64),
    Var(String),
    Add(Box<NumExpr>, Box<NumExpr>),
    Mul(Box<NumExpr>, Box<NumExpr>),
    Other,
}

pub(super) fn num_of(expr: &Expr) -> NumExpr {
    match expr {
        Expr::Integer { value: v, .. } => NumExpr::Lit(*v),
        Expr::Identifier { name: n, .. } => NumExpr::Var(n.clone()),
        Expr::BinaryOp {
            op: BinOp::Add,
            left,
            right,
            ..
        } => NumExpr::Add(Box::new(num_of(left)), Box::new(num_of(right))),
        Expr::BinaryOp {
            op: BinOp::Mul,
            left,
            right,
            ..
        } => NumExpr::Mul(Box::new(num_of(left)), Box::new(num_of(right))),
        // C: only sums and products of literals/names carry numeric
        // knowledge; every other operator and every non-numeric form is
        // the unknowable
        Expr::BinaryOp { .. }
        | Expr::UnaryOp { .. }
        | Expr::Float { .. }
        | Expr::Boolean { .. }
        | Expr::String { .. }
        | Expr::Nil { .. }
        | Expr::TableCtor { .. }
        | Expr::Index { .. }
        | Expr::SysAllocCount { .. }
        | Expr::SysExecCount { .. }
        | Expr::FfiModule { .. }
        | Expr::AsyncModule { .. }
        | Expr::Field { .. }
        | Expr::Function { .. }
        | Expr::Call { .. } => NumExpr::Other,
    }
}

impl Analyzer {
    pub(super) fn infer_bind(&mut self, rec: Gate, expr: &Expr) -> Result<TableShape, ShapeError> {
        let (ty, aliases, lineage) = self.infer_expr(rec, expr)?;
        Ok(TableShape {
            ty,
            layout: LayoutVerdict::default(),
            aliases,
            lineage,
        })
    }

    pub(super) fn collect_entry_moves(
        &mut self,
        _rec: Gate,
        expr: &Expr,
        out: &mut Vec<(usize, String)>,
    ) -> Result<(), ShapeError> {
        if let Expr::TableCtor { entries, .. } = expr {
            for (_, e) in entries {
                if let Expr::Identifier { name: n, .. } = e {
                    let (d, bind) = self.resolve(n)?;
                    self.record_moved_param(n);
                    self.check_boundary_pin(&bind, n)?;
                    if matches!(bind.ty, Tbl(_)) && !out.iter().any(|(_, m)| m == n) {
                        out.push((d, n.clone()));
                    }
                } else {
                    self.collect_entry_moves(_rec, e, out)?;
                }
            }
        }
        Ok(())
    }

    fn infer_module_call(
        &mut self,
        rec: Gate,
        obj: &Expr,
        name: &str,
        args: &[Expr],
        call_id: NodeId,
    ) -> Result<(Ty, BTreeSet<usize>, RowLineage), ShapeError> {
        let base = match obj {
            Expr::Identifier { name: n, .. } => n.as_str(),
            _ => {
                return Err(ShapeError(Diagnostic::scope(
                    "the ffi surface's '.' base must be a name",
                )));
            }
        };
        // The type-shaped read: a severed module record (captured into
        // a module fn's env by the creation-capture law) still answers
        // as the table it is — resolve_severed_view, not the raw moved
        // state.
        let (_, bind) = self.resolve_severed_view(base)?;
        let module = bind.ty == Ffi;
        if module || bind.ty == FfiLib {
            for a in args {
                self.infer_expr(rec, a)?;
            }
            if module && name == "new" {
                // The mint's site was stamped at derivation — the
                // minted buffer binds as an ordinary owner with that
                // site's alias, so the whole ownership law (scope-exit
                // batches, escape-by-move) applies verbatim. The ty
                // reads the site's current lattice elem so the
                // fixpoint converges: once a store has joined the
                // elem, later passes bind the joined table type
                // directly instead of churning `decide`'s rewrite.
                for a in args {
                    self.infer_expr(rec, a)?;
                }
                if let Some(&site) = self.lattice.sites.get(&call_id) {
                    let ty = match self.lattice.site_elem[site].clone() {
                        Pending => Pending,
                        e => Tbl(Box::new(e)),
                    };
                    return Ok((ty, BTreeSet::from([site]), BTreeMap::new()));
                }
                return Ok((Pending, BTreeSet::new(), BTreeMap::new()));
            }
            return Ok(if module && name == "load" {
                (FfiLib, BTreeSet::new(), BTreeMap::new())
            } else if module && name == "arg_kind" {
                (Int, BTreeSet::new(), BTreeMap::new())
            } else {
                (Pending, BTreeSet::new(), BTreeMap::new())
            });
        }
        if bind.ty == Async {
            for a in args {
                self.infer_expr(rec, a)?;
            }
            return Ok(if name == "status" {
                (Str, BTreeSet::new(), BTreeMap::new())
            } else {
                (Int, BTreeSet::new(), BTreeMap::new())
            });
        }
        if matches!(bind.ty, Tbl(_)) {
            for a in args {
                self.infer_expr(rec, a)?;
            }
            return Ok((Pending, BTreeSet::new(), BTreeMap::new()));
        }
        Err(ShapeError(Diagnostic::scope(format!(
            "'{base}' is not the ffi module, a loaded library, or the async \
             module — '.' is the module surfaces', tables use '[]'"
        ))))
    }

    pub(super) fn infer_expr(
        &mut self,
        rec: Gate,
        expr: &Expr,
    ) -> Result<(Ty, BTreeSet<usize>, RowLineage), ShapeError> {
        match expr {
            Expr::Integer { .. } => Ok((Int, BTreeSet::new(), BTreeMap::new())),
            Expr::Float { .. } => Ok((Flt, BTreeSet::new(), BTreeMap::new())),
            Expr::Boolean { .. } => Ok((Bool, BTreeSet::new(), BTreeMap::new())),
            Expr::String { .. } => Ok((Str, BTreeSet::new(), BTreeMap::new())),
            Expr::Nil { .. } => Ok((Conflict, BTreeSet::new(), BTreeMap::new())),
            Expr::TableCtor { entries, .. } => {
                let id = self.lattice.sites[&expr.id()];
                let mut first_elem_ty: Option<Ty> = None;
                let mut row_sites: Vec<usize> = Vec::new();
                for (ei, (k, e)) in entries.iter().enumerate() {
                    if let CtorKey::Const { slot, .. } = k
                        && let Some(&child) = self.lattice.sites.get(&e.id())
                        && matches!(e, Expr::TableCtor { .. })
                    {
                        self.lattice
                            .site_slots
                            .entry(id)
                            .or_default()
                            .insert(*slot, child);
                    }
                    if let CtorKey::Expr(ke) = k {
                        let (kt, _, _) = self.infer_expr(rec, ke)?;
                        if matches!(kt, Flt | Bool) {
                            continue;
                        }
                        self.pin_int_use(rec, ke, &kt);
                        if rec.on() {
                            self.check_key_threshold(
                                rec,
                                const_key_value(ke, self.surface.index_base()),
                                &BTreeSet::from([id]),
                            )?;
                        }
                    } else if let CtorKey::Const { slot, .. } = k
                        && rec.on()
                    {
                        // [index-base] A minted Const is already
                        // physical; it must never ride the base-aware
                        // reader (the double-shift law).
                        self.check_key_threshold(rec, Some(*slot), &BTreeSet::from([id]))?;
                    }
                    let (t, esites, elineage) = self.infer_expr(rec, e)?;
                    if matches!(t, Pending)
                        && esites.iter().all(|s| is_root(s) || is_ghost(s))
                        && self.walk.scopes.len() == 1
                    {
                        self.reads.boundary_fed.insert(id);
                    }
                    if matches!(t, Tbl(_)) {
                        self.reads.tbl_value_stores.insert(id);
                        for s in esites
                            .iter()
                            .copied()
                            .filter(|s| !is_root(s) && !is_ghost(s))
                        {
                            row_sites.push(s);
                        }
                        if let Some(&child_site) = self.lattice.sites.get(&e.id()) {
                            self.lattice
                                .child_sites
                                .entry(id)
                                .or_default()
                                .insert(child_site);
                        }
                        if !matches!(e, Expr::TableCtor { .. }) {
                            let entry_ghosts: Vec<usize> =
                                esites.iter().copied().filter(is_ghost).collect();
                            if !entry_ghosts.is_empty() {
                                for &g in &entry_ghosts {
                                    let Some(&birth) = self.lattice.ghost_site.get(&g) else {
                                        return Err(ShapeError(Diagnostic::lifetime(
                                            "a row read with a dynamic or \
                                             unproven key cannot be stored — its birth \
                                             site is not visible to the lattice; store a \
                                             row read through a literal key instead",
                                        )));
                                    };
                                    if id == birth || self.birth_closure(id).contains(&birth) {
                                        return Err(ShapeError(Diagnostic::lifetime(
                                            "cyclic row store — the row \
                                             read would be stored into a table that \
                                             already contains it (alm's element types are \
                                             finite)",
                                        )));
                                    }
                                    self.check_row_housing(g, e)?;
                                }
                                for &g in &entry_ghosts {
                                    let birth = self.lattice.ghost_site[&g];
                                    self.reads.row_links.entry(id).or_default().insert(birth);
                                    self.lattice.housed_ghosts.insert(g);
                                    if let CtorKey::Const { slot, .. } = k {
                                        self.lattice
                                            .site_slots
                                            .entry(id)
                                            .or_default()
                                            .insert(*slot, g);
                                    }
                                    if rec.on() {
                                        self.own
                                            .ctor_ghost_keeps
                                            .entry(expr.id())
                                            .or_default()
                                            .push((ei, g));
                                    }
                                }
                            } else if esites.iter().all(is_root) && !elineage.is_empty() {
                                return Err(ShapeError(Diagnostic::lifetime(
                                    "a row read cannot be stored — borrows \
                                     hold no ownership, and cells own exactly the headers \
                                     they are given",
                                )));
                            }
                            self.own.stored_ctor_parents.insert(id);
                            let proj_values: Vec<usize> = esites
                                .iter()
                                .copied()
                                .filter_map(|c| self.proj_node(c))
                                .collect();
                            for c in proj_values {
                                self.reads.row_links.entry(id).or_default().insert(c);
                            }
                        }
                    }
                    match first_elem_ty {
                        None => {
                            first_elem_ty = Some(t.clone());
                        }
                        Some(ref expected) => {
                            let joined = join_ty(expected, &t);
                            if joined == Conflict {
                                if self.lattice.site_elem[id] != Conflict {
                                    self.lattice.site_elem[id] = Conflict;
                                    self.walk.changed = true;
                                }
                            } else {
                                if matches!(joined, Any) && !matches!(expected, Any) {
                                    self.note_adopt(id, self.ctor_lines[id]);
                                }
                                if joined != *expected {
                                    first_elem_ty = Some(joined);
                                }
                            }
                        }
                    }
                    if matches!(t, Conflict) {
                        crate::alm_dbgln!(
                            "[ctor] site {id} line {:?}: cell value is Conflict",
                            self.ctor_lines[id]
                        );
                    }
                    self.decide(rec, id, &t);
                }
                let resolved = if self.lattice.site_elem[id] != Pending {
                    self.lattice.site_elem[id].clone()
                } else {
                    first_elem_ty.unwrap_or(Pending)
                };
                if let Tbl(inner) = &resolved
                    && contains_any(inner)
                {
                    for s in std::mem::take(&mut row_sites) {
                        if self.lattice.site_elem[s] != **inner
                            && !self.fn_body_sites.contains(&s)
                            && !self.fn_param_sites.contains(&s)
                        {
                            self.note_adopt(s, self.ctor_lines[id]);
                            self.decide(rec, s, inner);
                        }
                    }
                }
                Ok((
                    Tbl(Box::new(resolved)),
                    BTreeSet::from([id]),
                    BTreeMap::new(),
                ))
            }
            Expr::Index { obj, key, .. } => {
                let (kt, _, _) = self.infer_expr(rec, key)?;
                if matches!(kt, Flt | Bool) {
                    crate::alm_dbgln!("[idx] bad key ty={:?}", kt);
                    self.infer_expr(rec, obj)?;
                    return Ok((Conflict, BTreeSet::new(), BTreeMap::new()));
                }
                let (t, sites, mut lineage) = self.infer_expr(rec, obj)?;
                if !matches!(t, Tbl(_)) {
                    let r = if matches!(t, Pending) {
                        Pending
                    } else {
                        Conflict
                    };
                    for (&origin, (name, d)) in &lineage {
                        if is_ghost(&origin) {
                            continue;
                        }
                        let depth = d + 1;
                        let e = self
                            .reads
                            .row_reads
                            .entry(origin)
                            .or_insert((name.clone(), depth));
                        if depth > e.1 {
                            e.1 = depth;
                        }
                    }
                    return Ok((r, BTreeSet::new(), BTreeMap::new()));
                }
                self.pin_int_use(rec, key, &kt);
                let claimed_rows: BTreeSet<usize> = self
                    .lattice
                    .claimed_ghosts
                    .iter()
                    .filter_map(|g| self.lattice.ghost_site.get(g).copied())
                    .collect();
                if !claimed_rows.is_empty() {
                    let err = || {
                        ShapeError(Diagnostic::lifetime(
                            "this row was already released with its \
                             housing — read it through the housing's cell before it \
                             drops",
                        ))
                    };
                    for &s in &sites {
                        let row = if is_ghost(&s) {
                            self.lattice.ghost_site.get(&s).copied()
                        } else {
                            Some(s)
                        };
                        if row.is_some_and(|r| claimed_rows.contains(&r)) {
                            return Err(err());
                        }
                    }
                    let slot_claimed = |base: usize, k: Option<i64>| -> bool {
                        self.lattice.site_slots.get(&base).is_some_and(|m| {
                            m.iter().any(|(kk, node)| {
                                k.is_none_or(|x| *kk == x)
                                    && self
                                        .proj_node(*node)
                                        .is_some_and(|p| claimed_rows.contains(&p))
                            })
                        })
                    };
                    let k = const_key_value(key, self.surface.index_base());
                    for &s in &sites {
                        if !is_root(&s) && slot_claimed(s, k) {
                            return Err(err());
                        }
                    }
                }
                let mut r = Pending;
                for s in &sites {
                    if !is_root(s) && !is_ghost(s) {
                        self.lattice.needed[*s] = true;
                        r = join_ty(&r, &self.lattice.site_elem[*s]);
                    } else if is_ghost(s) {
                        r = join_ty(&r, &self.ghost_row_elem(*s));
                    }
                }
                for (&origin, (name, d)) in &lineage {
                    if is_ghost(&origin) {
                        continue;
                    }
                    let depth = d + 1;
                    let e = self
                        .reads
                        .row_reads
                        .entry(origin)
                        .or_insert((name.clone(), depth));
                    if depth > e.1 {
                        e.1 = depth;
                    }
                }
                for (_, d) in lineage.values_mut() {
                    *d += 1;
                }
                if let Expr::Identifier { name, .. } = obj.as_ref() {
                    for &s in &sites {
                        if !is_root(&s) {
                            lineage.entry(s).or_insert((name.clone(), 1));
                        }
                    }
                }
                let aliases = if lineage.is_empty() || value_kind(&r) || matches!(r, Conflict) {
                    BTreeSet::new()
                } else {
                    // [ownership] the row-ghost mint: a row read is a
                    // ghost alias whose birth site and key ride the
                    // lattice.
                    let node = expr.id();
                    let ghost = match self.lattice.row_ghosts.get(&node) {
                        Some(&g) => g,
                        None => {
                            let g = self.lattice.row_ghost_next;
                            self.lattice.row_ghost_next += 1;
                            self.lattice.row_ghosts.insert(node, g);
                            g
                        }
                    };
                    let bases: BTreeSet<usize> =
                        sites.iter().copied().filter(|s| !is_root(s)).collect();
                    self.lattice.ghost_mints.insert(
                        ghost,
                        GhostMint {
                            bases,
                            key: const_key_value(key, self.surface.index_base()),
                        },
                    );
                    if let Some(k) = const_key_value(key, self.surface.index_base()) {
                        let real: Vec<usize> = sites
                            .iter()
                            .copied()
                            .filter(|s| !is_root(s) && !is_ghost(s))
                            .collect();
                        if real.len() == 1
                            && let Some(&slot) = self
                                .lattice
                                .site_slots
                                .get(&real[0])
                                .and_then(|m| m.get(&k))
                        {
                            let birth = if is_ghost(&slot) {
                                self.lattice.ghost_site.get(&slot).copied()
                            } else {
                                Some(slot)
                            };
                            if let Some(b) = birth {
                                self.lattice.ghost_site.insert(ghost, b);
                            }
                        }
                    }
                    BTreeSet::from([ghost])
                };
                Ok((r, aliases, lineage))
            }
            Expr::Identifier { name, .. } => {
                let (depth, bind) = self.resolve(name)?;
                let _ = depth;
                if matches!(bind.ty, Conflict) {
                    crate::alm_dbgln!(
                        "[ident] '{name}' resolves to Conflict aliases={:?}",
                        bind.aliases
                    );
                }
                Ok((bind.ty, bind.aliases.clone(), bind.lineage.clone()))
            }
            Expr::BinaryOp {
                op, left, right, ..
            } => {
                let (lt, _, _) = self.infer_expr(rec, left)?;
                let (rt, _, _) = self.infer_expr(rec, right)?;
                match op {
                    BinOp::And | BinOp::Or => {
                        self.pin_bool_use(rec, left, &lt);
                        self.pin_bool_use(rec, right, &rt);
                    }
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::IntDiv
                    | BinOp::Mod
                    | BinOp::Div
                    | BinOp::LessThan
                    | BinOp::GreaterThan
                    | BinOp::LessEq
                    | BinOp::GreaterEq => {
                        self.pin_numeric_pair(rec, left, &lt, right, &rt);
                    }
                    BinOp::Equal | BinOp::NotEqual => {
                        self.pin_scalar_pair(rec, left, &lt, right, &rt);
                    }
                    // '..' pins nothing here — the checker's Concat arm
                    // (L4) is the one law that binds unknowns to Str;
                    // the lattice only needs the result type below.
                    BinOp::Concat => {}
                }
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::IntDiv | BinOp::Mod => {
                        if let Some(t) = self.computed_arith_scalar(rec, left, &lt, right, &rt) {
                            return Ok((t, BTreeSet::new(), BTreeMap::new()));
                        }
                    }
                    BinOp::Div => {
                        if let Some(t) = self.computed_div_scalar(rec, left, &lt, right, &rt) {
                            return Ok((t, BTreeSet::new(), BTreeMap::new()));
                        }
                    }
                    _ => {}
                }
                match op {
                    BinOp::Div if matches!(lt, Int | Flt) && matches!(rt, Int | Flt) => {
                        Ok((Flt, BTreeSet::new(), BTreeMap::new()))
                    }
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::IntDiv | BinOp::Mod => {
                        if matches!(arith_ty(lt.clone(), rt.clone()), Conflict) {
                            crate::alm_dbgln!("[arith] {:?} {op:?} {:?} = Conflict", lt, rt);
                        }
                        Ok((arith_ty(lt, rt), BTreeSet::new(), BTreeMap::new()))
                    }
                    BinOp::Concat => Ok((Str, BTreeSet::new(), BTreeMap::new())),
                    _ => Ok((Bool, BTreeSet::new(), BTreeMap::new())),
                }
            }
            Expr::UnaryOp { op, expr, .. } => {
                let (t, _, _) = self.infer_expr(rec, expr)?;
                match op {
                    UnOp::Neg => {
                        self.pin_int_use(rec, expr, &t);
                        if let Some(k) = self.computed_neg_scalar(rec, expr, &t) {
                            return Ok((k, BTreeSet::new(), BTreeMap::new()));
                        }
                        Ok((t, BTreeSet::new(), BTreeMap::new()))
                    }
                    UnOp::Not => {
                        self.pin_bool_use(rec, expr, &t);
                        Ok((Bool, BTreeSet::new(), BTreeMap::new()))
                    }
                    UnOp::Len => Ok((Int, BTreeSet::new(), BTreeMap::new())),
                }
            }
            Expr::SysAllocCount { .. } => Ok((Int, BTreeSet::new(), BTreeMap::new())),
            Expr::SysExecCount { .. } => Ok((Int, BTreeSet::new(), BTreeMap::new())),
            Expr::FfiModule { .. } => Ok((Ffi, BTreeSet::new(), BTreeMap::new())),
            Expr::AsyncModule { .. } => Ok((Async, BTreeSet::new(), BTreeMap::new())),
            Expr::Field { obj, .. } => {
                let (ty, sites, lineage) = self.infer_expr(rec, obj)?;
                match ty {
                    Tbl(inner) if matches!(*inner, Conflict) => {
                        crate::alm_dbgln!("[field] dot read on Tbl(Conflict) sites={:?}", sites);
                        Ok((*inner, sites, lineage))
                    }
                    Tbl(inner) => Ok((*inner, sites, lineage)),
                    _ => {
                        crate::alm_dbgln!(
                            "[field] dot access on non-table ty={:?} sites={:?}",
                            ty,
                            sites
                        );
                        Err(ShapeError(Diagnostic::scope(
                            "dot access needs a record or the ffi surface",
                        )))
                    }
                }
            }
            Expr::Function { .. } => Ok((Pending, BTreeSet::new(), BTreeMap::new())),
            Expr::Call { callee, args, .. } => {
                let name: String = match callee.as_ref() {
                    Expr::Field { obj, name, .. } => {
                        if let Some(dotted) = dotted_callee(callee.as_ref())
                            && self.resolve_fn(&dotted).is_some()
                        {
                            dotted
                        } else {
                            return self.infer_module_call(rec, obj, name, args, expr.id());
                        }
                    }
                    Expr::Identifier { name: n, .. } => n.clone(),
                    _ => {
                        return Err(ShapeError(calls_through_fn_var_msg()));
                    }
                };
                let name = name.as_str();
                let Some(fn_ptr) = self.resolve_fn(name) else {
                    for a in args {
                        self.infer_expr(rec, a)?;
                        self.check_uses(rec, a)?;
                    }
                    return Ok((Pending, BTreeSet::new(), BTreeMap::new()));
                };
                let params = self.fn_params.get(&fn_ptr).cloned().unwrap_or_default();
                let stored_params = self.fn_store_params.get(&fn_ptr).cloned();
                let moved_params = self.fn_moved_params.get(&fn_ptr).cloned();
                let ret_params = self.fn_ret_params.get(&fn_ptr).cloned();
                let mut ret_pinned = false;
                let mut ret_arg_sites: BTreeSet<usize> = BTreeSet::new();
                let mut ret_lineage: RowLineage = BTreeMap::new();
                for (i, a) in args.iter().enumerate() {
                    if let Expr::Identifier { name: n, .. } = a {
                        let moves_it = moved_params
                            .as_ref()
                            .is_some_and(|m| params.get(i).is_some_and(|p| m.contains(p)));
                        if moves_it {
                            let cur = self
                                .fn_walk
                                .last()
                                .map(|(fp, ps)| (*fp, ps.iter().any(|p| p == n)));
                            if let Some((cur_fn, is_param)) = cur
                                && is_param
                            {
                                self.fn_moved_params
                                    .entry(cur_fn)
                                    .or_default()
                                    .insert(n.clone());
                            }
                            if let Ok((_, bind)) = self.resolve(n)
                                && bind.aliases.contains(&BOUNDARY_ROOT)
                            {
                                let p = params.get(i).cloned().unwrap_or_default();
                                return Err(ShapeError(Diagnostic::lifetime(format!(
                                    "'{name}' moves its parameter '{p}' \
                                     into another table or binding — the pinned table \
                                     '{n}' may not be passed to it (the host owns the \
                                     boundary header)"
                                ))));
                            }
                        }
                        if ret_params.as_ref().is_some_and(|r| r.contains(&i))
                            && let Ok((_, bind)) = self.resolve(n)
                            && bind.aliases.contains(&BOUNDARY_ROOT)
                        {
                            ret_pinned = true;
                        }
                    }
                    let (_, sites, arg_lineage) = self.infer_expr(rec, a)?;
                    if let Some(p) = params.get(i)
                        && let Some(stored) = &stored_params
                        && stored.contains(p)
                    {
                        self.fn_param_sites.extend(
                            sites
                                .iter()
                                .copied()
                                .filter(|s| !is_root(s) && !is_ghost(s)),
                        );
                    }
                    if ret_params.as_ref().is_some_and(|r| r.contains(&i))
                        && !matches!(a, Expr::Identifier { .. })
                    {
                        ret_arg_sites.extend(sites.iter().copied().filter(|s| !is_root(s)));
                        for (origin, val) in &arg_lineage {
                            match ret_lineage.entry(*origin) {
                                std::collections::btree_map::Entry::Vacant(v) => {
                                    v.insert(val.clone());
                                }
                                std::collections::btree_map::Entry::Occupied(mut o) => {
                                    if val.1 > o.get().1 {
                                        o.get_mut().1 = val.1;
                                    }
                                }
                            }
                        }
                    }
                }
                if let Some(shape) = self.fn_ret_shapes.get(&fn_ptr) {
                    let mut aliases = shape.aliases.clone();
                    aliases.extend(ret_arg_sites);
                    if ret_pinned {
                        aliases.insert(BOUNDARY_ROOT);
                    }
                    let mut lineage = shape.lineage.clone();
                    for (origin, (name, d)) in ret_lineage {
                        match lineage.entry(origin) {
                            std::collections::btree_map::Entry::Vacant(v) => {
                                v.insert((name, d));
                            }
                            std::collections::btree_map::Entry::Occupied(mut o) => {
                                if d > o.get().1 {
                                    o.get_mut().1 = d;
                                }
                            }
                        }
                    }
                    Ok((shape.ty.clone(), aliases, lineage))
                } else {
                    Ok((Pending, BTreeSet::new(), BTreeMap::new()))
                }
            }
        }
    }

    /// [index-base] `key` is the key's PHYSICAL compile-time value
    /// (callers translate at their boundary: user-space expressions
    /// through `const_key_value(key, index_base)`, minted `Const` slots
    /// raw). The thresholds compare physical indices, matching the
    /// runtime's `set_core`.
    pub(super) fn check_key_threshold(
        &mut self,
        _rec: Gate,
        key: Option<i64>,
        sites: &BTreeSet<usize>,
    ) -> Result<(), ShapeError> {
        if let Some(i) = key {
            if i >= BOUNDS_FAIL_THRESHOLD {
                return Err(ShapeError(Diagnostic::bounds("table index overflow")));
            }
            if i > SPARSE_THRESHOLD {
                for &site in sites {
                    if !is_root(&site) && !is_ghost(&site) {
                        self.layout.verdicts[site] =
                            self.layout.verdicts[site].join(LayoutVerdict::Sparse);
                    }
                }
            }
        }
        Ok(())
    }
}
