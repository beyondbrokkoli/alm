use super::*;
use crate::ast::has_break;
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
        Expr::Integer(v) => NumExpr::Lit(*v),
        Expr::Identifier(n) => NumExpr::Var(n.clone()),
        Expr::BinaryOp {
            op: BinOp::Add,
            left,
            right,
        } => NumExpr::Add(Box::new(num_of(left)), Box::new(num_of(right))),
        Expr::BinaryOp {
            op: BinOp::Mul,
            left,
            right,
        } => NumExpr::Mul(Box::new(num_of(left)), Box::new(num_of(right))),
        _ => NumExpr::Other,
    }
}

pub(super) fn provably_nonneg(
    num_assigns: &BTreeMap<String, Vec<NumExpr>>,
    expr: &NumExpr,
    self_name: &str,
    path: &mut BTreeSet<String>,
) -> bool {
    match expr {
        NumExpr::Lit(v) => *v >= 0,
        NumExpr::Var(n) => {
            if n == self_name {
                true
            } else if path.contains(n) {
                false
            } else {
                let Some(shapes) = num_assigns.get(n) else {
                    return false;
                };
                path.insert(n.clone());
                let ok = shapes
                    .iter()
                    .all(|sh| provably_nonneg(num_assigns, sh, n, path));
                path.remove(n);
                ok
            }
        }
        NumExpr::Add(a, b) | NumExpr::Mul(a, b) => {
            provably_nonneg(num_assigns, a, self_name, path)
                && provably_nonneg(num_assigns, b, self_name, path)
        }
        NumExpr::Other => false,
    }
}

pub(super) fn guard_provably_nonneg_expr(
    num_assigns: &BTreeMap<String, Vec<NumExpr>>,
    expr: &Expr,
) -> bool {
    let mut path = BTreeSet::new();
    provably_nonneg(num_assigns, &num_of(expr), "", &mut path)
}

pub(super) fn guard_provably_nonneg(
    num_assigns: &BTreeMap<String, Vec<NumExpr>>,
    guard: &str,
) -> bool {
    num_assigns.get(guard).is_some_and(|shapes| {
        let mut path = BTreeSet::new();
        shapes
            .iter()
            .all(|sh| provably_nonneg(num_assigns, sh, guard, &mut path))
    })
}

pub(super) fn guard_only_ascends(
    num_assigns: &BTreeMap<String, Vec<NumExpr>>,
    stmts: &[Stmt],
    guard: &str,
) -> bool {
    for s in stmts {
        match s {
            Stmt::Assignment { name, expr } if name == guard => {
                let Expr::BinaryOp {
                    op: BinOp::Add,
                    left,
                    right,
                } = expr
                else {
                    return false;
                };
                if !matches!(left.as_ref(), Expr::Identifier(n) if n == guard) {
                    return false;
                }
                if !guard_provably_nonneg_expr(num_assigns, right) {
                    return false;
                }
            }
            Stmt::While { body, .. } | Stmt::Do { body } => {
                if !guard_only_ascends(num_assigns, body, guard) {
                    return false;
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } if !guard_only_ascends(num_assigns, then_body, guard)
                || !guard_only_ascends(num_assigns, else_body, guard) =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
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
        rec: Gate,
        expr: &Expr,
        out: &mut Vec<(usize, String)>,
    ) -> Result<(), ShapeError> {
        if let Expr::TableCtor(entries) = expr {
            for (_, e) in entries {
                if let Expr::Identifier(n) = e {
                    let (d, bind) = self.resolve(rec, n)?;
                    self.record_moved_param(n);
                    self.check_boundary_pin(&bind, n)?;
                    if matches!(bind.ty, Tbl(_)) && !out.iter().any(|(_, m)| m == n) {
                        out.push((d, n.clone()));
                    }
                } else {
                    self.collect_entry_moves(rec, e, out)?;
                }
            }
        }
        Ok(())
    }

    /// The module-surface half of a dotted call (`A.b(x)` where "A.b" is
    /// NOT an expansion binding): ffi load/arg_kind, loaded libraries,
    /// the coroutine verbs. The D4 expansion-map precedence in
    /// `infer_expr`'s Call arm decides which half a dotted call is.
    fn infer_module_call(
        &mut self,
        rec: Gate,
        obj: &Expr,
        name: &str,
        args: &[Expr],
    ) -> Result<(Ty, BTreeSet<usize>, RowLineage), ShapeError> {
        let base = match obj {
            Expr::Identifier(n) => n.as_str(),
            _ => {
                return Err(ShapeError(
                    "Scope Error: the ffi surface's '.' base must be a name".into(),
                ));
            }
        };
        let (_, bind) = self.resolve(rec, base)?;
        let module = bind.ty == Ffi;
        if module || bind.ty == FfiLib {
            for a in args {
                self.infer_expr(rec, a)?;
            }
            return Ok(if module && name == "load" {
                (FfiLib, BTreeSet::new(), BTreeMap::new())
            } else if module && name == "arg_kind" {
                (Int, BTreeSet::new(), BTreeMap::new())
            } else {
                (Pending, BTreeSet::new(), BTreeMap::new())
            });
        }
        if bind.ty == Coro {
            for a in args {
                self.infer_expr(rec, a)?;
            }
            return Ok(if name == "status" {
                (Str, BTreeSet::new(), BTreeMap::new())
            } else {
                (Int, BTreeSet::new(), BTreeMap::new())
            });
        }
        Err(ShapeError(format!(
            "Scope Error: '{base}' is not the ffi module, a loaded library, or the coroutine \
             module — '.' is the module surfaces', tables use '[]'"
        )))
    }

    pub(super) fn infer_expr(
        &mut self,
        rec: Gate,
        expr: &Expr,
    ) -> Result<(Ty, BTreeSet<usize>, RowLineage), ShapeError> {
        match expr {
            Expr::Integer(_) => {
                signal!(rec.on(), trace::TRACE_INFER_INT);
                Ok((Int, BTreeSet::new(), BTreeMap::new()))
            }
            Expr::Float(_) => {
                signal!(rec.on(), trace::TRACE_INFER_FLT);
                Ok((Flt, BTreeSet::new(), BTreeMap::new()))
            }
            Expr::Boolean(_) => {
                signal!(rec.on(), trace::TRACE_INFER_BOOL);
                Ok((Bool, BTreeSet::new(), BTreeMap::new()))
            }
            Expr::String(_) => {
                signal!(rec.on(), trace::TRACE_INFER_STR);
                Ok((Str, BTreeSet::new(), BTreeMap::new()))
            }
            Expr::Nil => {
                signal!(rec.on(), trace::TRACE_INFER_NIL);
                Ok((Conflict, BTreeSet::new(), BTreeMap::new()))
            }
            Expr::TableCtor(entries) => {
                let id = self.lattice.sites[&(expr as *const Expr)];
                let mut first_elem_ty: Option<Ty> = None;
                let mut row_sites: Vec<usize> = Vec::new();
                for (ei, (k, e)) in entries.iter().enumerate() {
                    if let CtorKey::Const(c) = k
                        && let Some(&child) = self.lattice.sites.get(&(e as *const Expr))
                        && matches!(e, Expr::TableCtor(_))
                    {
                        self.lattice
                            .site_slots
                            .entry(id)
                            .or_default()
                            .insert(*c, child);
                    }
                    if let CtorKey::Expr(ke) = k {
                        let (kt, _, _) = self.infer_expr(rec, ke)?;
                        if matches!(kt, Flt | Bool) {
                            signal!(rec.on(), trace::TRACE_INFER_IDX_BAD_KEY);
                            continue;
                        }
                        // an expression key pins to Integer when the
                        // walk can see its node
                        self.pin_int_use(rec, ke, &kt);
                        if rec.on() {
                            self.check_key_threshold(rec, ke, &BTreeSet::from([id]))?;
                        }
                    } else if let CtorKey::Const(c) = k
                        && rec.on()
                    {
                        self.check_key_threshold(rec, &Expr::Integer(*c), &BTreeSet::from([id]))?;
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
                        if let Some(&child_site) = self.lattice.sites.get(&(e as *const Expr)) {
                            signal!(rec.on(), trace::TRACE_INFER_TBL_CHILD);
                            self.lattice
                                .child_sites
                                .entry(id)
                                .or_default()
                                .insert(child_site);
                        }
                        if !matches!(e, Expr::TableCtor(_)) {
                            let entry_ghosts: Vec<usize> =
                                esites.iter().copied().filter(is_ghost).collect();
                            if !entry_ghosts.is_empty() {
                                signal!(rec.on(), trace::TRACE_ROW_HOUSING);
                                for &g in &entry_ghosts {
                                    let Some(&birth) = self.lattice.ghost_site.get(&g) else {
                                        signal!(rec.on(), trace::TRACE_FAIL_ROW_STORE);
                                        return Err(ShapeError(
                                            "Lifetime Error: a row read with a dynamic or \
                                             unproven key cannot be stored — its birth \
                                             site is not visible to the lattice; store a \
                                             row read through a literal key instead"
                                                .to_string(),
                                        ));
                                    };
                                    if id == birth || self.birth_closure(id).contains(&birth) {
                                        signal!(rec.on(), trace::TRACE_FAIL_ROW_STORE);
                                        return Err(ShapeError(
                                            "Lifetime Error: cyclic row store — the row \
                                             read would be stored into a table that \
                                             already contains it (alm's element types \
                                             are finite)"
                                                .to_string(),
                                        ));
                                    }
                                    self.check_row_housing(g, e)?;
                                }
                                for &g in &entry_ghosts {
                                    let birth = self.lattice.ghost_site[&g];
                                    self.reads.row_links.entry(id).or_default().insert(birth);
                                    self.lattice.housed_ghosts.insert(g);
                                    if let CtorKey::Const(c) = k {
                                        self.lattice
                                            .site_slots
                                            .entry(id)
                                            .or_default()
                                            .insert(*c, g);
                                    }
                                    if rec.on() {
                                        self.own
                                            .ctor_ghost_keeps
                                            .entry(expr as *const Expr)
                                            .or_default()
                                            .push((ei, g));
                                        signal!(rec.on(), trace::TRACE_ROW_HOUSED);
                                    }
                                }
                            } else if esites.iter().all(is_root) && !elineage.is_empty() {
                                signal!(rec.on(), trace::TRACE_FAIL_BORROW_ESCAPE);
                                return Err(ShapeError(
                                    "Lifetime Error: a row read cannot be stored — borrows \
                                     hold no ownership, and cells own exactly the headers \
                                     they are given"
                                        .to_string(),
                                ));
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
                            signal!(rec.on(), trace::TRACE_INFER_TBL_FIRST);
                            first_elem_ty = Some(t.clone());
                        }
                        Some(ref expected) => {
                            let joined = join_ty(expected, &t);
                            if joined == Conflict {
                                signal!(rec.on(), trace::TRACE_INFER_TBL_MISMATCH);
                                if self.lattice.site_elem[id] != Conflict {
                                    self.probe(rec, trace::TRACE_INFER_TBL_CONFLICT);
                                    self.lattice.site_elem[id] = Conflict;
                                    self.walk.changed = true;
                                }
                            } else {
                                signal!(rec.on(), trace::TRACE_INFER_TBL_MATCH);
                                if matches!(joined, Any) && !matches!(expected, Any) {
                                    self.probe(rec, trace::TRACE_CHK_ANY_MIXED_CTOR);
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
                    signal!(rec.on(), trace::TRACE_INFER_TBL_RESOLVED);
                    self.lattice.site_elem[id].clone()
                } else {
                    signal!(rec.on(), trace::TRACE_INFER_TBL_PENDING);
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
                            self.probe(rec, trace::TRACE_CHK_ANY_MIXED_ROWS);
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
            Expr::Index { obj, key } => {
                let (kt, _, _) = self.infer_expr(rec, key)?;
                if matches!(kt, Flt | Bool) {
                    crate::alm_dbgln!("[idx] bad key ty={:?}", kt);
                    signal!(rec.on(), trace::TRACE_INFER_IDX_BAD_KEY);
                    self.infer_expr(rec, obj)?;
                    return Ok((Conflict, BTreeSet::new(), BTreeMap::new()));
                }
                let (t, sites, mut lineage) = self.infer_expr(rec, obj)?;
                if !matches!(t, Tbl(_)) {
                    signal!(rec.on(), trace::TRACE_INFER_IDX_BAD_OBJ);
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
                // base checks out as a table: the key discipline pins an
                // unresolved key to Integer (mirroring the checking
                // half's base-then-key order)
                self.pin_int_use(rec, key, &kt);
                let claimed_rows: BTreeSet<usize> = self
                    .lattice
                    .claimed_ghosts
                    .iter()
                    .filter_map(|g| self.lattice.ghost_site.get(g).copied())
                    .collect();
                if !claimed_rows.is_empty() {
                    let err = || {
                        ShapeError(
                            "Lifetime Error: this row was already released with its \
                             housing — read it through the housing's cell before it \
                             drops"
                                .to_string(),
                        )
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
                    let k = const_key_value(key);
                    for &s in &sites {
                        if !is_root(&s) && slot_claimed(s, k) {
                            return Err(err());
                        }
                    }
                }
                let mut r = Pending;
                for s in &sites {
                    if !is_root(s) && !is_ghost(s) {
                        signal!(rec.on(), trace::TRACE_INFER_IDX_VALID);
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
                if let Expr::Identifier(name) = obj.as_ref() {
                    for &s in &sites {
                        if !is_root(&s) {
                            lineage.entry(s).or_insert((name.clone(), 1));
                        }
                    }
                }
                let aliases = if lineage.is_empty() || value_kind(&r) || matches!(r, Conflict) {
                    BTreeSet::new()
                } else {
                    signal!(rec.on(), trace::TRACE_ROW_GHOST_MINT);
                    let node = expr as *const Expr;
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
                            key: const_key_value(key),
                        },
                    );
                    if let Some(k) = const_key_value(key) {
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
            Expr::Identifier(name) => {
                signal!(rec.on(), trace::TRACE_INFER_IDENT);
                let (depth, bind) = self.resolve(rec, name)?;
                let _ = depth;
                if matches!(bind.ty, Conflict) {
                    crate::alm_dbgln!(
                        "[ident] '{name}' resolves to Conflict aliases={:?}",
                        bind.aliases
                    );
                }
                Ok((bind.ty, bind.aliases.clone(), bind.lineage.clone()))
            }
            Expr::BinaryOp { op, left, right } => {
                let (lt, _, _) = self.infer_expr(rec, left)?;
                let (rt, _, _) = self.infer_expr(rec, right)?;
                // the use-site pin disciplines, mirroring the checking
                // half at this same operator: Boolean operands for
                // and/or, the numeric pair for arithmetic and the
                // comparisons, the scalar pair for equality
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
                }
                // the computed-scalar discipline: where the just-landed
                // pins closed both operands and the checker's own
                // discipline at this operator would return a type
                // without error, the walk binds that type directly (the
                // binding is the value view; no held `top` entry). The
                // fixpoint and walk-blind operands keep the Pending
                // shape below.
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
                        signal!(rec.on(), trace::TRACE_INFER_BINOP_ARITH);
                        Ok((Flt, BTreeSet::new(), BTreeMap::new()))
                    }
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::IntDiv | BinOp::Mod => {
                        signal!(rec.on(), trace::TRACE_INFER_BINOP_ARITH);
                        if matches!(arith_ty(lt.clone(), rt.clone()), Conflict) {
                            crate::alm_dbgln!("[arith] {:?} {op:?} {:?} = Conflict", lt, rt);
                        }
                        Ok((arith_ty(lt, rt), BTreeSet::new(), BTreeMap::new()))
                    }
                    _ => {
                        signal!(rec.on(), trace::TRACE_INFER_BINOP_OTHER);
                        Ok((Bool, BTreeSet::new(), BTreeMap::new()))
                    }
                }
            }
            Expr::UnaryOp { op, expr } => {
                let (t, _, _) = self.infer_expr(rec, expr)?;
                match op {
                    UnOp::Neg => {
                        signal!(rec.on(), trace::TRACE_INFER_UNOP_NEG);
                        // unary '-' pins its operand to Integer
                        self.pin_int_use(rec, expr, &t);
                        // the computed-scalar discipline (same as the
                        // binary operators): a closed operand binds its
                        // kind directly
                        if let Some(k) = self.computed_neg_scalar(rec, expr, &t) {
                            return Ok((k, BTreeSet::new(), BTreeMap::new()));
                        }
                        Ok((t, BTreeSet::new(), BTreeMap::new()))
                    }
                    UnOp::Not => {
                        signal!(rec.on(), trace::TRACE_INFER_UNOP_NOT);
                        // 'not' pins its operand to Boolean
                        self.pin_bool_use(rec, expr, &t);
                        Ok((Bool, BTreeSet::new(), BTreeMap::new()))
                    }
                    UnOp::Len => {
                        signal!(rec.on(), trace::TRACE_INFER_UNOP_LEN);
                        Ok((Int, BTreeSet::new(), BTreeMap::new()))
                    }
                }
            }
            Expr::SysAllocCount => {
                signal!(rec.on(), trace::TRACE_INFER_SYSALLOC);
                Ok((Int, BTreeSet::new(), BTreeMap::new()))
            }
            Expr::SysExecCount => {
                signal!(rec.on(), trace::TRACE_INFER_SYS_EXEC);
                Ok((Int, BTreeSet::new(), BTreeMap::new()))
            }
            Expr::FfiModule => Ok((Ffi, BTreeSet::new(), BTreeMap::new())),
            Expr::CoroModule => Ok((Coro, BTreeSet::new(), BTreeMap::new())),
            Expr::Field { obj, .. } => {
                // a record read answers the table's element type and rides
                // the receiver's sites: record cells are the table's elem
                // (Any for heterogeneous records), and the constant-key
                // row-read lifetime machinery does not apply to names
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
                        Err(ShapeError(
                            "Scope Error: dot access needs a record or the ffi surface".into(),
                        ))
                    }
                }
            }
            Expr::Function { .. } => {
                signal!(rec.on(), trace::TRACE_INFER_IDENT);
                Ok((Pending, BTreeSet::new(), BTreeMap::new()))
            }
            Expr::Call { callee, args } => {
                let name: String = match callee.as_ref() {
                    Expr::Field { obj, name } => {
                        // D4 precedence, walk half: a dotted callee chain
                        // ("A.b", "A.B.c") that resolves through the fn
                        // maps is an expansion call — the expansion map
                        // wins; module surfaces are the fallback.
                        if let Some(dotted) = dotted_callee(callee.as_ref())
                            && self.resolve_fn(&dotted).is_some()
                        {
                            dotted
                        } else {
                            return self.infer_module_call(rec, obj, name, args);
                        }
                    }
                    Expr::Identifier(n) => n.clone(),
                    _ => {
                        return Err(ShapeError(calls_through_fn_var_msg()));
                    }
                };
                let name = name.as_str();
                let fn_ptr = self
                    .resolve_fn(name)
                    .ok_or_else(|| ShapeError(not_a_function_msg(name)))?;
                let params = self.fn_params.get(&fn_ptr).cloned().unwrap_or_default();
                let stored_params = self.fn_store_params.get(&fn_ptr).cloned();
                let moved_params = self.fn_moved_params.get(&fn_ptr).cloned();
                let ret_params = self.fn_ret_params.get(&fn_ptr).cloned();
                let mut ret_pinned = false;
                let mut ret_arg_sites: BTreeSet<usize> = BTreeSet::new();
                let mut ret_lineage: RowLineage = BTreeMap::new();
                for (i, a) in args.iter().enumerate() {
                    if let Expr::Identifier(n) = a {
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
                            if let Ok((_, bind)) = self.resolve(rec, n)
                                && bind.aliases.contains(&BOUNDARY_ROOT)
                            {
                                let p = params.get(i).cloned().unwrap_or_default();
                                return Err(ShapeError(format!(
                                    "Lifetime Error: '{name}' moves its parameter '{p}' \
                                     into another table or binding — the pinned table \
                                     '{n}' may not be passed to it (the host owns the \
                                     boundary header)"
                                )));
                            }
                        }
                        if ret_params.as_ref().is_some_and(|r| r.contains(&i))
                            && let Ok((_, bind)) = self.resolve(rec, n)
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
                        && !matches!(a, Expr::Identifier(_))
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
                    signal!(rec.on(), trace::TRACE_INFER_IDENT);
                    Ok((Pending, BTreeSet::new(), BTreeMap::new()))
                }
            }
        }
    }

    pub(super) fn check_key_threshold(
        &mut self,
        rec: Gate,
        key: &Expr,
        sites: &BTreeSet<usize>,
    ) -> Result<(), ShapeError> {
        if let Some(i) = const_key_value(key) {
            signal!(rec.on(), trace::TRACE_THRESH_INT);
            if i >= BOUNDS_FAIL_THRESHOLD {
                signal!(rec.on(), trace::TRACE_THRESH_BOUNDS);
                return Err(ShapeError(
                    "Table Bounds Error: table index overflow".to_string(),
                ));
            }
            if i > SPARSE_THRESHOLD {
                signal!(rec.on(), trace::TRACE_THRESH_SPARSE);
                for &site in sites {
                    if !is_root(&site) && !is_ghost(&site) {
                        signal!(rec.on(), trace::TRACE_THRESH_SPARSE_ALIAS);
                        self.layout.verdicts[site] =
                            self.layout.verdicts[site].join(LayoutVerdict::Sparse);
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn detect_fill_loop(&mut self, rec: Gate, guard: &str, body: &[Stmt]) {
        if has_break(body) {
            return;
        }
        if !guard_provably_nonneg(&self.holds.num_assigns, guard) {
            return;
        }
        if !guard_only_ascends(&self.holds.num_assigns, body, guard) {
            return;
        }

        let mutated = self.collect_mutated_names(rec, body);
        let mut fills = BTreeSet::new();

        fn collect_fills(
            stmts: &[Stmt],
            guard: &str,
            mutated: &BTreeSet<String>,
            fills: &mut BTreeSet<String>,
        ) {
            for stmt in stmts {
                if let Stmt::IndexAssign {
                    obj,
                    key: Expr::Identifier(key_ident),
                    ..
                } = stmt
                    && key_ident == guard
                    && let Some(table_name) = get_base_identifier(obj)
                    && !mutated.contains(table_name)
                {
                    fills.insert(table_name.clone());
                }
                match stmt {
                    Stmt::While { body, .. } | Stmt::Do { body } => {
                        collect_fills(body, guard, mutated, fills)
                    }
                    Stmt::If {
                        then_body,
                        else_body,
                        ..
                    } => {
                        collect_fills(then_body, guard, mutated, fills);
                        collect_fills(else_body, guard, mutated, fills);
                    }
                    _ => {}
                }
            }
        }

        collect_fills(body, guard, &mutated, &mut fills);

        let depth = self.walk.scopes.len();
        for table_name in fills {
            let site_ids: BTreeSet<usize> = self
                .walk
                .scopes
                .iter()
                .rev()
                .filter_map(|s| s.get(&table_name))
                .flat_map(|ts| ts.aliases.iter().copied())
                .collect();

            for &site in &site_ids {
                if !is_root(&site) && !is_ghost(&site) {
                    signal!(rec.on(), trace::TRACE_FILL_LOOP_DENSE);
                    if self.layout.verdicts[site] == LayoutVerdict::Growing {
                        self.layout.verdicts[site] = LayoutVerdict::Dense;
                    }
                }
            }

            self.layout.name_dense.insert((table_name, depth), true);
        }
    }

    pub(super) fn collect_mutated_names(&self, rec: Gate, stmts: &[Stmt]) -> BTreeSet<String> {
        let mut mutated = BTreeSet::new();
        for s in stmts {
            match s {
                Stmt::Assignment { name, .. } => {
                    signal!(rec.on(), trace::TRACE_MUT_ASSIGN);
                    mutated.insert(name.clone());
                }
                Stmt::While { .. } => {}
                Stmt::Do { .. } => {}
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    signal!(rec.on(), trace::TRACE_MUT_IF);
                    for ss in then_body {
                        if let Stmt::Assignment { name, .. } = ss {
                            signal!(rec.on(), trace::TRACE_MUT_THEN_ASSIGN);
                            mutated.insert(name.clone());
                        }
                    }
                    for ss in else_body {
                        if let Stmt::Assignment { name, .. } = ss {
                            signal!(rec.on(), trace::TRACE_MUT_ELSE_ASSIGN);
                            mutated.insert(name.clone());
                        }
                    }
                }
                _ => {}
            }
        }
        mutated
    }
}
