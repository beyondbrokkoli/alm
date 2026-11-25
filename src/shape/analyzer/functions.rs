use super::*;
use crate::ast::Loc;

/// Names read by a creation site — rides the traversal engine. Two laws
/// carried over from the hand walker: a function literal's body is not
/// descended (its reads belong to the closure's own accounting), and a
/// direct-identifier callee is a call, not a read.
struct CreationReads {
    out: Vec<String>,
}

impl crate::visit::Visitor for CreationReads {
    type Break = std::convert::Infallible;

    fn visit_identifier(&mut self, name: &str, _id: NodeId) -> Result<(), Self::Break> {
        self.out.push(name.to_string());
        Ok(())
    }

    fn visit_call(&mut self, callee: &Expr, args: &[Expr], _id: NodeId) -> Result<(), Self::Break> {
        if !matches!(callee, Expr::Identifier { .. }) {
            crate::visit::walk_expr(self, callee)?;
        }
        for a in args {
            crate::visit::walk_expr(self, a)?;
        }
        Ok(())
    }

    fn visit_function(
        &mut self,
        _params: &[String],
        _body: &[Stmt],
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        Ok(())
    }
}

fn collect_creation_reads_stmt(stmt: &Stmt, out: &mut Vec<String>) {
    let mut v = CreationReads {
        out: std::mem::take(out),
    };
    let _ = crate::visit::walk_stmt(&mut v, stmt);
    *out = v.out;
}

/// Free names of a body, transitively — rides the traversal engine with
/// the bound-set as visitor state. If branches walk on independent clones
/// (a binding in one arm must not satisfy the other); a function literal
/// binds its params for its body only.
struct FreeNames {
    bound: BTreeSet<String>,
    out: BTreeSet<String>,
}

impl crate::visit::Visitor for FreeNames {
    type Break = std::convert::Infallible;

    fn visit_identifier(&mut self, name: &str, _id: NodeId) -> Result<(), Self::Break> {
        if !self.bound.contains(name) {
            self.out.insert(name.to_string());
        }
        Ok(())
    }

    fn visit_local_decl(
        &mut self,
        names: &[String],
        exprs: &[Expr],
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        for e in exprs {
            crate::visit::walk_expr(self, e)?;
        }
        for name in names {
            self.bound.insert(name.clone());
        }
        Ok(())
    }

    fn visit_assignment(
        &mut self,
        name: &str,
        expr: &Expr,
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        crate::visit::walk_expr(self, expr)?;
        if !self.bound.contains(name) {
            self.out.insert(name.to_string());
        }
        Ok(())
    }

    fn visit_if(
        &mut self,
        condition: &Expr,
        then_body: &[Stmt],
        else_body: &[Stmt],
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        crate::visit::walk_expr(self, condition)?;
        let entry = self.bound.clone();
        crate::visit::walk_stmts(self, then_body)?;
        self.bound = entry.clone();
        crate::visit::walk_stmts(self, else_body)?;
        self.bound = entry;
        Ok(())
    }

    fn visit_call(&mut self, callee: &Expr, args: &[Expr], _id: NodeId) -> Result<(), Self::Break> {
        if !matches!(callee, Expr::Identifier { .. }) {
            crate::visit::walk_expr(self, callee)?;
        }
        for a in args {
            crate::visit::walk_expr(self, a)?;
        }
        Ok(())
    }

    fn visit_function(
        &mut self,
        params: &[String],
        body: &[Stmt],
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        let saved = self.bound.clone();
        self.bound.extend(params.iter().cloned());
        let _ = crate::visit::walk_stmts(self, body);
        self.bound = saved;
        Ok(())
    }
}

fn transitive_free_names(stmts: &[Stmt], bound: &mut BTreeSet<String>) -> BTreeSet<String> {
    let mut v = FreeNames {
        bound: std::mem::take(bound),
        out: BTreeSet::new(),
    };
    let _ = crate::visit::walk_stmts(&mut v, stmts);
    *bound = v.bound;
    v.out
}

impl Analyzer {
    pub(super) fn resolve_fn(&self, name: &str) -> Option<NodeId> {
        self.walk.resolve_fn(name)
    }

    pub(super) fn walk_fn_def(
        &mut self,
        rec: Gate,
        fn_ptr: NodeId,
        params: &[String],
        body: &[Stmt],
        key: (NodeId, u8),
    ) -> Result<(), ShapeError> {
        self.fn_scope_keys.insert(fn_ptr, key);
        let mut chain: BTreeMap<String, Option<NodeId>> = BTreeMap::new();
        let mut chain_depth: BTreeMap<String, usize> = BTreeMap::new();
        for (depth, scope) in self.walk.scopes.iter().enumerate() {
            for (n, b) in scope {
                // Fn-bound depth-0 names stay OUT of the chain even
                // though depth 0 is in it: a fn NAME is a variable —
                // the judge re-points a closure when the top-level
                // binding rebinds to a new literal (fn_key_late_
                // binding: 1 then 2), and resolve_fn_binding's snap.fns
                // fallback must see the CURRENT binding for that.
                // Depth-0 VALUE bindings are the Finding B fix: the
                // boundary-root scope sits at the base of every scope
                // stack the lowerer ever lowers, so they are
                // capturable from any expansion site — the lexical
                // fix, not a global scope (the dialect still has
                // none).
                if depth == 0 && b.fn_ptr.is_some() {
                    continue;
                }
                chain.insert(n.clone(), b.fn_ptr);
                // The same inner-wins pass that picks the chain's
                // binding picks its walk-scope index: the capture's
                // binding identity is WHERE it was bound, not its
                // string. Depths ride to the lowerer beside the face
                // so a mint can tell two same-named captures apart
                // (Closure Finding A).
                chain_depth.insert(n.clone(), depth);
            }
        }
        self.fn_def_sites.insert(fn_ptr, chain.clone());
        let mut bound = BTreeSet::new();
        bound.extend(params.iter().cloned());
        let free = transitive_free_names(body, &mut bound);
        // A capture is a free name whose chain entry is a plain value
        // binding (`Some(&None)`); fn-bound names (Some(&Some(ptr)))
        // resolve through resolve_fn_binding's definition-site chain +
        // snap.fns and never ride the caller's frames (t8). With depth
        // 0 in the chain, top-level bindings are captured like any
        // other — Finding B's dynamic tier is gone. Boundary, named:
        // a top-level binding declared AFTER this fn literal is not in
        // scopes[0] at the recorded pass either, so it is neither
        // capture nor fact — the forward-referenced tier still
        // resolves dynamically at expansion time (Finding B's
        // sibling).
        let captures: BTreeSet<String> = free
            .into_iter()
            .filter(|n| chain.get(n) == Some(&None))
            .collect();
        let capture_depths: BTreeMap<String, usize> = captures
            .iter()
            .map(|n| {
                (
                    n.clone(),
                    *chain_depth.get(n).expect(
                        "a capture has no recorded walk-scope depth — \
                         captures filter the chain itself, so every \
                         capture's name carries a depth",
                    ),
                )
            })
            .collect();
        self.fn_captures.insert(fn_ptr, captures);
        self.fn_capture_depths.insert(fn_ptr, capture_depths);
        // The body scope `with_scope` is about to push lands at this
        // walk-stack index — the fn's body-scope walk depth. The
        // lowerer keys declare-site box minting off it.
        self.fn_body_depths.insert(fn_ptr, self.walk.scopes.len());
        self.lattice.unknowns.ensure_fn_ret(fn_ptr);
        collect_body_sites(body, &self.lattice.sites, &mut self.fn_body_sites);
        self.fn_params.insert(fn_ptr, params.to_vec());
        let stored: BTreeSet<String> = collect_stored_bases(body)
            .into_iter()
            .filter(|n| params.contains(n))
            .collect();
        self.fn_store_params.insert(fn_ptr, stored);
        self.fn_rets.push(None);
        self.fn_edge_frames.push(Vec::new());
        self.fn_ret_reaches.push(BTreeSet::new());
        self.fn_walk.push((fn_ptr, params.to_vec()));
        self.fn_scope_entries.push(self.walk.scopes.len());
        let mut result = Ok(());
        self.with_scope(|an| {
            let scope = an.walk.scopes.last_mut().unwrap();
            for p in params {
                // A parameter is a fresh binding whose value is the
                // caller's argument: record it as the unknowable shape
                // so an outer same-named literal cannot lend its
                // nonneg/lower-bound facts to a loop over the
                // parameter — the entry facts would describe the
                // caller's argument, not the literal (the F3 probe).
                // One binding carries the whole face set: shape
                // Pending, and no fn/node/prov face (the fn_scopes
                // None-insert rides inside the Binding now).
                an.holds.num_assigns.insert(p.clone(), vec![NumExpr::Other]);
                scope.insert(
                    p.clone(),
                    Binding::new(TableShape {
                        ty: Pending,
                        layout: LayoutVerdict::default(),
                        aliases: BTreeSet::new(),
                        lineage: BTreeMap::new(),
                    }),
                );
            }
            an.walk_stmts(rec, body);
            if let Err(err) = an.decide_scope_exit(rec, key) {
                result = Err(err);
            }
        });
        self.fn_scope_entries.pop();
        self.fn_walk.pop();
        let joined = self.fn_rets.pop().unwrap_or(None);
        let edges = self.fn_edge_frames.pop().unwrap_or_default();
        let joined_reach = self.fn_ret_reaches.pop().unwrap_or_default();
        if joined.is_some() {
            self.fn_ret_reach.insert(fn_ptr, joined_reach);
        }
        if !edges.is_empty() {
            self.fn_ret_edge_shapes.insert(fn_ptr, edges);
        }
        if let Some(shape) = joined {
            self.fn_ret_shapes.insert(fn_ptr, shape);
        }
        result
    }

    pub(super) fn sever_creation_captures(&mut self, rec: Gate, stmt: &Stmt) {
        let mut readers = Vec::new();
        collect_creation_reads_stmt(stmt, &mut readers);
        if readers.is_empty() {
            return;
        }
        let mut severed: Vec<(usize, String)> = Vec::new();
        for name in readers {
            let Some(ptr) = self.resolve_fn(&name) else {
                continue;
            };
            let Some(caps) = self.fn_captures.get(&ptr).cloned() else {
                continue;
            };
            for cap in caps {
                if let Ok((d, bind)) = self.resolve(&cap)
                    && matches!(bind.ty, Tbl(_))
                    && !severed.iter().any(|(_, n)| n == &cap)
                {
                    severed.push((d, cap));
                }
            }
        }
        if severed.is_empty() {
            return;
        }
        for (d, cap) in &severed {
            self.poison_moved(*d, cap);
        }
        if rec.on() {
            let entry = self.own.move_poisons.entry(stmt.id()).or_default();
            for (_, cap) in &severed {
                entry.insert(cap.clone());
            }
        }
    }

    pub(super) fn return_reaches_param(&self, expr: &Expr, params: &[String]) -> BTreeSet<usize> {
        match expr {
            Expr::Identifier { name: n, .. } => {
                params.iter().position(|p| p == n).into_iter().collect()
            }
            Expr::Call { callee, args, .. } => match callee.as_ref() {
                Expr::Identifier { name, .. } => {
                    let Some(fn_ptr) = self.resolve_fn(name) else {
                        return BTreeSet::new();
                    };
                    let Some(ret) = self.fn_ret_params.get(&fn_ptr) else {
                        return BTreeSet::new();
                    };
                    let mut out = BTreeSet::new();
                    for &j in ret {
                        if let Some(arg) = args.get(j) {
                            out.extend(self.return_reaches_param(arg, params));
                        }
                    }
                    out
                }
                // C: only a direct-name callee resolves — every other
                // callee shape has no param reach to trace
                _ => BTreeSet::new(),
            },
            // C: only identifiers and calls carry a param's value out
            _ => BTreeSet::new(),
        }
    }

    pub(super) fn record_moved_param(&mut self, name: &str) {
        if let Some((fn_ptr, params)) = self.fn_walk.last()
            && params.iter().any(|p| p == name)
        {
            self.fn_moved_params
                .entry(*fn_ptr)
                .or_default()
                .insert(name.to_string());
        }
    }

    pub(super) fn check_boundary_pin(
        &self,
        bind: &TableShape,
        src: &str,
    ) -> Result<(), ShapeError> {
        if bind.aliases.contains(&BOUNDARY_ROOT) {
            return Err(ShapeError(Diagnostic::lifetime(format!(
                "the boundary table '{src}' is pinned — the host owns \
                 its header; read its cells ('{src}[i]') instead of moving the table"
            ))));
        }
        Ok(())
    }

    pub(super) fn ret_reach_sites(&self, e: &Expr, out: &mut BTreeSet<usize>) {
        match e {
            Expr::Identifier { name: n, .. } => {
                if let Ok((_, bind)) = self.resolve(n) {
                    out.extend(bind.aliases.iter().copied().filter(|s| !is_root(s)));
                    out.extend(bind.lineage.keys().copied().filter(|s| !is_root(s)));
                }
            }
            Expr::Index { obj, .. } => self.ret_reach_sites(obj, out),
            Expr::Call { callee, args, .. } => {
                if let Expr::Identifier { name, .. } = callee.as_ref()
                    && let Some(fn_ptr) = self.resolve_fn(name)
                {
                    if let Some(reach) = self.fn_ret_reach.get(&fn_ptr) {
                        out.extend(reach.iter().copied());
                    }
                    if let Some(rets) = self.fn_ret_params.get(&fn_ptr) {
                        for &i in rets {
                            if let Some(a) = args.get(i) {
                                self.ret_reach_sites(a, out);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // (L6 receipt: `ret_base_temp_sites` — the keep-temp site collector
    // the return-exit planner reads — ports with exits.rs.)
}
