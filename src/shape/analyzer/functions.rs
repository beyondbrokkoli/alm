use super::*;
impl Analyzer {
    pub(super) fn resolve_fn(&self, name: &str) -> Option<*const Expr> {
        for scope in self.walk.fn_scopes.iter().rev() {
            if let Some(entry) = scope.get(name) {
                return *entry;
            }
        }
        None
    }

    pub(super) fn declare_fn_binding(&mut self, name: &str, ptr: Option<*const Expr>) {
        self.walk
            .fn_scopes
            .last_mut()
            .unwrap()
            .insert(name.to_string(), ptr);
    }

    pub(super) fn assign_fn_binding(&mut self, name: &str, ptr: Option<*const Expr>) {
        let depth = self
            .walk
            .fn_scopes
            .iter()
            .rposition(|s| s.contains_key(name))
            .unwrap_or(self.walk.fn_scopes.len() - 1);
        self.walk.fn_scopes[depth].insert(name.to_string(), ptr);
    }

    pub(super) fn walk_fn_def(
        &mut self,
        rec: Gate,
        fn_ptr: *const Expr,
        params: &[String],
        body: &[Stmt],
        key: (*const Stmt, u8),
    ) -> Result<(), ShapeError> {
        self.fn_scope_keys.insert(fn_ptr, key);
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
                scope.insert(
                    p.clone(),
                    TableShape {
                        ty: Pending,
                        layout: LayoutVerdict::default(),
                        aliases: BTreeSet::new(),
                        lineage: BTreeMap::new(),
                    },
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

    pub(super) fn return_reaches_param(&self, expr: &Expr, params: &[String]) -> BTreeSet<usize> {
        match expr {
            Expr::Identifier(n) => params.iter().position(|p| p == n).into_iter().collect(),
            Expr::Call { callee, args } => match callee.as_ref() {
                Expr::Identifier(name) => {
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
                _ => BTreeSet::new(),
            },
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
            return Err(ShapeError(format!(
                "Lifetime Error: the boundary table '{src}' is pinned — the host owns \
                 its header; read its cells ('{src}[i]') instead of moving the table"
            )));
        }
        Ok(())
    }

    pub(super) fn ret_reach_sites(&self, e: &Expr, out: &mut BTreeSet<usize>) {
        match e {
            Expr::Identifier(n) => {
                if let Ok((_, bind)) = self.resolve(None, n) {
                    out.extend(bind.aliases.iter().copied().filter(|s| !is_root(s)));
                    out.extend(bind.lineage.keys().copied().filter(|s| !is_root(s)));
                }
            }
            Expr::Index { obj, .. } => self.ret_reach_sites(obj, out),
            Expr::Call { callee, args } => {
                if let Expr::Identifier(name) = callee.as_ref()
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

    pub(super) fn ret_base_temp_sites(&self, e: &Expr, out: &mut Vec<usize>) {
        if let Expr::Index { obj, .. } = e {
            match obj.as_ref() {
                Expr::TableCtor(_) => {
                    if let Some(&site) = self.lattice.sites.get(&(obj.as_ref() as *const Expr)) {
                        out.push(site);
                    }
                }
                Expr::Call { callee, .. } => {
                    if let Expr::Identifier(name) = callee.as_ref()
                        && let Some(fn_ptr) = self.resolve_fn(name)
                        && let Some(shape) = self.fn_ret_shapes.get(&fn_ptr)
                    {
                        out.extend(
                            shape
                                .aliases
                                .iter()
                                .copied()
                                .filter(|s| !is_root(s) && !is_ghost(s)),
                        );
                    }
                }
                _ => {}
            }
            self.ret_base_temp_sites(obj, out);
        }
    }
}
