use super::*;
#[derive(Clone, Copy, PartialEq)]
pub(super) enum Fate {
    Dies,
    Escapes,
}

impl Analyzer {
    pub(super) fn scope_exit_frees(
        &mut self,
        _rec: Gate,
        depth: usize,
        key: (NodeId, u8),
    ) -> Result<
        (
            Vec<super::facts::DoExitFree>,
            Vec<super::facts::ArmFreeEntry>,
        ),
        ShapeError,
    > {
        let (frees, arms) = self.compute_scope_frees(depth, true)?;
        let _ = key;
        Ok((frees, arms))
    }

    /// [ownership] The scope-death plan: a dying binding's roots split
    /// into sites and ghosts (a mixed shape by `plan_mixed`), freed
    /// unless a housed origin defers or another free covers them.
    pub(super) fn compute_scope_frees(
        &mut self,
        depth: usize,
        split: bool,
    ) -> Result<
        (
            Vec<super::facts::DoExitFree>,
            Vec<super::facts::ArmFreeEntry>,
        ),
        ShapeError,
    > {
        let dying = self.walk.scopes[depth].clone();
        let mut arm_frees: Vec<super::facts::ArmFreeEntry> = Vec::new();

        struct Batch {
            name: String,
            sites: Vec<usize>,
            ghosts: Vec<usize>,
            housed: bool,
        }
        let mut batch: Vec<Batch> = Vec::new();
        let mut fired_keeps: Vec<(String, Vec<String>)> = Vec::new();
        for (name, bind) in &dying {
            let shape = &bind.shape;
            let roots: Vec<usize> = shape
                .aliases
                .iter()
                .copied()
                .filter(|site| !is_root(site))
                .collect();
            if roots.is_empty() {
                continue;
            }
            if value_kind(&shape.ty) {
                continue;
            }
            let ghosts: Vec<usize> = roots.iter().copied().filter(is_ghost).collect();
            let sites: Vec<usize> = roots.iter().copied().filter(|s| !is_ghost(s)).collect();
            if split && !ghosts.is_empty() && !sites.is_empty() {
                match self.plan_mixed(name, depth, shape) {
                    MixedPlan::NotMixed => {}
                    MixedPlan::Suppress => {
                        batch.push(Batch {
                            name: name.clone(),
                            sites,
                            ghosts,
                            housed: true,
                        });
                        continue;
                    }
                    MixedPlan::Fire { keeps } => {
                        batch.push(Batch {
                            name: name.clone(),
                            sites,
                            ghosts,
                            housed: false,
                        });
                        fired_keeps.push((name.clone(), keeps));
                        continue;
                    }
                    MixedPlan::ArmSplit {
                        tag,
                        nothing_on,
                        keeps,
                    } => {
                        arm_frees.push(super::facts::ArmFreeEntry {
                            carrier: name.clone(),
                            tag,
                            nothing_on,
                            keeps: keeps.into_iter().map(super::facts::Keep::Name).collect(),
                        });
                        batch.push(Batch {
                            name: name.clone(),
                            sites,
                            ghosts,
                            housed: true,
                        });
                        continue;
                    }
                }
            }
            let housed = !ghosts.is_empty()
                && shape.lineage.keys().any(|o| {
                    origin_housed(
                        &self.walk.scopes[..depth],
                        &self.lattice,
                        &self.own,
                        &self.reads,
                        *o,
                        depth,
                        name,
                    )
                });
            batch.push(Batch {
                name: name.clone(),
                sites,
                ghosts,
                housed,
            });
        }

        let covered: BTreeSet<usize> = batch
            .iter()
            .filter(|b| !b.housed)
            .flat_map(|b| b.sites.iter().copied())
            .flat_map(|site| release_set(&self.lattice, &self.own, &self.reads, site))
            .collect();
        let covered_flags: Vec<bool> = batch
            .iter()
            .map(|b| {
                b.housed
                    || b.ghosts.iter().any(|_g| {
                        let shape = &dying[&b.name].shape;
                        shape.lineage.keys().any(|o| {
                            !shape.aliases.contains(o)
                                && ghost_origin_covered(&self.lattice, &covered, *o)
                        })
                    })
            })
            .collect();

        let mut frees: Vec<super::facts::DoExitFree> = Vec::new();
        for (i, b) in batch.iter().enumerate() {
            if covered_flags[i] {
                continue;
            }
            let forced: Option<Vec<String>> = fired_keeps
                .iter()
                .find(|(n, _)| n == &b.name)
                .map(|(_, k)| k.clone());
            for site in &b.sites {
                let (spare, _) = self.housed_in_release(*site);
                let harm = self.harm_set(*site);
                let mut keeps: Vec<super::facts::Keep> = match &forced {
                    Some(k) => k
                        .iter()
                        .map(|n| super::facts::Keep::Name(n.clone()))
                        .collect(),
                    None => borrowers_of(&self.walk.scopes, &harm, depth, depth, &b.name)
                        .into_iter()
                        .map(super::facts::Keep::Name)
                        .collect(),
                };
                if !spare.is_empty() {
                    keeps.extend(spare.iter().map(|&g| super::facts::Keep::Ghost(g)));
                }
                // [ownership] the claim: the release houses these row
                // ghosts unless a keep spares them.
                self.mark_claimed(*site, &keeps);
                frees.push(super::facts::DoExitFree {
                    site: *site,
                    carrier: b.name.clone(),
                    keeps,
                });
            }
            for ghost in &b.ghosts {
                let harm = self.harm_set(*ghost);
                let keeps: Vec<super::facts::Keep> = match &forced {
                    Some(k) => k
                        .iter()
                        .map(|n| super::facts::Keep::Name(n.clone()))
                        .collect(),
                    None => borrowers_of(
                        &self.walk.scopes,
                        &harm,
                        self.walk.scopes.len(),
                        depth,
                        &b.name,
                    )
                    .into_iter()
                    .map(super::facts::Keep::Name)
                    .collect(),
                };
                frees.push(super::facts::DoExitFree {
                    site: *ghost,
                    carrier: b.name.clone(),
                    keeps,
                });
            }
        }
        Ok((frees, arm_frees))
    }

    pub(super) fn decide_scope_exit(
        &mut self,
        rec: Gate,
        key: (NodeId, u8),
    ) -> Result<(), ShapeError> {
        if !rec.on() {
            return Ok(());
        }

        let depth = self.walk.scopes.len() - 1;
        let (frees, arms) = self.scope_exit_frees(rec, depth, key)?;
        // [ownership] the do-exit mint: a scope's exit frees, keyed by
        // the scope that died — the key lands even when empty.
        self.own.do_exit_frees.insert(key, frees);
        if !arms.is_empty() {
            // [ownership] the arm-split mint: a mixed binding whose
            // arms release differently frees on the join's tag.
            self.own.arm_do_exit_frees.insert(key, arms);
        }
        Ok(())
    }

    pub(super) fn decide_root_exit(&mut self, rec: Gate) -> Result<(), ShapeError> {
        if !rec.on() {
            return Ok(());
        }

        let (frees, arms) = self.scope_exit_frees(rec, 0, (NodeId(u32::MAX), 0))?;
        // [ownership] the root drain: the host chunk's own exit frees,
        // plain and arm-split.
        self.own.root_exit_frees = frees;
        self.own.arm_root_exit_frees = arms;
        Ok(())
    }

    pub(super) fn prune_deepfree_children(&self, sites: &mut Vec<usize>) {
        let mut children: BTreeSet<usize> = BTreeSet::new();
        for &site in sites.iter() {
            children.extend(deepfree_children(
                &self.lattice,
                &self.own,
                &self.reads,
                site,
            ));
        }
        sites.retain(|s| !children.contains(s));
    }

    pub(super) fn plan_stmt_temp_frees(&mut self, stmts: &[Stmt]) {
        for s in stmts {
            let mut sites = Vec::new();
            match s {
                Stmt::Print { exprs, .. } => {
                    for e in exprs {
                        self.collect_temp_sites(e, Fate::Dies, &mut sites);
                    }
                }
                Stmt::Expr { expr, .. } => {
                    self.collect_temp_sites(expr, Fate::Dies, &mut sites);
                }
                Stmt::LocalDecl { exprs, .. } => {
                    for e in exprs {
                        self.collect_temp_sites(e, Fate::Escapes, &mut sites);
                    }
                }
                Stmt::Assignment { expr, .. } => {
                    self.collect_temp_sites(expr, Fate::Escapes, &mut sites);
                }
                Stmt::IndexAssign {
                    obj, key, value, ..
                } => {
                    self.collect_temp_sites(obj, Fate::Dies, &mut sites);
                    self.collect_temp_sites(key, Fate::Dies, &mut sites);
                    self.collect_temp_sites(value, Fate::Escapes, &mut sites);
                }
                Stmt::Return { .. } => {}
                Stmt::Break { .. } => {}
                Stmt::While {
                    condition, body, ..
                } => {
                    self.plan_cond_temp_frees(condition, s);
                    self.plan_stmt_temp_frees(body);
                }
                Stmt::Do { body, .. } => self.plan_stmt_temp_frees(body),
                Stmt::If {
                    condition,
                    then_body,
                    else_body,
                    ..
                } => {
                    self.plan_cond_temp_frees(condition, s);
                    self.plan_stmt_temp_frees(then_body);
                    self.plan_stmt_temp_frees(else_body);
                }
            }
            if !sites.is_empty() {
                self.prune_deepfree_children(&mut sites);
                if !sites.is_empty() {
                    // [ownership] the stmt-temp mint: a ctor born in the
                    // statement and only read through dies where its
                    // value does — one entry per statement.
                    self.own.stmt_temp_frees.insert(s.id(), sites);
                }
            }
            self.plan_fn_bodies_in_stmt(s);
            self.plan_arm_temp_frees_in_stmt(s);
        }
    }

    pub(super) fn plan_cond_temp_frees(&mut self, cond: &Expr, stmt: &Stmt) {
        let mut sites = Vec::new();
        self.collect_temp_sites(cond, Fate::Dies, &mut sites);
        self.prune_deepfree_children(&mut sites);
        if !sites.is_empty() {
            // [ownership] the cond-temp mint: a condition's temps free
            // at the branch — keyed by the If / While statement.
            self.own.cond_temp_frees.insert(stmt.id(), sites);
        }
    }

    pub(super) fn plan_arm_temp_frees_in_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
                for e in exprs {
                    self.plan_arm_temp_frees_in_expr(e);
                }
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr, .. } => {
                self.plan_arm_temp_frees_in_expr(expr)
            }
            Stmt::IndexAssign {
                obj, key, value, ..
            } => {
                self.plan_arm_temp_frees_in_expr(obj);
                self.plan_arm_temp_frees_in_expr(key);
                self.plan_arm_temp_frees_in_expr(value);
            }
            Stmt::While {
                condition, body, ..
            } => {
                self.plan_arm_temp_frees_in_expr(condition);
                for s in body {
                    self.plan_arm_temp_frees_in_stmt(s);
                }
            }
            Stmt::Do { body, .. } => {
                for s in body {
                    self.plan_arm_temp_frees_in_stmt(s);
                }
            }
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                self.plan_arm_temp_frees_in_expr(condition);
                for s in then_body.iter().chain(else_body) {
                    self.plan_arm_temp_frees_in_stmt(s);
                }
            }
            Stmt::Return { value, .. } => {
                if let Some(e) = value {
                    self.plan_arm_temp_frees_in_expr(e);
                }
            }
            Stmt::Break { .. } => {}
        }
    }

    pub(super) fn plan_arm_temp_frees_in_expr(&mut self, e: &Expr) {
        match e {
            Expr::BinaryOp {
                op: BinOp::And | BinOp::Or,
                left,
                right,
                ..
            } => {
                for operand in [left.as_ref(), right.as_ref()] {
                    let mut sites = Vec::new();
                    self.collect_temp_sites(operand, Fate::Dies, &mut sites);
                    self.prune_deepfree_children(&mut sites);
                    if !sites.is_empty() {
                        // [ownership] the arm-temp mint: an and/or
                        // operand owns its temps — keyed by the operand
                        // expression, nested operands their own entries.
                        self.own.arm_temp_frees.insert(operand.id(), sites);
                    }
                }
                self.plan_arm_temp_frees_in_expr(left);
                self.plan_arm_temp_frees_in_expr(right);
            }
            Expr::TableCtor { entries, .. } => {
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        self.plan_arm_temp_frees_in_expr(ke);
                    }
                    self.plan_arm_temp_frees_in_expr(v);
                }
            }
            Expr::Index { obj, key, .. } => {
                self.plan_arm_temp_frees_in_expr(obj);
                self.plan_arm_temp_frees_in_expr(key);
            }
            Expr::BinaryOp { left, right, .. } => {
                self.plan_arm_temp_frees_in_expr(left);
                self.plan_arm_temp_frees_in_expr(right);
            }
            Expr::UnaryOp { expr, .. } => self.plan_arm_temp_frees_in_expr(expr),
            Expr::Call { callee, args, .. } => {
                self.plan_arm_temp_frees_in_expr(callee);
                for a in args {
                    self.plan_arm_temp_frees_in_expr(a);
                }
            }
            // NOTE historical shape: a Field's obj is not arm-scanned
            // (kept bit-for-bit for the goldens); function literals own
            // their arm frees, and the leaves/sys faces carry none
            Expr::Field { .. }
            | Expr::Function { .. }
            | Expr::Integer { .. }
            | Expr::Float { .. }
            | Expr::Boolean { .. }
            | Expr::String { .. }
            | Expr::Nil { .. }
            | Expr::Identifier { .. }
            | Expr::SysAllocCount { .. }
            | Expr::SysExecCount { .. }
            | Expr::FfiModule { .. }
            | Expr::AsyncModule { .. } => {}
        }
    }

    pub(super) fn collect_temp_sites(&self, e: &Expr, fate: Fate, out: &mut Vec<usize>) {
        match e {
            Expr::TableCtor { entries, .. } => {
                if fate == Fate::Dies
                    && let Some(&site) = self.lattice.sites.get(&e.id())
                {
                    out.push(site);
                }
                for (_, v) in entries {
                    self.collect_temp_sites(v, fate, out);
                }
            }
            Expr::Call { callee, args, .. } => {
                if let Expr::Identifier { name, .. } = callee.as_ref()
                    && let Some(fn_ptr) = self.resolve_fn(name)
                {
                    if fate == Fate::Dies
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
                    let empty = BTreeSet::new();
                    let empty_idx = BTreeSet::new();
                    let moved = self.fn_moved_params.get(&fn_ptr).unwrap_or(&empty);
                    let rets = self.fn_ret_params.get(&fn_ptr).unwrap_or(&empty_idx);
                    let params = self.fn_params.get(&fn_ptr).cloned().unwrap_or_default();
                    for (i, a) in args.iter().enumerate() {
                        let is_moved = params.get(i).is_some_and(|p| moved.contains(p));
                        let is_ret = rets.contains(&i);
                        let arg_fate = if is_moved {
                            Fate::Escapes
                        } else if is_ret {
                            if fate == Fate::Dies && !matches!(a, Expr::Identifier { .. }) {
                                Fate::Dies
                            } else {
                                Fate::Escapes
                            }
                        } else {
                            Fate::Dies
                        };
                        self.collect_temp_sites(a, arg_fate, out);
                    }
                } else if let Expr::Field { .. } = callee.as_ref() {
                    for a in args {
                        self.collect_temp_sites(a, Fate::Dies, out);
                    }
                }
            }
            Expr::Index { obj, key, .. } => {
                self.collect_temp_sites(obj, Fate::Dies, out);
                self.collect_temp_sites(key, Fate::Dies, out);
            }
            Expr::BinaryOp {
                op: BinOp::And | BinOp::Or,
                ..
            } => {}
            Expr::BinaryOp { left, right, .. } => {
                self.collect_temp_sites(left, Fate::Dies, out);
                self.collect_temp_sites(right, Fate::Dies, out);
            }
            Expr::UnaryOp { expr, .. } => self.collect_temp_sites(expr, Fate::Dies, out),
            Expr::Function { .. } => {}
            Expr::FfiModule { .. } => {}
            Expr::AsyncModule { .. } => {}
            Expr::Field { obj, .. } => {
                self.collect_temp_sites(obj, Fate::Dies, out);
            }
            Expr::Integer { .. }
            | Expr::Float { .. }
            | Expr::Boolean { .. }
            | Expr::String { .. }
            | Expr::Nil { .. }
            | Expr::Identifier { .. }
            | Expr::SysAllocCount { .. }
            | Expr::SysExecCount { .. } => {}
        }
    }

    pub(super) fn plan_fn_bodies_in_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
                for e in exprs {
                    self.plan_fn_bodies_in_expr(e);
                }
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr, .. } => {
                self.plan_fn_bodies_in_expr(expr)
            }
            Stmt::IndexAssign {
                obj, key, value, ..
            } => {
                self.plan_fn_bodies_in_expr(obj);
                self.plan_fn_bodies_in_expr(key);
                self.plan_fn_bodies_in_expr(value);
            }
            Stmt::While { condition, .. } => self.plan_fn_bodies_in_expr(condition),
            Stmt::If { condition, .. } => self.plan_fn_bodies_in_expr(condition),
            Stmt::Do { .. } => {}
            Stmt::Return { value, .. } => {
                if let Some(e) = value {
                    self.plan_fn_bodies_in_expr(e);
                }
            }
            Stmt::Break { .. } => {}
        }
    }

    pub(super) fn plan_fn_bodies_in_expr(&mut self, e: &Expr) {
        match e {
            Expr::Function { body, .. } => self.plan_stmt_temp_frees(body),
            Expr::TableCtor { entries, .. } => {
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        self.plan_fn_bodies_in_expr(ke);
                    }
                    self.plan_fn_bodies_in_expr(v);
                }
            }
            Expr::Index { obj, key, .. } => {
                self.plan_fn_bodies_in_expr(obj);
                self.plan_fn_bodies_in_expr(key);
            }
            Expr::BinaryOp { left, right, .. } => {
                self.plan_fn_bodies_in_expr(left);
                self.plan_fn_bodies_in_expr(right);
            }
            Expr::UnaryOp { expr, .. } => self.plan_fn_bodies_in_expr(expr),
            Expr::Call { callee, args, .. } => {
                self.plan_fn_bodies_in_expr(callee);
                for a in args {
                    self.plan_fn_bodies_in_expr(a);
                }
            }
            // NOTE historical shape: a Field's obj hides no fn body scan
            // (kept bit-for-bit for the goldens); the leaves/sys faces
            // carry no bodies to plan
            Expr::Field { .. }
            | Expr::Integer { .. }
            | Expr::Float { .. }
            | Expr::Boolean { .. }
            | Expr::String { .. }
            | Expr::Nil { .. }
            | Expr::Identifier { .. }
            | Expr::SysAllocCount { .. }
            | Expr::SysExecCount { .. }
            | Expr::FfiModule { .. }
            | Expr::AsyncModule { .. } => {}
        }
    }
}
