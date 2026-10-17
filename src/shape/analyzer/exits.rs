use super::*;
#[derive(Clone, Copy, PartialEq)]
pub(super) enum Fate {
    Dies,
    Escapes,
}

impl Analyzer {
    pub(super) fn scope_exit_frees(
        &mut self,
        rec: Gate,
        depth: usize,
        key: (*const Stmt, u8),
    ) -> Result<
        (
            Vec<super::facts::DoExitFree>,
            Vec<super::facts::ArmFreeEntry>,
        ),
        ShapeError,
    > {
        let (frees, arms) = match self.compute_scope_frees(depth, true) {
            Ok(v) => v,
            Err(err) => {
                signal!(rec.on(), trace::TRACE_DO_EXIT_ALIAS_SURVIVES);
                return Err(err);
            }
        };
        for _ in &frees {
            signal!(rec.on(), trace::TRACE_DO_EXIT_FREE_SITE);
        }
        let _ = key;
        Ok((frees, arms))
    }

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
        for (name, shape) in &dying {
            let roots: Vec<usize> = shape
                .aliases
                .iter()
                .copied()
                .filter(|site| !is_root(site))
                .collect();
            if roots.is_empty() {
                continue;
            }
            let ghosts: Vec<usize> = roots.iter().copied().filter(is_ghost).collect();
            let sites: Vec<usize> = roots.iter().copied().filter(|s| !is_ghost(s)).collect();
            if split && !ghosts.is_empty() && !sites.is_empty() {
                match self.plan_mixed(name, depth, shape) {
                    MixedPlan::NotMixed => {}
                    MixedPlan::Suppress => {
                        signal!(true, trace::TRACE_ROW_GHOST_DEFER);
                        batch.push(Batch {
                            name: name.clone(),
                            sites,
                            ghosts,
                            housed: true,
                        });
                        continue;
                    }
                    MixedPlan::Fire { keeps } => {
                        signal!(true, trace::TRACE_ROW_GHOST_FIRE);
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
                        signal!(true, trace::TRACE_JOIN_ARM_SPLIT);
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
            if housed {
                signal!(true, trace::TRACE_ROW_GHOST_DEFER);
            }
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
                        let shape = &dying[&b.name];
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
                if !b.housed {
                    signal!(true, trace::TRACE_ROW_GHOST_DEFER);
                }
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
                    signal!(true, trace::TRACE_ROW_GHOST_KEEP);
                    keeps.extend(spare.iter().map(|&g| super::facts::Keep::Ghost(g)));
                }
                if keeps
                    .iter()
                    .any(|k| !matches!(k, super::facts::Keep::Ghost(_)))
                {
                    signal!(true, trace::TRACE_ROW_KEEP_FREE);
                }
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
                if !keeps.is_empty() {
                    signal!(true, trace::TRACE_ROW_KEEP_FREE);
                } else {
                    signal!(true, trace::TRACE_ROW_GHOST_FIRE);
                }
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
        key: (*const Stmt, u8),
    ) -> Result<(), ShapeError> {
        if !rec.on() {
            return Ok(());
        }

        let depth = self.walk.scopes.len() - 1;
        let (frees, arms) = self.scope_exit_frees(rec, depth, key)?;
        self.own.do_exit_frees.insert(key, frees);
        if !arms.is_empty() {
            self.own.arm_do_exit_frees.insert(key, arms);
        }
        Ok(())
    }

    pub(super) fn plan_return_exits(
        &mut self,
        value: Option<(&Expr, &Ty)>,
        reach: &BTreeSet<usize>,
        stmt: *const Stmt,
    ) {
        let entry = self.fn_scope_entries.last().copied().unwrap_or(0);
        let boundary = self.fn_scope_entries.is_empty();
        let mut plain: Vec<super::facts::DoExitFree> = Vec::new();
        let mut keeps: Vec<super::facts::DoExitFree> = Vec::new();
        for depth in (entry..self.walk.scopes.len()).rev() {
            if let Ok((frees, _)) = self.compute_scope_frees(depth, false) {
                for mut f in frees {
                    if boundary {
                        f.keeps.clear();
                    }
                    if reach.contains(&f.site) {
                        keeps.push(f);
                    } else {
                        plain.push(f);
                    }
                }
            }
        }
        plain.sort_by_key(|f| (f.site, f.carrier.clone()));
        plain.dedup_by_key(|f| (f.site, f.carrier.clone()));
        if !plain.is_empty() {
            for _ in &plain {
                signal!(true, trace::TRACE_RET_PATH_FREE_SITE);
            }
            self.own.ret_path_frees.insert(stmt, plain);
        }
        keeps.sort_by_key(|f| (f.site, f.carrier.clone()));
        keeps.dedup_by_key(|f| (f.site, f.carrier.clone()));
        if !keeps.is_empty() {
            for _ in &keeps {
                signal!(true, trace::TRACE_RET_KEEP_FREE_SITE);
            }
            self.own.ret_path_keep_frees.insert(stmt, keeps);
        }
        if let Some((v, ty)) = value
            && matches!(ty, Tbl(_) | Pending)
        {
            let mut keep_temps = Vec::new();
            self.ret_base_temp_sites(v, &mut keep_temps);
            keep_temps.sort_unstable();
            keep_temps.dedup();
            self.prune_deepfree_children(&mut keep_temps);
            if !keep_temps.is_empty() {
                signal!(true, trace::TRACE_RET_KEEP_FREE_SITE);
                self.own.ret_path_keep_temps.insert(stmt, keep_temps);
            }
        }
        if let Some((v, ty)) = value
            && !matches!(ty, Tbl(_) | Pending)
        {
            let mut sites = Vec::new();
            self.collect_temp_sites(v, Fate::Escapes, &mut sites);
            self.prune_deepfree_children(&mut sites);
            if !sites.is_empty() {
                signal!(true, trace::TRACE_STMT_TEMP_FREE_SITE);
                self.own.stmt_temp_frees.insert(stmt, sites);
            }
        }
    }

    pub(super) fn decide_root_exit(&mut self, rec: Gate) -> Result<(), ShapeError> {
        if !rec.on() {
            return Ok(());
        }

        let (frees, arms) = self.scope_exit_frees(rec, 0, (std::ptr::null_mut(), 0))?;
        for _ in &frees {
            signal!(rec.on(), trace::TRACE_ROOT_EXIT_FREE_SITE);
        }
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
                Stmt::Print { exprs } => {
                    for e in exprs {
                        self.collect_temp_sites(e, Fate::Dies, &mut sites);
                    }
                }
                Stmt::Expr { expr } => {
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
                Stmt::IndexAssign { obj, key, value } => {
                    self.collect_temp_sites(obj, Fate::Dies, &mut sites);
                    self.collect_temp_sites(key, Fate::Dies, &mut sites);
                    self.collect_temp_sites(value, Fate::Escapes, &mut sites);
                }
                Stmt::Return { .. } => {}
                Stmt::While { condition, body } => {
                    self.plan_cond_temp_frees(condition, s);
                    self.plan_stmt_temp_frees(body);
                }
                Stmt::Do { body } => self.plan_stmt_temp_frees(body),
                Stmt::If {
                    condition,
                    then_body,
                    else_body,
                } => {
                    self.plan_cond_temp_frees(condition, s);
                    self.plan_stmt_temp_frees(then_body);
                    self.plan_stmt_temp_frees(else_body);
                }
            }
            if !sites.is_empty() {
                self.prune_deepfree_children(&mut sites);
                if !sites.is_empty() {
                    signal!(true, trace::TRACE_STMT_TEMP_FREE_SITE);
                    self.own.stmt_temp_frees.insert(s as *const Stmt, sites);
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
            signal!(true, trace::TRACE_COND_TEMP_FREE_SITE);
            self.own.cond_temp_frees.insert(stmt as *const Stmt, sites);
        }
    }

    pub(super) fn plan_arm_temp_frees_in_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs } => {
                for e in exprs {
                    self.plan_arm_temp_frees_in_expr(e);
                }
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr } => {
                self.plan_arm_temp_frees_in_expr(expr)
            }
            Stmt::IndexAssign { obj, key, value } => {
                self.plan_arm_temp_frees_in_expr(obj);
                self.plan_arm_temp_frees_in_expr(key);
                self.plan_arm_temp_frees_in_expr(value);
            }
            Stmt::While { condition, body } => {
                self.plan_arm_temp_frees_in_expr(condition);
                for s in body {
                    self.plan_arm_temp_frees_in_stmt(s);
                }
            }
            Stmt::Do { body } => {
                for s in body {
                    self.plan_arm_temp_frees_in_stmt(s);
                }
            }
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                self.plan_arm_temp_frees_in_expr(condition);
                for s in then_body.iter().chain(else_body) {
                    self.plan_arm_temp_frees_in_stmt(s);
                }
            }
            Stmt::Return { value } => {
                if let Some(e) = value {
                    self.plan_arm_temp_frees_in_expr(e);
                }
            }
        }
    }

    pub(super) fn plan_arm_temp_frees_in_expr(&mut self, e: &Expr) {
        match e {
            Expr::BinaryOp {
                op: BinOp::And | BinOp::Or,
                left,
                right,
            } => {
                for operand in [left.as_ref(), right.as_ref()] {
                    let mut sites = Vec::new();
                    self.collect_temp_sites(operand, Fate::Dies, &mut sites);
                    self.prune_deepfree_children(&mut sites);
                    if !sites.is_empty() {
                        signal!(true, trace::TRACE_ARM_TEMP_FREE_SITE);
                        self.own
                            .arm_temp_frees
                            .insert(operand as *const Expr, sites);
                    }
                }
                self.plan_arm_temp_frees_in_expr(left);
                self.plan_arm_temp_frees_in_expr(right);
            }
            Expr::TableCtor(entries) => {
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        self.plan_arm_temp_frees_in_expr(ke);
                    }
                    self.plan_arm_temp_frees_in_expr(v);
                }
            }
            Expr::Index { obj, key } => {
                self.plan_arm_temp_frees_in_expr(obj);
                self.plan_arm_temp_frees_in_expr(key);
            }
            Expr::BinaryOp { left, right, .. } => {
                self.plan_arm_temp_frees_in_expr(left);
                self.plan_arm_temp_frees_in_expr(right);
            }
            Expr::UnaryOp { expr, .. } => self.plan_arm_temp_frees_in_expr(expr),
            Expr::Call { callee, args } => {
                self.plan_arm_temp_frees_in_expr(callee);
                for a in args {
                    self.plan_arm_temp_frees_in_expr(a);
                }
            }
            _ => {}
        }
    }

    pub(super) fn collect_temp_sites(&self, e: &Expr, fate: Fate, out: &mut Vec<usize>) {
        match e {
            Expr::TableCtor(entries) => {
                if fate == Fate::Dies
                    && let Some(&site) = self.lattice.sites.get(&(e as *const Expr))
                {
                    out.push(site);
                }
                for (_, v) in entries {
                    self.collect_temp_sites(v, fate, out);
                }
            }
            Expr::Call { callee, args } => {
                if let Expr::Identifier(name) = callee.as_ref()
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
                            if fate == Fate::Dies && !matches!(a, Expr::Identifier(_)) {
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
            Expr::Index { obj, key } => {
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
            Expr::FfiModule => {}
            Expr::CoroModule => {}
            Expr::Field { obj, .. } => {
                self.collect_temp_sites(obj, Fate::Dies, out);
            }
            Expr::Integer(_)
            | Expr::Float(_)
            | Expr::Boolean(_)
            | Expr::String(_)
            | Expr::Nil
            | Expr::Identifier(_)
            | Expr::SysAllocCount
            | Expr::SysExecCount => {}
        }
    }

    pub(super) fn plan_fn_bodies_in_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs } => {
                for e in exprs {
                    self.plan_fn_bodies_in_expr(e);
                }
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr } => {
                self.plan_fn_bodies_in_expr(expr)
            }
            Stmt::IndexAssign { obj, key, value } => {
                self.plan_fn_bodies_in_expr(obj);
                self.plan_fn_bodies_in_expr(key);
                self.plan_fn_bodies_in_expr(value);
            }
            Stmt::While { condition, .. } => self.plan_fn_bodies_in_expr(condition),
            Stmt::If { condition, .. } => self.plan_fn_bodies_in_expr(condition),
            Stmt::Do { .. } => {}
            Stmt::Return { value } => {
                if let Some(e) = value {
                    self.plan_fn_bodies_in_expr(e);
                }
            }
        }
    }

    pub(super) fn plan_fn_bodies_in_expr(&mut self, e: &Expr) {
        match e {
            Expr::Function { body, .. } => self.plan_stmt_temp_frees(body),
            Expr::TableCtor(entries) => {
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        self.plan_fn_bodies_in_expr(ke);
                    }
                    self.plan_fn_bodies_in_expr(v);
                }
            }
            Expr::Index { obj, key } => {
                self.plan_fn_bodies_in_expr(obj);
                self.plan_fn_bodies_in_expr(key);
            }
            Expr::BinaryOp { left, right, .. } => {
                self.plan_fn_bodies_in_expr(left);
                self.plan_fn_bodies_in_expr(right);
            }
            Expr::UnaryOp { expr, .. } => self.plan_fn_bodies_in_expr(expr),
            Expr::Call { callee, args } => {
                self.plan_fn_bodies_in_expr(callee);
                for a in args {
                    self.plan_fn_bodies_in_expr(a);
                }
            }
            _ => {}
        }
    }
}
