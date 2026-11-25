use super::*;
#[derive(Clone, Copy, PartialEq)]
pub(super) enum Fate {
    Dies,
    Escapes,
}

impl Analyzer {
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
