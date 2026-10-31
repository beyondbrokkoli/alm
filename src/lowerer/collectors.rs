
fn const_of(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Integer { value: v, .. } => Some(*v),
        _ => None,
    }
}

fn find_moved_names(stmts: &[Stmt], shape: &ShapeFacts) -> BTreeSet<String> {
    let mut moved = BTreeSet::new();
    let mut seen = BTreeSet::new();
    find_moved_names_into(stmts, shape, &mut moved, &mut seen);
    moved
}

/// The recursion threads the accumulator and `seen` through nested
/// blocks (the `fn_stmts_touched` shape): one query, one `seen` — a fn
/// body walked in a sibling branch is not walked again. The union is
/// idempotent, so the result is identical to the per-block recursion;
/// only the re-walk and the per-block allocations die.
fn find_moved_names_into(
    stmts: &[Stmt],
    shape: &ShapeFacts,
    out: &mut BTreeSet<String>,
    seen: &mut BTreeSet<NodeId>,
) {
    for stmt in stmts {
        if let Some(names) = shape.move_poisons.get(&stmt.id()) {
            out.extend(names.iter().cloned());
        }
        stmt_call_touched(stmt, shape, out, seen);
        match stmt {
            Stmt::While { body, .. } | Stmt::Do { body, .. } => {
                find_moved_names_into(body, shape, out, seen);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                find_moved_names_into(then_body, shape, out, seen);
                find_moved_names_into(else_body, shape, out, seen);
            }
            _ => {}
        }
    }
}

fn calls_touched(
    expr: &Expr,
    shape: &ShapeFacts,
    out: &mut BTreeSet<String>,
    seen: &mut BTreeSet<NodeId>,
) {
    match expr {
        Expr::Call { callee, args, .. } => {
            // union read: every instantiation of this call expr (all its
            // expansion sites) contributes its fn's touched names — the
            // order-insensitive consumer the per-instantiation keys were
            // designed to leave alone
            let key = expr.id();
            for (_, &fn_ptr) in shape
                .call_defs
                .range((key, NodeId(0))..=(key, NodeId(u32::MAX)))
            {
                if let Some(touched) = shape.fn_touched.get(&fn_ptr) {
                    out.extend(touched.iter().cloned());
                }
                // THE TRANSITIVE CLOSURE: `fn_touched` is the per-fn law
                // (a fn's own lexical outer touches — the derivation
                // pass's scan; a callee's set lives under its own id and
                // never propagates into its caller's). A chain G→H
                // assigning an outer name must therefore reach the set
                // through the MIDDLE call: walk the callee's OWNED BODY
                // (H6's self-contained facts) with the same walker. The
                // checker refuses recursive inlining, so the call graph
                // is a DAG on every compile that reaches the lowerer;
                // `seen` is the walk's convergence face and its defense
                // in depth.
                if seen.insert(fn_ptr)
                    && let Some(def) = shape.fn_defs.get(&fn_ptr)
                {
                    fn_stmts_touched(def.body(), shape, out, seen);
                }
            }
            calls_touched(callee, shape, out, seen);
            for a in args {
                calls_touched(a, shape, out, seen);
            }
        }
        Expr::BinaryOp { left, right, .. } => {
            calls_touched(left, shape, out, seen);
            calls_touched(right, shape, out, seen);
        }
        Expr::UnaryOp { expr, .. } => calls_touched(expr, shape, out, seen),
        Expr::Index { obj, key, .. } => {
            calls_touched(obj, shape, out, seen);
            calls_touched(key, shape, out, seen);
        }
        Expr::Field { obj, .. } => calls_touched(obj, shape, out, seen),
        Expr::TableCtor { entries, .. } => {
            for (k, v) in entries {
                if let CtorKey::Expr(ke) = k {
                    calls_touched(ke, shape, out, seen);
                }
                calls_touched(v, shape, out, seen);
            }
        }
        _ => {}
    }
}

/// The transitive closure's body walker: one fn's owned body, every
/// statement face (nested loops and branches included), every call
/// routed back through `calls_touched` so the chain keeps walking.
fn fn_stmts_touched(
    stmts: &[Stmt],
    shape: &ShapeFacts,
    out: &mut BTreeSet<String>,
    seen: &mut BTreeSet<NodeId>,
) {
    for s in stmts {
        stmt_call_touched(s, shape, out, seen);
        match s {
            Stmt::While { body, .. } | Stmt::Do { body, .. } => {
                fn_stmts_touched(body, shape, out, seen);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                fn_stmts_touched(then_body, shape, out, seen);
                fn_stmts_touched(else_body, shape, out, seen);
            }
            _ => {}
        }
    }
}

/// Every expression face one statement carries, swept for calls. The
/// loop-phi collectors ride this on EVERY statement shape: the pre-fold
/// scan reached `calls_touched` only from `Stmt::Expr`, so a call in
/// any value position (`local c = H()`, `c = H()`, `print(H())`, a
/// condition, a return value) contributed nothing — an outer name
/// assigned through such a call never joined the loop's phi set, the
/// loop body read the pre-loop register every iteration, and a
/// post-loop read was an undominated use (the backend aborted on a
/// legal program; without the read the loop's writes were silently
/// lost). Over-approximation is the safe direction here: a name in the
/// phi set whose register never changes mints a degenerate phi, never
/// a wrong answer.
fn stmt_call_touched(
    stmt: &Stmt,
    shape: &ShapeFacts,
    out: &mut BTreeSet<String>,
    seen: &mut BTreeSet<NodeId>,
) {
    match stmt {
        Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
            for e in exprs {
                calls_touched(e, shape, out, seen);
            }
        }
        Stmt::Assignment { expr, .. } => calls_touched(expr, shape, out, seen),
        Stmt::IndexAssign {
            obj, key, value, ..
        } => {
            calls_touched(obj, shape, out, seen);
            calls_touched(key, shape, out, seen);
            calls_touched(value, shape, out, seen);
        }
        Stmt::While { condition, .. } => calls_touched(condition, shape, out, seen),
        Stmt::If { condition, .. } => calls_touched(condition, shape, out, seen),
        Stmt::Expr { expr, .. } => calls_touched(expr, shape, out, seen),
        Stmt::Return { value: Some(e), .. } => calls_touched(e, shape, out, seen),
        _ => {}
    }
}

fn find_mutated_vars(stmts: &[Stmt], shape: &ShapeFacts) -> BTreeSet<String> {
    let mut mutated = BTreeSet::new();
    let mut seen = BTreeSet::new();
    find_mutated_names_into(stmts, shape, &mut mutated, &mut seen);
    mutated
}

/// `find_moved_names_into`'s twin: the assigned-name face rides the
/// same threaded recursion.
fn find_mutated_names_into(
    stmts: &[Stmt],
    shape: &ShapeFacts,
    out: &mut BTreeSet<String>,
    seen: &mut BTreeSet<NodeId>,
) {
    for stmt in stmts {
        stmt_call_touched(stmt, shape, out, seen);
        match stmt {
            Stmt::Assignment { name, .. } => {
                out.insert(name.clone());
            }
            Stmt::While { body, .. } => {
                find_mutated_names_into(body, shape, out, seen);
            }
            Stmt::Do { body, .. } => {
                find_mutated_names_into(body, shape, out, seen);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                find_mutated_names_into(then_body, shape, out, seen);
                find_mutated_names_into(else_body, shape, out, seen);
            }
            _ => {}
        }
    }
}

fn as_ident(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Identifier { name, .. } => Some(name),
        _ => None,
    }
}

fn get_base_identifier(expr: &Expr) -> Option<&String> {
    match expr {
        Expr::Identifier { name, .. } => Some(name),
        Expr::Index { obj, .. } => get_base_identifier(obj),
        _ => None,
    }
}
