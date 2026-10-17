use crate::ast::{CtorKey, Expr, Stmt};
use crate::ir::SourceLoc;
use std::collections::{BTreeMap, BTreeSet};

pub struct AnalysisContext<'a> {
    pub sites: BTreeMap<*const Expr, usize>,
    pub ast: &'a [Stmt],
    pub stmt_lines: BTreeMap<*const Stmt, usize>,
    pub stmt_locs: BTreeMap<*const Stmt, SourceLoc>,
    pub ctor_lines: Vec<usize>,
}

pub fn build_context<'a>(
    ast: &'a [Stmt],
    stmt_line_seq: &[usize],
    stmt_col_seq: &[usize],
    ctor_lines: Vec<usize>,
) -> AnalysisContext<'a> {
    let mut sites = BTreeMap::new();
    number_sites(ast, &mut sites);
    assert_eq!(
        sites.len(),
        ctor_lines.len(),
        "ctor line sequence out of step with the site walk"
    );
    assert_eq!(
        stmt_line_seq.len(),
        stmt_col_seq.len(),
        "stmt column sequence out of step with the line sequence"
    );
    let mut stmt_lines = BTreeMap::new();
    let mut stmt_locs = BTreeMap::new();
    let mut i = 0;
    record_stmt_lines(
        ast,
        &mut stmt_lines,
        &mut stmt_locs,
        stmt_line_seq,
        stmt_col_seq,
        &mut i,
    );
    assert_eq!(
        i,
        stmt_line_seq.len(),
        "stmt line sequence out of step with the AST walk"
    );

    AnalysisContext {
        sites,
        ast,
        stmt_lines,
        stmt_locs,
        ctor_lines,
    }
}

fn record_stmt_lines(
    stmts: &[Stmt],
    map: &mut BTreeMap<*const Stmt, usize>,
    locs: &mut BTreeMap<*const Stmt, SourceLoc>,
    seq: &[usize],
    cols: &[usize],
    i: &mut usize,
) {
    for s in stmts {
        if *i >= seq.len() {
            return;
        }
        map.insert(s as *const Stmt, seq[*i]);
        locs.insert(
            s as *const Stmt,
            SourceLoc {
                line: seq[*i] as u32,
                col: cols[*i] as u32,
            },
        );
        *i += 1;
        record_stmt_exprs(s, map, locs, seq, cols, i);
    }
}

fn record_stmt_exprs(
    stmt: &Stmt,
    map: &mut BTreeMap<*const Stmt, usize>,
    locs: &mut BTreeMap<*const Stmt, SourceLoc>,
    seq: &[usize],
    cols: &[usize],
    i: &mut usize,
) {
    let expr = |e: &Expr,
                map: &mut BTreeMap<*const Stmt, usize>,
                locs: &mut BTreeMap<*const Stmt, SourceLoc>,
                i: &mut usize| { record_expr_lines(e, map, locs, seq, cols, i) };
    match stmt {
        Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs } => {
            for e in exprs {
                expr(e, map, locs, i);
            }
        }
        Stmt::Assignment { expr: ev, .. } | Stmt::Expr { expr: ev } => expr(ev, map, locs, i),
        Stmt::IndexAssign { obj, key, value } => {
            expr(obj, map, locs, i);
            expr(key, map, locs, i);
            expr(value, map, locs, i);
        }
        Stmt::While { condition, body } => {
            expr(condition, map, locs, i);
            record_stmt_lines(body, map, locs, seq, cols, i);
        }
        Stmt::Do { body } => record_stmt_lines(body, map, locs, seq, cols, i),
        Stmt::If {
            condition,
            then_body,
            else_body,
        } => {
            expr(condition, map, locs, i);
            record_stmt_lines(then_body, map, locs, seq, cols, i);
            record_stmt_lines(else_body, map, locs, seq, cols, i);
        }
        Stmt::Return { value } => {
            if let Some(e) = value {
                expr(e, map, locs, i);
            }
        }
    }
}

fn record_expr_lines(
    e: &Expr,
    map: &mut BTreeMap<*const Stmt, usize>,
    locs: &mut BTreeMap<*const Stmt, SourceLoc>,
    seq: &[usize],
    cols: &[usize],
    i: &mut usize,
) {
    match e {
        Expr::Function { body, .. } => record_stmt_lines(body, map, locs, seq, cols, i),
        Expr::TableCtor(entries) => {
            for (k, v) in entries {
                if let CtorKey::Expr(ke) = k {
                    record_expr_lines(ke, map, locs, seq, cols, i);
                }
                record_expr_lines(v, map, locs, seq, cols, i);
            }
        }
        Expr::Index { obj, key } => {
            record_expr_lines(obj, map, locs, seq, cols, i);
            record_expr_lines(key, map, locs, seq, cols, i);
        }
        Expr::BinaryOp { left, right, .. } => {
            record_expr_lines(left, map, locs, seq, cols, i);
            record_expr_lines(right, map, locs, seq, cols, i);
        }
        Expr::UnaryOp { expr, .. } => record_expr_lines(expr, map, locs, seq, cols, i),
        Expr::Call { callee, args } => {
            record_expr_lines(callee, map, locs, seq, cols, i);
            for a in args {
                record_expr_lines(a, map, locs, seq, cols, i);
            }
        }
        _ => {}
    }
}

pub fn number_sites(stmts: &[Stmt], sites: &mut BTreeMap<*const Expr, usize>) {
    for s in stmts {
        number_stmt(s, sites);
    }
}

fn number_stmt(stmt: &Stmt, sites: &mut BTreeMap<*const Expr, usize>) {
    match stmt {
        Stmt::LocalDecl { exprs, .. } => {
            for e in exprs {
                number_expr(e, sites);
            }
        }
        Stmt::Assignment { expr, .. } => number_expr(expr, sites),
        Stmt::IndexAssign { obj, key, value } => {
            number_expr(obj, sites);
            number_expr(key, sites);
            number_expr(value, sites);
        }
        Stmt::While { condition, body } => {
            number_expr(condition, sites);
            number_sites(body, sites);
        }
        Stmt::Do { body } => {
            number_sites(body, sites);
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
        } => {
            number_expr(condition, sites);
            number_sites(then_body, sites);
            number_sites(else_body, sites);
        }
        Stmt::Print { exprs } => {
            for e in exprs {
                number_expr(e, sites);
            }
        }
        Stmt::Expr { expr } => number_expr(expr, sites),
        Stmt::Return { value } => {
            if let Some(e) = value {
                number_expr(e, sites);
            }
        }
    }
}

fn number_expr(expr: &Expr, sites: &mut BTreeMap<*const Expr, usize>) {
    match expr {
        Expr::TableCtor(entries) => {
            let id = sites.len();
            sites.insert(expr as *const Expr, id);
            for (key, val) in entries {
                if let CtorKey::Expr(ke) = key {
                    number_expr(ke, sites);
                }
                number_expr(val, sites);
            }
        }
        Expr::SysAllocCount => {}
        Expr::SysExecCount => {}
        Expr::FfiModule => {}
        Expr::CoroModule => {}
        Expr::Field { obj, .. } => {
            number_expr(obj, sites);
        }
        Expr::Index { obj, key } => {
            number_expr(obj, sites);
            number_expr(key, sites);
        }
        Expr::BinaryOp { left, right, .. } => {
            number_expr(left, sites);
            number_expr(right, sites);
        }
        Expr::UnaryOp { expr, .. } => number_expr(expr, sites),
        Expr::Call { callee, args } => {
            number_expr(callee, sites);
            for a in args {
                number_expr(a, sites);
            }
        }
        Expr::Function { body, .. } => {
            number_sites(body, sites);
        }
        _ => {}
    }
}

pub fn scan_fn_touched(stmts: &[Stmt]) -> BTreeMap<*const Expr, BTreeSet<String>> {
    let mut touched = BTreeMap::new();
    let mut scopes = vec![BTreeSet::new()];
    scan_stmts(stmts, &mut scopes, None, &mut touched);
    touched
}

struct FnScan {
    entry_depth: usize,
    touched: BTreeSet<String>,
}

fn scan_stmts(
    stmts: &[Stmt],
    scopes: &mut Vec<BTreeSet<String>>,
    mut current_fn: Option<&mut FnScan>,
    touched: &mut BTreeMap<*const Expr, BTreeSet<String>>,
) {
    for s in stmts {
        scan_stmt(s, scopes, current_fn.as_deref_mut(), touched);
    }
}

fn base_identifier(expr: &Expr) -> Option<&String> {
    match expr {
        Expr::Identifier(name) => Some(name),
        Expr::Index { obj, .. } => base_identifier(obj),
        _ => None,
    }
}

fn scan_stmt(
    stmt: &Stmt,
    scopes: &mut Vec<BTreeSet<String>>,
    mut current_fn: Option<&mut FnScan>,
    touched: &mut BTreeMap<*const Expr, BTreeSet<String>>,
) {
    fn record(current_fn: Option<&mut FnScan>, scopes: &[BTreeSet<String>], name: &str) {
        if let Some(scan) = current_fn
            && !scopes[scan.entry_depth..].iter().any(|s| s.contains(name))
        {
            scan.touched.insert(name.to_string());
        }
    }
    match stmt {
        Stmt::LocalDecl { names, exprs } => {
            for e in exprs {
                scan_expr(e, scopes, current_fn.as_deref_mut(), touched);
            }
            scopes.last_mut().unwrap().extend(names.iter().cloned());
        }
        Stmt::Assignment { name, expr } => {
            record(current_fn.as_deref_mut(), scopes, name);
            scan_expr(expr, scopes, current_fn.as_deref_mut(), touched);
        }
        Stmt::IndexAssign { obj, key, value } => {
            if let Some(base) = base_identifier(obj) {
                record(current_fn.as_deref_mut(), scopes, base);
            }
            scan_expr(obj, scopes, current_fn.as_deref_mut(), touched);
            scan_expr(key, scopes, current_fn.as_deref_mut(), touched);
            scan_expr(value, scopes, current_fn.as_deref_mut(), touched);
        }
        Stmt::While { condition, body } => {
            scan_expr(condition, scopes, current_fn.as_deref_mut(), touched);
            scopes.push(Default::default());
            scan_stmts(body, scopes, current_fn.as_deref_mut(), touched);
            scopes.pop();
        }
        Stmt::Do { body } => {
            scopes.push(Default::default());
            scan_stmts(body, scopes, current_fn.as_deref_mut(), touched);
            scopes.pop();
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
        } => {
            scan_expr(condition, scopes, current_fn.as_deref_mut(), touched);
            scopes.push(Default::default());
            scan_stmts(then_body, scopes, current_fn.as_deref_mut(), touched);
            scopes.pop();
            scopes.push(Default::default());
            scan_stmts(else_body, scopes, current_fn.as_deref_mut(), touched);
            scopes.pop();
        }
        Stmt::Print { exprs } => {
            for e in exprs {
                scan_expr(e, scopes, current_fn.as_deref_mut(), touched);
            }
        }
        Stmt::Expr { expr } => scan_expr(expr, scopes, current_fn.as_deref_mut(), touched),
        Stmt::Return { value } => {
            if let Some(e) = value {
                scan_expr(e, scopes, current_fn, touched);
            }
        }
    }
}

fn scan_expr(
    expr: &Expr,
    scopes: &mut Vec<BTreeSet<String>>,
    mut current_fn: Option<&mut FnScan>,
    touched: &mut BTreeMap<*const Expr, BTreeSet<String>>,
) {
    match expr {
        Expr::Function { params, body } => {
            let entry_depth = scopes.len();
            scopes.push(params.iter().cloned().collect());
            let mut inner = FnScan {
                entry_depth,
                touched: BTreeSet::new(),
            };
            scan_stmts(body, scopes, Some(&mut inner), touched);
            scopes.pop();
            if let Some(outer) = current_fn.as_deref_mut() {
                outer.touched.extend(inner.touched.iter().cloned());
            }
            touched.insert(expr as *const Expr, inner.touched);
        }
        Expr::Call { callee, args } => {
            scan_expr(callee, scopes, current_fn.as_deref_mut(), touched);
            for a in args {
                scan_expr(a, scopes, current_fn.as_deref_mut(), touched);
            }
        }
        Expr::Index { obj, key } => {
            scan_expr(obj, scopes, current_fn.as_deref_mut(), touched);
            scan_expr(key, scopes, current_fn.as_deref_mut(), touched);
        }
        Expr::BinaryOp { left, right, .. } => {
            scan_expr(left, scopes, current_fn.as_deref_mut(), touched);
            scan_expr(right, scopes, current_fn.as_deref_mut(), touched);
        }
        Expr::UnaryOp { expr, .. } => scan_expr(expr, scopes, current_fn.as_deref_mut(), touched),
        Expr::TableCtor(entries) => {
            for (k, v) in entries {
                if let CtorKey::Expr(ke) = k {
                    scan_expr(ke, scopes, current_fn.as_deref_mut(), touched);
                }
                scan_expr(v, scopes, current_fn.as_deref_mut(), touched);
            }
        }
        _ => {}
    }
}
