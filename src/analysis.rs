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
        "stmt line sequence out of step with the AST walk (over-run: {} fabricated entries \
         were never consumed by {} statements — a desugar minted seq entries without \
         minting statements)",
        stmt_line_seq.len(),
        i
    );
    // H5's misattribution half: the count asserts prove totals in both
    // directions; they cannot prove a fabricated entry points at the
    // RIGHT line. The census pins the one multi-statement desugar's
    // attribution discipline on every compile.
    census_for_desugar(ast, &stmt_lines);

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
        // H5's loud under-count: build_context only ever sees fully
        // parsed programs (both call sites gate on empty front
        // diagnostics), so a missing entry here is a desugar that
        // minted statements without minting their seq entries. The
        // old silent early-return masked exactly this bug class —
        // trailing statements went line-less and the final count
        // assert still passed. It cries wolf now.
        let (line, col) = match (seq.get(*i), cols.get(*i)) {
            (Some(&l), Some(&c)) => (l, c),
            _ => panic!(
                "stmt line sequence under-runs the AST walk: statement #{} ({}) has no \
                 fabricated entry — a desugar minted statements without minting seq \
                 entries (H5)",
                *i,
                stmt_kind(s)
            ),
        };
        map.insert(s as *const Stmt, line);
        locs.insert(
            s as *const Stmt,
            SourceLoc {
                line: line as u32,
                col: col as u32,
            },
        );
        *i += 1;
        record_stmt_exprs(s, map, locs, seq, cols, i);
    }
}

/// The statement's kind name for tripwire prose: H5's panics name the
/// construct that ran out of entries (or the entry that ran out of
/// construct).
fn stmt_kind(s: &Stmt) -> &'static str {
    match s {
        Stmt::LocalDecl { .. } => "LocalDecl",
        Stmt::Assignment { .. } => "Assignment",
        Stmt::IndexAssign { .. } => "IndexAssign",
        Stmt::While { .. } => "While",
        Stmt::Do { .. } => "Do",
        Stmt::If { .. } => "If",
        Stmt::Print { .. } => "Print",
        Stmt::Expr { .. } => "Expr",
        Stmt::Return { .. } => "Return",
        Stmt::Break => "Break",
    }
}

/// THE DESUGAR ATTRIBUTION CENSUS (H5). The count asserts above are
/// symmetric — under-run and over-run both cry wolf — but a right-COUNT
/// wrong-LINE fabrication slips through them silently: only the one
/// multi-statement desugar (the for loop, R7) fabricates entries by
/// hand (four pre-pushes before the body parses, one post-push after),
/// so only it can drift. This census walks the finished tree and pins
/// the discipline: the block Do, the counter decl, the for$limit latch
/// decl, the While, the body's inner Do, and the synthetic increment
/// ALL report the for header's one line — any drift fails loudly at
/// attribution time instead of whispering wrong line prefixes into
/// diagnostics.
///
/// `for$limit` is unspellable (identifiers are [a-zA-Z_][a-zA-Z0-9_]*,
/// lexer.rs), so the latch decl is an unforgeable fingerprint of the
/// desugar: no user-shaped program can reach these panics. If the
/// desugar's output shape itself changes, the census says so by name —
/// it must be updated together with the desugar, on purpose, in the
/// open (omniscience, not convention).
fn census_for_desugar(stmts: &[Stmt], lines: &BTreeMap<*const Stmt, usize>) {
    for s in stmts {
        if let Stmt::Do { body } = s
            && matches!(
                body.get(1),
                Some(Stmt::LocalDecl { names, .. })
                    if names.len() == 1 && names[0] == "for$limit"
            )
        {
            let header = lines
                .get(&(s as *const Stmt))
                .expect("for-desugar census: the block Do is unmapped (H5)");
            let check = |what: &str, node: &Stmt| match lines.get(&(node as *const Stmt)) {
                Some(&l) if l == *header => {}
                Some(&l) => panic!(
                    "for-desugar attribution drift: the {what} reports line {l} but the for \
                     header reports line {header} — every fabricated entry must point at the \
                     header (R7's law, H5's census)"
                ),
                None => panic!("for-desugar census: the {what} is unmapped (H5)"),
            };
            check("counter decl", &body[0]);
            check("for$limit latch decl", &body[1]);
            let Stmt::While { body: wbody, .. } = &body[2] else {
                panic!(
                    "for-desugar census: the block's third statement is not the While — the \
                     desugar shape changed; update the census with it (H5)"
                );
            };
            check("While", &body[2]);
            match (wbody.first(), wbody.last()) {
                (Some(inner), Some(inc)) if wbody.len() == 2 => {
                    check("body's inner Do", inner);
                    check("synthetic increment", inc);
                }
                _ => panic!(
                    "for-desugar census: the While body is not [inner Do, increment] — the \
                     desugar shape changed; update the census with it (H5)"
                ),
            }
        }
        // recurse through every statement list, including fn-literal
        // bodies riding inside expressions (a for can hide in any of
        // them)
        match s {
            Stmt::While { body, .. } | Stmt::Do { body } => census_for_desugar(body, lines),
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                census_for_desugar(then_body, lines);
                census_for_desugar(else_body, lines);
            }
            _ => {}
        }
        census_for_desugar_in_exprs(s, lines);
    }
}

/// The expression half of the census recursion: statements hide inside
/// fn-literal bodies, which ride inside every expression position.
fn census_for_desugar_in_exprs(stmt: &Stmt, lines: &BTreeMap<*const Stmt, usize>) {
    let walk = |e: &Expr| census_expr(e, lines);
    match stmt {
        Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs } => {
            for e in exprs {
                walk(e);
            }
        }
        Stmt::Assignment { expr, .. } | Stmt::Expr { expr } => walk(expr),
        Stmt::IndexAssign { obj, key, value } => {
            walk(obj);
            walk(key);
            walk(value);
        }
        Stmt::While { condition, .. } => walk(condition),
        Stmt::If { condition, .. } => walk(condition),
        Stmt::Return { value } => {
            if let Some(e) = value {
                walk(e);
            }
        }
        Stmt::Break | Stmt::Do { .. } => {}
    }
}

fn census_expr(e: &Expr, lines: &BTreeMap<*const Stmt, usize>) {
    match e {
        Expr::Function { body, .. } => census_for_desugar(body, lines),
        Expr::TableCtor(entries) => {
            for (k, v) in entries {
                if let CtorKey::Expr(ke) = k {
                    census_expr(ke, lines);
                }
                census_expr(v, lines);
            }
        }
        Expr::Index { obj, key } => {
            census_expr(obj, lines);
            census_expr(key, lines);
        }
        Expr::BinaryOp { left, right, .. } => {
            census_expr(left, lines);
            census_expr(right, lines);
        }
        Expr::UnaryOp { expr, .. } => census_expr(expr, lines),
        Expr::Call { callee, args } => {
            census_expr(callee, lines);
            for a in args {
                census_expr(a, lines);
            }
        }
        _ => {}
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
        Stmt::Break => {}
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
        Stmt::Break => {}
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
        Stmt::Break => {}
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
