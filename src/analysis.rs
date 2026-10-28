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

pub fn build_context<'a>(ast: &'a [Stmt]) -> AnalysisContext<'a> {
    let mut sites = BTreeMap::new();
    number_sites(ast, &mut sites);
    // THE attribution derivation (H5 sessions 2–4): read off the
    // nodes' own `loc` stamps. The parser's parallel seq arrays are
    // deleted — there is no second representation to drift, no
    // counter to miscount. Statements live in fn-literal bodies
    // inside exprs, so the walk recurses through every expression
    // face.
    let mut stmt_lines = BTreeMap::new();
    let mut stmt_locs = BTreeMap::new();
    derive_from_locs(ast, &mut stmt_lines, &mut stmt_locs);
    // H5's misattribution half: counts are structural now (a stamped
    // node cannot be un-counted), but a stamp can still be minted
    // wrong — and the one multi-statement desugar (the for loop, R7)
    // is the only place that stamps by hand-copy. The census pins its
    // discipline on every compile, over the loc-derived map.
    census_for_desugar(ast, &stmt_lines);
    // The ctor half (H5 session 3): lines read off the nodes' own
    // stamps, collected in the same pre-order number_sites walks —
    // index i IS site i, and the vec drops into every `ctor_lines[id]`
    // consumer unchanged. The count pin holds the two walks' face
    // sets together: a face added to one walk and not the other cries
    // wolf here, before it can shift a site's line.
    let ctor_lines = derive_ctor_lines(ast);
    assert_eq!(
        ctor_lines.len(),
        sites.len(),
        "ctor line derivation walks {} sites but the site walk numbered {} — the two \
         pre-order walks' faces diverged (H5)",
        ctor_lines.len(),
        sites.len()
    );

    AnalysisContext {
        sites,
        ast,
        stmt_lines,
        stmt_locs,
        ctor_lines,
    }
}

/// THE attribution derivation (H5): read off the nodes' own `loc`
/// stamps — there is no other representation. Statements live in
/// fn-literal bodies inside exprs, so the recursion covers every
/// expression face; the golden pins in property_tests.rs hold its
/// values (desugar families at the header, everything else at its own
/// leading token).
fn derive_from_locs(
    stmts: &[Stmt],
    lines: &mut BTreeMap<*const Stmt, usize>,
    locs: &mut BTreeMap<*const Stmt, SourceLoc>,
) {
    for s in stmts {
        let stamp = s.loc();
        lines.insert(s as *const Stmt, stamp.line as usize);
        locs.insert(
            s as *const Stmt,
            SourceLoc {
                line: stamp.line,
                col: stamp.col,
            },
        );
        derive_stmt_exprs(s, lines, locs);
    }
}

/// The loc-derivation's expression half — the statement lists hiding in
/// fn-literal bodies inside every expression position.
fn derive_stmt_exprs(
    stmt: &Stmt,
    lines: &mut BTreeMap<*const Stmt, usize>,
    locs: &mut BTreeMap<*const Stmt, SourceLoc>,
) {
    match stmt {
        Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
            for e in exprs {
                derive_expr(e, lines, locs);
            }
        }
        Stmt::Assignment { expr, .. } | Stmt::Expr { expr, .. } => derive_expr(expr, lines, locs),
        Stmt::IndexAssign {
            obj, key, value, ..
        } => {
            derive_expr(obj, lines, locs);
            derive_expr(key, lines, locs);
            derive_expr(value, lines, locs);
        }
        Stmt::While {
            condition, body, ..
        } => {
            derive_expr(condition, lines, locs);
            derive_from_locs(body, lines, locs);
        }
        Stmt::Do { body, .. } => derive_from_locs(body, lines, locs),
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            derive_expr(condition, lines, locs);
            derive_from_locs(then_body, lines, locs);
            derive_from_locs(else_body, lines, locs);
        }
        Stmt::Return { value, .. } => {
            if let Some(e) = value {
                derive_expr(e, lines, locs);
            }
        }
        Stmt::Break { .. } => {}
    }
}

fn derive_expr(
    e: &Expr,
    lines: &mut BTreeMap<*const Stmt, usize>,
    locs: &mut BTreeMap<*const Stmt, SourceLoc>,
) {
    match e {
        Expr::Function { body, .. } => derive_from_locs(body, lines, locs),
        Expr::TableCtor { entries, .. } => {
            for (k, v) in entries {
                if let CtorKey::Expr(ke) = k {
                    derive_expr(ke, lines, locs);
                }
                derive_expr(v, lines, locs);
            }
        }
        Expr::Index { obj, key } => {
            derive_expr(obj, lines, locs);
            derive_expr(key, lines, locs);
        }
        Expr::BinaryOp { left, right, .. } => {
            derive_expr(left, lines, locs);
            derive_expr(right, lines, locs);
        }
        Expr::UnaryOp { expr, .. } => derive_expr(expr, lines, locs),
        Expr::Call { callee, args } => {
            derive_expr(callee, lines, locs);
            for a in args {
                derive_expr(a, lines, locs);
            }
        }
        _ => {}
    }
}

/// The ctor attribution derivation (H5): lines read off the nodes'
/// own `line` stamps, collected in the same pre-order number_sites
/// walks — so index i IS site i and the vec drops into every
/// `ctor_lines[id]` consumer unchanged. The recursion mirrors
/// number_stmt/number_expr exactly (same faces, same order); the
/// count assert in build_context holds the two face sets together.
fn derive_ctor_lines(stmts: &[Stmt]) -> Vec<usize> {
    let mut lines = Vec::new();
    derive_ctor_lines_into(stmts, &mut lines);
    lines
}

fn derive_ctor_lines_into(stmts: &[Stmt], lines: &mut Vec<usize>) {
    for s in stmts {
        derive_ctor_lines_stmt(s, lines);
    }
}

fn derive_ctor_lines_stmt(stmt: &Stmt, lines: &mut Vec<usize>) {
    match stmt {
        Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
            for e in exprs {
                derive_ctor_line_expr(e, lines);
            }
        }
        Stmt::Assignment { expr, .. } | Stmt::Expr { expr, .. } => {
            derive_ctor_line_expr(expr, lines)
        }
        Stmt::IndexAssign {
            obj, key, value, ..
        } => {
            derive_ctor_line_expr(obj, lines);
            derive_ctor_line_expr(key, lines);
            derive_ctor_line_expr(value, lines);
        }
        Stmt::While {
            condition, body, ..
        } => {
            derive_ctor_line_expr(condition, lines);
            derive_ctor_lines_into(body, lines);
        }
        Stmt::Do { body, .. } => derive_ctor_lines_into(body, lines),
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            derive_ctor_line_expr(condition, lines);
            derive_ctor_lines_into(then_body, lines);
            derive_ctor_lines_into(else_body, lines);
        }
        Stmt::Return { value, .. } => {
            if let Some(e) = value {
                derive_ctor_line_expr(e, lines);
            }
        }
        Stmt::Break { .. } => {}
    }
}

fn derive_ctor_line_expr(expr: &Expr, lines: &mut Vec<usize>) {
    match expr {
        Expr::TableCtor { entries, line } => {
            lines.push(*line as usize);
            for (key, val) in entries {
                if let CtorKey::Expr(ke) = key {
                    derive_ctor_line_expr(ke, lines);
                }
                derive_ctor_line_expr(val, lines);
            }
        }
        Expr::Field { obj, .. } => derive_ctor_line_expr(obj, lines),
        Expr::Index { obj, key } => {
            derive_ctor_line_expr(obj, lines);
            derive_ctor_line_expr(key, lines);
        }
        Expr::BinaryOp { left, right, .. } => {
            derive_ctor_line_expr(left, lines);
            derive_ctor_line_expr(right, lines);
        }
        Expr::UnaryOp { expr, .. } => derive_ctor_line_expr(expr, lines),
        Expr::Call { callee, args } => {
            derive_ctor_line_expr(callee, lines);
            for a in args {
                derive_ctor_line_expr(a, lines);
            }
        }
        Expr::Function { body, .. } => derive_ctor_lines_into(body, lines),
        _ => {}
    }
}

/// THE DESUGAR ATTRIBUTION CENSUS (H5). Attribution rides the AST
/// node, so counts are structural — but a stamp can still be minted
/// wrong, and the one multi-statement desugar (the for loop, R7) is
/// the only construct that stamps by hand-copy: its six statements
/// must all carry the for header's stamp. This census walks the
/// finished tree and pins the discipline: the block Do, the counter
/// decl, the for$limit latch decl, the While, the body's inner Do,
/// and the synthetic increment ALL report the for header's one line —
/// any drift fails loudly at attribution time instead of whispering
/// wrong line prefixes into diagnostics.
///
/// `for$limit` is unspellable (identifiers are [a-zA-Z_][a-zA-Z0-9_]*,
/// lexer.rs), so the latch decl is an unforgeable fingerprint of the
/// desugar: no user-shaped program can reach these panics. If the
/// desugar's output shape itself changes, the census says so by name —
/// it must be updated together with the desugar, on purpose, in the
/// open (omniscience, not convention).
fn census_for_desugar(stmts: &[Stmt], lines: &BTreeMap<*const Stmt, usize>) {
    for s in stmts {
        if let Stmt::Do { body, .. } = s
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
                     header reports line {header} — every desugared statement must carry the \
                     header's stamp (R7's law, H5's census)"
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
            Stmt::While { body, .. } | Stmt::Do { body, .. } => census_for_desugar(body, lines),
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
        Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
            for e in exprs {
                walk(e);
            }
        }
        Stmt::Assignment { expr, .. } | Stmt::Expr { expr, .. } => walk(expr),
        Stmt::IndexAssign {
            obj, key, value, ..
        } => {
            walk(obj);
            walk(key);
            walk(value);
        }
        Stmt::While { condition, .. } => walk(condition),
        Stmt::If { condition, .. } => walk(condition),
        Stmt::Return { value, .. } => {
            if let Some(e) = value {
                walk(e);
            }
        }
        Stmt::Break { .. } | Stmt::Do { .. } => {}
    }
}

fn census_expr(e: &Expr, lines: &BTreeMap<*const Stmt, usize>) {
    match e {
        Expr::Function { body, .. } => census_for_desugar(body, lines),
        Expr::TableCtor { entries, .. } => {
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
        Stmt::IndexAssign {
            obj, key, value, ..
        } => {
            number_expr(obj, sites);
            number_expr(key, sites);
            number_expr(value, sites);
        }
        Stmt::While {
            condition, body, ..
        } => {
            number_expr(condition, sites);
            number_sites(body, sites);
        }
        Stmt::Do { body, .. } => {
            number_sites(body, sites);
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            number_expr(condition, sites);
            number_sites(then_body, sites);
            number_sites(else_body, sites);
        }
        Stmt::Print { exprs, .. } => {
            for e in exprs {
                number_expr(e, sites);
            }
        }
        Stmt::Expr { expr, .. } => number_expr(expr, sites),
        Stmt::Return { value, .. } => {
            if let Some(e) = value {
                number_expr(e, sites);
            }
        }
        Stmt::Break { .. } => {}
    }
}

fn number_expr(expr: &Expr, sites: &mut BTreeMap<*const Expr, usize>) {
    match expr {
        Expr::TableCtor { entries, .. } => {
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
        Stmt::LocalDecl { names, exprs, .. } => {
            for e in exprs {
                scan_expr(e, scopes, current_fn.as_deref_mut(), touched);
            }
            scopes.last_mut().unwrap().extend(names.iter().cloned());
        }
        Stmt::Assignment { name, expr, .. } => {
            record(current_fn.as_deref_mut(), scopes, name);
            scan_expr(expr, scopes, current_fn.as_deref_mut(), touched);
        }
        Stmt::IndexAssign {
            obj, key, value, ..
        } => {
            if let Some(base) = base_identifier(obj) {
                record(current_fn.as_deref_mut(), scopes, base);
            }
            scan_expr(obj, scopes, current_fn.as_deref_mut(), touched);
            scan_expr(key, scopes, current_fn.as_deref_mut(), touched);
            scan_expr(value, scopes, current_fn.as_deref_mut(), touched);
        }
        Stmt::While {
            condition, body, ..
        } => {
            scan_expr(condition, scopes, current_fn.as_deref_mut(), touched);
            scopes.push(Default::default());
            scan_stmts(body, scopes, current_fn.as_deref_mut(), touched);
            scopes.pop();
        }
        Stmt::Do { body, .. } => {
            scopes.push(Default::default());
            scan_stmts(body, scopes, current_fn.as_deref_mut(), touched);
            scopes.pop();
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            scan_expr(condition, scopes, current_fn.as_deref_mut(), touched);
            scopes.push(Default::default());
            scan_stmts(then_body, scopes, current_fn.as_deref_mut(), touched);
            scopes.pop();
            scopes.push(Default::default());
            scan_stmts(else_body, scopes, current_fn.as_deref_mut(), touched);
            scopes.pop();
        }
        Stmt::Print { exprs, .. } => {
            for e in exprs {
                scan_expr(e, scopes, current_fn.as_deref_mut(), touched);
            }
        }
        Stmt::Expr { expr, .. } => scan_expr(expr, scopes, current_fn.as_deref_mut(), touched),
        Stmt::Return { value, .. } => {
            if let Some(e) = value {
                scan_expr(e, scopes, current_fn, touched);
            }
        }
        Stmt::Break { .. } => {}
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
        Expr::TableCtor { entries, .. } => {
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
