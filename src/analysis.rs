use crate::ast::{CtorKey, Expr, NodeId, Stmt};
use std::collections::{BTreeMap, BTreeSet};

pub struct AnalysisContext<'a> {
    pub sites: BTreeMap<NodeId, usize>,
    pub ast: &'a [Stmt],
    pub ctor_lines: Vec<usize>,
    /// The fn-touched map (H7): per fn-literal node, the OUTER names
    /// its body assigns or stores through — the bindings a closure
    /// reaches past its own scopes. Minted by the one derivation pass
    /// below; the analyzer hands it to the facts (mod.rs) and the
    /// lowerer consumes it for closure captures.
    pub fn_touched: BTreeMap<NodeId, BTreeSet<String>>,
}

pub fn build_context<'a>(ast: &'a [Stmt]) -> AnalysisContext<'a> {
    // ONE derivation pass (H7): one walk mints every map — site ids,
    // ctor lines, fn-touched. The ctor line and the site id land at
    // the SAME arm of the SAME walk, so `ctor_lines[id]` is the
    // ctor's own `{` line by construction; H5's count assert (two
    // walks' face sets held together by hand) died with the second
    // walk — same walk, same faces is structural now.
    let mut pass = Derivation::new();
    pass.run(ast);
    // THE DESUGAR ATTRIBUTION CENSUS (H5/H8) stays the every-compile
    // omniscience check: it walks the FINISHED tree reading the
    // nodes' own stamps (H6: `loc` off the node — there is no line
    // map left to read) — a check on top of the derivation, not a
    // second derivation. Counts are structural (a stamped node
    // cannot be un-counted), but a stamp can still be minted wrong,
    // and the multi-statement desugars (the for loop, R7; the tuple
    // assignment, H8) are the places that stamp by hand-copy.
    census_for_desugar(ast);

    AnalysisContext {
        sites: pass.sites,
        ast,
        ctor_lines: pass.ctor_lines,
        fn_touched: pass.fn_touched,
    }
}

/// THE ONE DERIVATION PASS (H7): analysis.rs walked the tree five
/// times — the site numbering, the loc derivation, the census, the
/// ctor-line collection, the fn-touched scan — and the walks' face
/// sets were held together by hand: an assert compared two counts,
/// and the loc/census/scan walks quietly skipped the Field face the
/// site/ctor walks visited. The fold: ONE walk, ONE face set, every
/// map minted in place —
///
/// - the TableCtor arm numbers the site AND pushes its line at the
///   same pre-order index (index i IS site i, structurally — there is
///   no second count to assert against);
/// - statements no longer need a line/loc MAP at all (H6 killed
///   `stmt_lines`/`stmt_locs`): every stamp is a field off the node
///   (H5's loc dividend), so consumers read `s.loc()` directly and
///   this pass mints only what a node cannot carry itself;
/// - the fn-touched scan rides along (scope stack + per-fn
///   accumulators): purely syntactic, no walk result feeds it, so its
///   old late call site (analyze_with, after the walk) bought nothing
///   — the map now rides the context and the analyzer copies it into
///   the facts;
/// - the FACE SET is the union the old walks already disagreed on:
///   Field objs recurse (the site/ctor walks' face — the checker
///   infers through Field, so sites must cover it), which closes the
///   loc/scan walks' old Field blind spot: a fn body under a Field
///   obj carries stamps and a touched set like any other fn body.
///
/// A face added here is added to every map at once — there is no
/// second walk whose faces can drift. The census below is the one
/// remaining deliberate second walk: a CHECK over the finished tree,
/// recursing the same faces by law (its pins hold it).
///
/// THE IDENTITY CENSUS (H6) rides this pass: every node's `NodeId`
/// is asserted unique over the whole tree. Identity rides the node —
/// one construction mints one id — so a duplicate can only mean a
/// CLONED subtree reached the tree (a copy is the same node; making a
/// new one means constructing it). The census makes that accident
/// loud here, at analysis time, instead of letting two "different"
/// statements silently share one fact entry.
struct Derivation {
    sites: BTreeMap<NodeId, usize>,
    ctor_lines: Vec<usize>,
    fn_touched: BTreeMap<NodeId, BTreeSet<String>>,
    seen: BTreeSet<NodeId>,
    /// the fn-touched scan's scope stack: names declared at each
    /// depth. A body-touched name is an OUTER one — not declared in
    /// any scope at or below the fn's entry depth.
    scopes: Vec<BTreeSet<String>>,
}

/// A fn literal's touched-name accumulator (the scan half of the
/// pass): names the body assigns or stores through that no scope at
/// or below its entry depth declares.
struct FnScan {
    entry_depth: usize,
    touched: BTreeSet<String>,
}

impl Derivation {
    fn new() -> Self {
        Derivation {
            sites: BTreeMap::new(),
            ctor_lines: Vec::new(),
            fn_touched: BTreeMap::new(),
            seen: BTreeSet::new(),
            scopes: vec![BTreeSet::new()],
        }
    }

    fn run(&mut self, stmts: &[Stmt]) {
        for s in stmts {
            self.visit_stmt(s, None);
        }
    }

    fn visit_stmts(&mut self, stmts: &[Stmt], mut current_fn: Option<&mut FnScan>) {
        for s in stmts {
            self.visit_stmt(s, current_fn.as_deref_mut());
        }
    }

    /// One statement, every map at once: the identity census first,
    /// then the arm's children in the ONE visit order — the pre-order
    /// byte-identical to the walks this pass replaced (site ids and
    /// ctor line indexes included). Line and loc need no mint: they
    /// are fields off the node (H5/H6).
    fn visit_stmt(&mut self, stmt: &Stmt, mut current_fn: Option<&mut FnScan>) {
        assert!(
            self.seen.insert(stmt.id()),
            "identity census (H6): stmt id {} appears twice — a cloned subtree \
             reached the tree; one construction mints one node, a re-materialized \
             subtree must be constructed, never cloned",
            stmt.id().0
        );
        match stmt {
            Stmt::LocalDecl { names, exprs, .. } => {
                for e in exprs {
                    self.visit_expr(e, current_fn.as_deref_mut());
                }
                // the scan half: initializers cannot see the names
                // they declare — scope-extend AFTER the exprs
                self.scopes
                    .last_mut()
                    .unwrap()
                    .extend(names.iter().cloned());
            }
            Stmt::Assignment { name, expr, .. } => {
                record_touched(current_fn.as_deref_mut(), &self.scopes, name);
                self.visit_expr(expr, current_fn);
            }
            Stmt::IndexAssign {
                obj, key, value, ..
            } => {
                if let Some(base) = base_identifier(obj) {
                    record_touched(current_fn.as_deref_mut(), &self.scopes, base);
                }
                self.visit_expr(obj, current_fn.as_deref_mut());
                self.visit_expr(key, current_fn.as_deref_mut());
                self.visit_expr(value, current_fn);
            }
            Stmt::While {
                condition, body, ..
            } => {
                self.visit_expr(condition, current_fn.as_deref_mut());
                self.scopes.push(Default::default());
                self.visit_stmts(body, current_fn);
                self.scopes.pop();
            }
            Stmt::Do { body, .. } => {
                self.scopes.push(Default::default());
                self.visit_stmts(body, current_fn);
                self.scopes.pop();
            }
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                self.visit_expr(condition, current_fn.as_deref_mut());
                self.scopes.push(Default::default());
                self.visit_stmts(then_body, current_fn.as_deref_mut());
                self.scopes.pop();
                self.scopes.push(Default::default());
                self.visit_stmts(else_body, current_fn);
                self.scopes.pop();
            }
            Stmt::Print { exprs, .. } => {
                for e in exprs {
                    self.visit_expr(e, current_fn.as_deref_mut());
                }
            }
            Stmt::Expr { expr, .. } => self.visit_expr(expr, current_fn),
            Stmt::Return { value, .. } => {
                if let Some(e) = value {
                    self.visit_expr(e, current_fn);
                }
            }
            Stmt::Break { .. } => {}
        }
    }

    /// One expression: the identity census, the ctor's two mints, the
    /// fn literal's scope and touched set, and the one recursion
    /// shared by every face.
    fn visit_expr(&mut self, expr: &Expr, mut current_fn: Option<&mut FnScan>) {
        assert!(
            self.seen.insert(expr.id()),
            "identity census (H6): expr id {} appears twice — a cloned subtree \
             reached the tree; one construction mints one node, a re-materialized \
             subtree must be constructed, never cloned",
            expr.id().0
        );
        match expr {
            Expr::TableCtor { entries, line, .. } => {
                // ONE arm, TWO mints: the site id and the ctor line
                // land at the same pre-order index — `ctor_lines[id]`
                // is this ctor's `{` line by construction. The pair
                // cannot disagree; H5's count assert died here.
                self.sites.insert(expr.id(), self.sites.len());
                self.ctor_lines.push(*line as usize);
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        self.visit_expr(ke, current_fn.as_deref_mut());
                    }
                    self.visit_expr(v, current_fn.as_deref_mut());
                }
            }
            Expr::Field { obj, .. } => {
                self.visit_expr(obj, current_fn);
            }
            Expr::Index { obj, key, .. } => {
                self.visit_expr(obj, current_fn.as_deref_mut());
                self.visit_expr(key, current_fn);
            }
            Expr::BinaryOp { left, right, .. } => {
                self.visit_expr(left, current_fn.as_deref_mut());
                self.visit_expr(right, current_fn);
            }
            Expr::UnaryOp { expr, .. } => self.visit_expr(expr, current_fn),
            Expr::Call { callee, args, .. } => {
                self.visit_expr(callee, current_fn.as_deref_mut());
                for a in args {
                    self.visit_expr(a, current_fn.as_deref_mut());
                }
            }
            Expr::Function { params, body, .. } => {
                let entry_depth = self.scopes.len();
                self.scopes.push(params.iter().cloned().collect());
                let mut inner = FnScan {
                    entry_depth,
                    touched: BTreeSet::new(),
                };
                self.visit_stmts(body, Some(&mut inner));
                self.scopes.pop();
                // a nested fn's outer touches are the parent's too
                if let Some(outer) = current_fn {
                    outer.touched.extend(inner.touched.iter().cloned());
                }
                self.fn_touched.insert(expr.id(), inner.touched);
            }
            _ => {}
        }
    }
}

/// The scan's one law: a name a fn body assigns or stores through is
/// TOUCHED iff no scope at or below the fn's entry depth declares it.
fn record_touched(current_fn: Option<&mut FnScan>, scopes: &[BTreeSet<String>], name: &str) {
    if let Some(scan) = current_fn
        && !scopes[scan.entry_depth..].iter().any(|s| s.contains(name))
    {
        scan.touched.insert(name.to_string());
    }
}

/// The base name a store writes through (`t` in `t[x][i] = v`), if
/// the obj face is a plain chain of indexes off a name.
fn base_identifier(expr: &Expr) -> Option<&String> {
    match expr {
        Expr::Identifier { name, .. } => Some(name),
        Expr::Index { obj, .. } => base_identifier(obj),
        _ => None,
    }
}

/// THE DESUGAR ATTRIBUTION CENSUS (H5). Attribution rides the AST
/// node, so counts are structural — but a stamp can still be minted
/// wrong, and the multi-statement desugars (the for loop, R7; the
/// tuple assignment, H8/row 3) are the only constructs that stamp by
/// hand-copy: their synthetic statements must all carry the sugar
/// header's stamp. This census walks the finished tree — reading each
/// node's OWN stamp (H6: `loc` off the node; the line map is gone),
/// recursing the pass's faces by law, Field included — and pins the
/// discipline; any drift fails loudly at attribution time instead of
/// whispering wrong line prefixes into diagnostics.
///
/// `for$limit` and `tuple$tN` are unspellable (identifiers are
/// [a-zA-Z_][a-zA-Z0-9_]*, lexer.rs), so both latch decls are
/// unforgeable fingerprints of their desugars: no user-shaped
/// program can reach these panics. If a desugar's output shape
/// itself changes, the census says so by name — it must be updated
/// together with the desugar (the pure elaborator, elaborate.rs, and
/// its unit goldens), on purpose, in the open (omniscience, not
/// convention).
fn census_for_desugar(stmts: &[Stmt]) {
    for s in stmts {
        if let Stmt::Do { body, .. } = s
            && matches!(
                body.get(1),
                Some(Stmt::LocalDecl { names, .. })
                    if names.len() == 1 && names[0] == "for$limit"
            )
        {
            let header = s.loc().line;
            let check = |what: &str, node: &Stmt| {
                let l = node.loc().line;
                if l != header {
                    panic!(
                        "for-desugar attribution drift: the {what} reports line {l} but the for \
                         header reports line {header} — every desugared statement must carry the \
                         header's stamp (R7's law, H5's census)"
                    );
                }
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
        // The tuple-assign family (H8): a Do whose first statement is
        // the `tuple$tN` temp decl. The same header-discipline check,
        // plus the family's wiring shape — store i's value IS temp i.
        if let Stmt::Do { body, .. } = s
            && matches!(
                body.first(),
                Some(Stmt::LocalDecl { names, .. })
                    if !names.is_empty() && names[0] == "tuple$t0"
            )
        {
            let header = s.loc().line;
            let check = |what: &str, node: &Stmt| {
                let l = node.loc().line;
                if l != header {
                    panic!(
                        "tuple-assign attribution drift: the {what} reports line {l} but the \
                         tuple header reports line {header} — every desugared statement must \
                         carry the header's stamp (R7's law, H5's census)"
                    );
                }
            };
            let Stmt::LocalDecl { names, .. } = &body[0] else {
                unreachable!("the fingerprint arm matched a LocalDecl")
            };
            for (i, name) in names.iter().enumerate() {
                if name != &format!("tuple$t{i}") {
                    panic!(
                        "tuple-assign census: temp {i} is named '{name}', not 'tuple$t{i}' — \
                         the desugar shape changed; update the census with it (H8)"
                    );
                }
            }
            check("temp decl", &body[0]);
            if body.len() != names.len() + 1 {
                panic!(
                    "tuple-assign census: {} temps but {} statements in the block — the desugar \
                     shape changed; update the census with it (H8)",
                    names.len(),
                    body.len() - 1
                );
            }
            for (i, stmt) in body[1..].iter().enumerate() {
                let Stmt::IndexAssign { value, .. } = stmt else {
                    panic!(
                        "tuple-assign census: the block's statement {} is not the cell store — \
                         the desugar shape changed; update the census with it (H8)",
                        i + 1
                    );
                };
                if !matches!(value, Expr::Identifier { name: v, .. } if v == &format!("tuple$t{i}"))
                {
                    panic!(
                        "tuple-assign census: store {i} does not read temp {i} — the desugar \
                         shape changed; update the census with it (H8)"
                    );
                }
                check(&format!("cell store {i}"), stmt);
            }
        }
        // recurse through every statement list, including fn-literal
        // bodies riding inside expressions (a for can hide in any of
        // them)
        match s {
            Stmt::While { body, .. } | Stmt::Do { body, .. } => census_for_desugar(body),
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                census_for_desugar(then_body);
                census_for_desugar(else_body);
            }
            _ => {}
        }
        census_for_desugar_in_exprs(s);
    }
}

/// The expression half of the census recursion: statements hide inside
/// fn-literal bodies, which ride inside every expression position.
fn census_for_desugar_in_exprs(stmt: &Stmt) {
    let walk = census_expr;
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

fn census_expr(e: &Expr) {
    match e {
        Expr::Function { body, .. } => census_for_desugar(body),
        Expr::TableCtor { entries, .. } => {
            for (k, v) in entries {
                if let CtorKey::Expr(ke) = k {
                    census_expr(ke);
                }
                census_expr(v);
            }
        }
        // the pass's Field face (H7): the census recurses every face
        // the derivation pass recurses — a desugar hiding under a
        // Field obj is censused like any other
        Expr::Field { obj, .. } => census_expr(obj),
        Expr::Index { obj, key, .. } => {
            census_expr(obj);
            census_expr(key);
        }
        Expr::BinaryOp { left, right, .. } => {
            census_expr(left);
            census_expr(right);
        }
        Expr::UnaryOp { expr, .. } => census_expr(expr),
        Expr::Call { callee, args, .. } => {
            census_expr(callee);
            for a in args {
                census_expr(a);
            }
        }
        _ => {}
    }
}
