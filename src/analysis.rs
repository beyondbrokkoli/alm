use crate::ast::{Expr, Loc, NodeId, Stmt};
use crate::visit::{self, Visitor};
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;

pub struct AnalysisContext<'a> {
    pub sites: BTreeMap<NodeId, usize>,
    pub ast: &'a [Stmt],
    pub ctor_lines: Vec<usize>,
    pub fn_touched: BTreeMap<NodeId, BTreeSet<String>>,
}

pub fn build_context<'a>(ast: &'a [Stmt]) -> AnalysisContext<'a> {
    let mut pass = Derivation::new();
    let _ = visit::walk_stmts(&mut pass, ast);
    let _ = visit::walk_stmts(&mut DesugarCensus, ast);

    AnalysisContext {
        sites: pass.sites,
        ast,
        ctor_lines: pass.ctor_lines,
        fn_touched: pass.fn_touched,
    }
}

struct Derivation {
    sites: BTreeMap<NodeId, usize>,
    ctor_lines: Vec<usize>,
    fn_touched: BTreeMap<NodeId, BTreeSet<String>>,
    seen: BTreeSet<NodeId>,
    scopes: Vec<BTreeSet<String>>,
    current_fn: Option<FnScan>,
}

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
            current_fn: None,
        }
    }
}

impl Visitor for Derivation {
    type Break = Infallible;

    fn enter_stmt(&mut self, stmt: &Stmt) -> Result<(), Self::Break> {
        assert!(
            self.seen.insert(stmt.id()),
            "identity census (H6): stmt id {} appears twice — a cloned subtree \
             reached the tree; one construction mints one node, a re-materialized \
             subtree must be constructed, never cloned",
            stmt.id().0
        );
        Ok(())
    }

    fn enter_expr(&mut self, expr: &Expr) -> Result<(), Self::Break> {
        assert!(
            self.seen.insert(expr.id()),
            "identity census (H6): expr id {} appears twice — a cloned subtree \
             reached the tree; one construction mints one node, a re-materialized \
             subtree must be constructed, never cloned",
            expr.id().0
        );
        if let Expr::TableCtor { line, .. } = expr {
            self.sites.insert(expr.id(), self.sites.len());
            self.ctor_lines.push(*line as usize);
        }
        // An ffi.new mint is a table construction for the ownership
        // walk's purposes — it gets a site here like any ctor, so the
        // minted buffer is an ordinary owner-binding (W4 §1.5). A
        // `.new` dotted call whose base is not the ffi module never
        // reaches the mint lane, and its phantom site is inert.
        if let Expr::Call { callee, .. } = expr
            && let Expr::Field { obj, name, .. } = callee.as_ref()
            && name == "new"
            && matches!(obj.as_ref(), Expr::Identifier { .. })
            && !self.sites.contains_key(&expr.id())
        {
            self.sites.insert(expr.id(), self.sites.len());
            self.ctor_lines.push(0);
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
            visit::walk_expr(self, e)?;
        }
        self.scopes
            .last_mut()
            .unwrap()
            .extend(names.iter().cloned());
        Ok(())
    }

    fn visit_assignment(
        &mut self,
        name: &str,
        expr: &Expr,
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        record_touched(&mut self.current_fn, &self.scopes, name);
        visit::walk_expr(self, expr)
    }

    fn visit_index_assign(
        &mut self,
        obj: &Expr,
        key: &Expr,
        value: &Expr,
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        if let Some(base) = base_identifier(obj) {
            record_touched(&mut self.current_fn, &self.scopes, base);
        }
        visit::walk_expr(self, obj)?;
        visit::walk_expr(self, key)?;
        visit::walk_expr(self, value)
    }

    fn visit_while(
        &mut self,
        condition: &Expr,
        body: &[Stmt],
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        visit::walk_expr(self, condition)?;
        self.scopes.push(Default::default());
        let r = visit::walk_stmts(self, body);
        self.scopes.pop();
        r
    }

    fn visit_do(&mut self, body: &[Stmt], _loc: Loc, _id: NodeId) -> Result<(), Self::Break> {
        self.scopes.push(Default::default());
        let r = visit::walk_stmts(self, body);
        self.scopes.pop();
        r
    }

    fn visit_if(
        &mut self,
        condition: &Expr,
        then_body: &[Stmt],
        else_body: &[Stmt],
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        visit::walk_expr(self, condition)?;
        self.scopes.push(Default::default());
        let r = visit::walk_stmts(self, then_body);
        self.scopes.pop();
        r?;
        self.scopes.push(Default::default());
        let r = visit::walk_stmts(self, else_body);
        self.scopes.pop();
        r
    }

    fn visit_function(
        &mut self,
        params: &[String],
        body: &[Stmt],
        id: NodeId,
    ) -> Result<(), Self::Break> {
        let entry_depth = self.scopes.len();
        self.scopes.push(params.iter().cloned().collect());
        let mut outer = self.current_fn.take();
        self.current_fn = Some(FnScan {
            entry_depth,
            touched: BTreeSet::new(),
        });
        let _ = visit::walk_stmts(self, body);
        let inner = self.current_fn.take().unwrap();
        self.scopes.pop();
        if let Some(o) = outer.as_mut() {
            o.touched.extend(inner.touched.iter().cloned());
        }
        self.fn_touched.insert(id, inner.touched);
        self.current_fn = outer;
        Ok(())
    }
}

fn record_touched(current_fn: &mut Option<FnScan>, scopes: &[BTreeSet<String>], name: &str) {
    if let Some(scan) = current_fn
        && !scopes[scan.entry_depth..].iter().any(|s| s.contains(name))
    {
        scan.touched.insert(name.to_string());
    }
}

fn base_identifier(expr: &Expr) -> Option<&String> {
    // C: index-chain classifier, not a traversal — recursion is only down
    // the obj spine of an Index; every other Expr has no base to name.
    match expr {
        Expr::Identifier { name, .. } => Some(name),
        Expr::Index { obj, .. } => base_identifier(obj),
        // leaves and operators never form an lvalue base
        Expr::Integer { .. }
        | Expr::Float { .. }
        | Expr::Boolean { .. }
        | Expr::String { .. }
        | Expr::Nil { .. }
        | Expr::TableCtor { .. }
        | Expr::BinaryOp { .. }
        | Expr::UnaryOp { .. }
        | Expr::SysAllocCount { .. }
        | Expr::SysExecCount { .. }
        | Expr::FfiModule { .. }
        | Expr::AsyncModule { .. }
        | Expr::Field { .. }
        | Expr::Function { .. }
        | Expr::Call { .. } => None,
    }
}

struct DesugarCensus;

impl Visitor for DesugarCensus {
    type Break = Infallible;

    fn enter_stmt(&mut self, s: &Stmt) -> Result<(), Self::Break> {
        for_desugar_header_check(s);
        tuple_assign_check(s);
        Ok(())
    }
}

fn for_desugar_header_check(s: &Stmt) {
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
}

fn tuple_assign_check(s: &Stmt) {
    // The fingerprint is the namespace itself: '$' never lexes in a
    // source identifier, so a block opening on a tuple$ decl is the
    // sugar — whichever target latched first (a name target or an
    // inline prefix at index 0 leaves the decl opening on a later
    // target's temp).
    if let Stmt::Do { body, .. } = s
        && matches!(
            body.first(),
            Some(Stmt::LocalDecl { names, .. })
                if names.first().is_some_and(|n| n.starts_with("tuple$"))
        )
    {
        let header = s.loc().line;
        let check = |what: &str, node: &Stmt| {
            let l = node.loc().line;
            if l != header {
                panic!(
                    "tuple-assign attribution drift: the {what} reports line {l} but the \
                     tuple header reports line {header} — every desugared statement must \
                     carry the header's stamp (R7's law, H8's census)"
                );
            }
        };
        let Stmt::LocalDecl { names, .. } = &body[0] else {
            unreachable!("the fingerprint arm matched a LocalDecl")
        };
        // The decl names are the latch block — per target, in target
        // order: optional tuple$o{i} then optional tuple$k{i}, i
        // strictly increasing — followed by the contiguous value tail
        // tuple$t0..tuple$t{m-1}.
        let mut latched: BTreeSet<String> = BTreeSet::new();
        let mut last_idx: Option<usize> = None;
        let mut seen_k = false;
        let mut in_tail = false;
        let mut m = 0usize;
        for name in names {
            let Some((kind, idx)) = name.as_str().strip_prefix("tuple$").and_then(|rest| {
                let mut cs = rest.chars();
                let kind = cs.next()?;
                if !matches!(kind, 'o' | 'k' | 't') {
                    return None;
                }
                Some((kind, cs.as_str().parse::<usize>().ok()?))
            }) else {
                panic!(
                    "tuple-assign census: temp '{name}' does not spell \
                     tuple$o<i>/tuple$k<i>/tuple$t<i> — the desugar shape changed; \
                     update the census with it (H8)"
                );
            };
            if kind == 't' {
                if idx != m {
                    panic!(
                        "tuple-assign census: value temp {m} is named \
                         'tuple$t{idx}' — the desugar shape changed; update the \
                         census with it (H8)"
                    );
                }
                in_tail = true;
                m += 1;
                continue;
            }
            if in_tail {
                panic!(
                    "tuple-assign census: latch temp '{name}' sits after the value \
                     tail — the desugar shape changed; update the census with it (H8)"
                );
            }
            if kind == 'k' && last_idx == Some(idx) && !seen_k {
                seen_k = true; // tuple$o{i} then tuple$k{i} — legal
            } else if Some(idx) > last_idx {
                last_idx = Some(idx);
                seen_k = kind == 'k';
            } else {
                panic!(
                    "tuple-assign census: latch temps out of order at '{name}' — the \
                     desugar shape changed; update the census with it (H8)"
                );
            }
            latched.insert(name.clone());
        }
        check("temp decl", &body[0]);
        if body.len() != m + 1 {
            panic!(
                "tuple-assign census: {m} temps but {} statements in the block — the \
                 desugar shape changed; update the census with it (H8)",
                body.len() - 1
            );
        }
        // The stores run right-to-left: block statement j carries the
        // store for target m-1-j, reading tuple$t{m-1-j}. A cell store
        // reads the target's latch temps exactly where the decl
        // declared them; a name store (T2) rebinds a source name and
        // owns no latch — a name has no prefix to evaluate.
        for (j, stmt) in body[1..].iter().enumerate() {
            let i = m - 1 - j;
            let reads_temp = |value: &Expr| matches!(value, Expr::Identifier { name: v, .. } if v == &format!("tuple$t{i}"));
            match stmt {
                Stmt::IndexAssign {
                    obj, key, value, ..
                } => {
                    if !reads_temp(value) {
                        panic!(
                            "tuple-assign census: store {j} does not read temp {i} — the \
                             desugar shape changed; update the census with it (H8)"
                        );
                    }
                    for (e, want, what) in [(obj, 'o', "obj"), (key, 'k', "key")] {
                        let spelled = format!("tuple${want}{i}");
                        match e {
                            Expr::Identifier { name, .. } if name == &spelled => {
                                if !latched.contains(&spelled) {
                                    panic!(
                                        "tuple-assign census: store {j}'s {what} reads \
                                         '{spelled}' but the decl never latched it — the \
                                         desugar shape changed; update the census with it (H8)"
                                    );
                                }
                            }
                            Expr::Identifier { name, .. } if name.starts_with("tuple$") => {
                                panic!(
                                    "tuple-assign census: store {j}'s {what} reads '{name}', \
                                     not '{spelled}' — the desugar shape changed; update the \
                                     census with it (H8)"
                                );
                            }
                            _ if latched.contains(&spelled) => {
                                panic!(
                                    "tuple-assign census: target {i} latched its {what} but \
                                     store {j} does not read '{spelled}' — the desugar shape \
                                     changed; update the census with it (H8)"
                                );
                            }
                            _ => {}
                        }
                    }
                    check(&format!("cell store {j}"), stmt);
                }
                Stmt::Assignment { name, expr, .. } => {
                    if !reads_temp(expr) {
                        panic!(
                            "tuple-assign census: store {j} does not read temp {i} — the \
                             desugar shape changed; update the census with it (H8)"
                        );
                    }
                    if name.starts_with("tuple$") {
                        panic!(
                            "tuple-assign census: name store {j} rebinds the synthetic \
                             '{name}' — a name store targets a source name; the desugar \
                             shape changed; update the census with it (H8)"
                        );
                    }
                    for want in ['o', 'k'] {
                        let spelled = format!("tuple${want}{i}");
                        if latched.contains(&spelled) {
                            panic!(
                                "tuple-assign census: target {i} is the name '{name}' but \
                                 the decl latched '{spelled}' — a name has no prefix; the \
                                 desugar shape changed; update the census with it (H8)"
                            );
                        }
                    }
                    check(&format!("name store {j}"), stmt);
                }
                _ => panic!(
                    "tuple-assign census: the block's statement {} is neither a cell store \
                     nor a name store — the desugar shape changed; update the census with \
                     it (H8)",
                    j + 1
                ),
            }
        }
    }
}
