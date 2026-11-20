//! The require splice (M3): dotted requires resolve against
//! `--module-root` and amalgamate into the one AST everything
//! downstream already walks.
//!
//! `local M = require("a.b")` disappears as a statement: the module's
//! chunk is parsed, its own requires spliced the same way, its
//! `function T.f(...)` sugar desugared into the p26 pattern (hoisted
//! local function + record-literal field), and the whole chunk is
//! wrapped as a zero-parameter local function called exactly once:
//!
//! ```text
//! -- root preamble, one pair per module, DFS first-require order
//! local mod$fn$0 = function() <module chunk> end
//! local mod$ret$0 = mod$fn$0()
//! -- every require site: the binding is renamed to mod$ret$0 for the
//! -- rest of its chunk (scope-aware, shadowing honored)
//! ```
//!
//! Lua chunk semantics fall out of the wrapper: the module body is a
//! function scope, so the requirer's locals are invisible and only
//! the returned table binds. Memoization is by resolved path — the
//! pair is minted once in the preamble and every site (root or
//! nested, first or later) renames to the one cache name, so
//! top-level effects run exactly once and every requirer sees the
//! same table. The preamble placement is forced by the checking
//! order, not chosen: a module first required inside another module
//! is inlined at its wrapper's preamble call, so anything it
//! references must already live in the preamble — and one uniform
//! rule beats two. The recursion diagnostic's voice one level up
//! rejects require cycles by name; the DAG law does the lifting.

use crate::ast::{CtorKey, Expr, Loc, NodeId, Stmt};
use crate::diag::Diagnostic;
use crate::surface::Surface;
use crate::visit::{self, Visitor};
use crate::{lexer, parser};
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;
use std::path::{Path, PathBuf};

struct Expander {
    /// [surface] The resolved surface rides the splice so nested
    /// module chunks parse under the same laws as their requirer
    /// (mirror fanned these through `RequireOpts`; P3's cure is the
    /// one `&Surface` parameter).
    surface: Surface,
    /// Where dotted requires anchor (`--module-root`, pipeline
    /// configuration — a filesystem tree, not a law; it lives outside
    /// `Surface` by design).
    module_root: Option<PathBuf>,
    /// resolved module path -> cache binding name
    cache: BTreeMap<PathBuf, String>,
    /// the modules currently being expanded: resolved paths for the
    /// law, dotted spellings for the cycle's chain message
    stack: Vec<(PathBuf, String)>,
    counter: usize,
    /// root-level statements ahead of the main chunk: one [fn decl,
    /// cache call] pair per module, in first-require order
    preamble: Vec<Stmt>,
    diags: Vec<Diagnostic>,
}

/// Expand every legal require in `stmts` (the main chunk). Returns
/// the amalgamated program on success; otherwise the named
/// diagnostics.
pub fn expand(
    stmts: Vec<Stmt>,
    surface: &Surface,
    module_root: Option<&Path>,
) -> Result<Vec<Stmt>, Vec<Diagnostic>> {
    let mut ex = Expander {
        surface: *surface,
        module_root: module_root.map(Path::to_path_buf),
        cache: BTreeMap::new(),
        stack: Vec::new(),
        counter: 0,
        preamble: Vec::new(),
        diags: Vec::new(),
    };
    let mut body = ex.splice_chunk(stmts);
    if ex.diags.is_empty() {
        let mut whole = std::mem::take(&mut ex.preamble);
        whole.append(&mut body);
        ex.census(&whole);
        if ex.diags.is_empty() {
            return Ok(whole);
        }
    }
    Err(ex.diags)
}

impl Expander {
    /// One chunk's top-level statements. A require site vanishes; its
    /// binding name is renamed to the module's cache name for the
    /// rest of the chunk.
    fn splice_chunk(&mut self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        let mut out = Vec::with_capacity(stmts.len());
        let mut renames: Vec<(String, String)> = Vec::new();
        for mut stmt in stmts {
            match self.take_require_site(&mut stmt) {
                Ok(Some((user, path, loc))) => match self.module(&path, loc) {
                    Ok(cache_name) => {
                        renames.retain(|(from, _)| from != &user);
                        renames.push((user, cache_name));
                    }
                    Err(d) => self.diags.push(d),
                },
                Ok(None) => {
                    if !renames.is_empty() {
                        for (from, to) in &renames {
                            rename_in_stmt(&mut stmt, from, to);
                        }
                        renames.retain(|(from, _)| !stmt_declares(&stmt, from));
                    }
                    out.push(stmt);
                }
                Err(d) => self.diags.push(d),
            }
        }
        out
    }

    /// If `stmt` is the require shape (`local M = require("p")`,
    /// one name, one expr), take its binding name and path and leave
    /// `stmt` emptied for removal. Err on the near shapes that need a
    /// named rejection instead.
    fn take_require_site(
        &mut self,
        stmt: &mut Stmt,
    ) -> Result<Option<(String, String, Loc)>, Diagnostic> {
        let Stmt::LocalDecl {
            names, exprs, loc, ..
        } = stmt
        else {
            return Ok(None);
        };
        if !is_require_call(exprs.first()) {
            // a require embedded in a larger expression, or sitting in
            // a nested block, is not this site — the census names every
            // one the splice left behind
            return Ok(None);
        }
        let (user, path) = {
            let Expr::Call { args, .. } = &exprs[0] else {
                unreachable!("the guard matched a require call");
            };
            let Expr::String { value, .. } = &args[0] else {
                unreachable!("a require call carries one string literal");
            };
            if names.len() != 1 || exprs.len() != 1 {
                return Err(Diagnostic::ty(
                    "require binds one name — 'local M = \
                     require(\"dotted.path\")' is the whole shape",
                )
                .with_site(Some(loc.line as usize)));
            }
            (names[0].clone(), value.clone())
        };
        names.clear();
        exprs.clear();
        Ok(Some((user, path, *loc)))
    }

    /// Resolve `path` against --module-root and splice its chunk into
    /// the preamble, minting the wrapper pair. A cached module
    /// returns its cache name — the site renames to it.
    fn module(&mut self, path: &str, loc: Loc) -> Result<String, Diagnostic> {
        if path == "bit" {
            return Err(Diagnostic::ty(
                "require(\"bit\") — the bit lane is M5 (checker Int \
                 builtins with the LuaJIT bit semantics); until it \
                 lands the dialect has no bit",
            )
            .with_site(Some(loc.line as usize)));
        }
        let Some(root) = self.module_root.clone() else {
            return Err(Diagnostic::ty(format!(
                "require(\"{path}\") — dotted requires resolve against \
                 --module-root; the flag anchors the module tree and this \
                 compile carries none",
            ))
            .with_site(Some(loc.line as usize)));
        };
        let segs: Vec<&str> = path.split('.').collect();
        if !segs.iter().all(|s| {
            !s.is_empty()
                && s.chars()
                    .next()
                    .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        }) {
            return Err(Diagnostic::ty(format!(
                "require(\"{path}\") — module paths are dotted names \
                 (runtime.services.memory), never filesystem spellings",
            ))
            .with_site(Some(loc.line as usize)));
        }
        let mut file = root;
        for seg in &segs[..segs.len() - 1] {
            file.push(seg);
        }
        file.push(format!("{}.lua", segs[segs.len() - 1]));
        let resolved = std::fs::canonicalize(&file).unwrap_or_else(|_| file.clone());
        if let Some(cache_name) = self.cache.get(&resolved).cloned() {
            return Ok(cache_name);
        }
        if self.stack.iter().any(|(p, _)| p == &resolved) {
            let chain: Vec<String> = self
                .stack
                .iter()
                .map(|(_, s)| s.clone())
                .chain(std::iter::once(path.to_string()))
                .collect();
            return Err(Diagnostic::ty(format!(
                "require cycle: {} — modules inline at their require \
                 sites, so a module chain may not reach back into itself",
                chain.join(" -> ")
            ))
            .with_site(Some(loc.line as usize)));
        }
        let source = std::fs::read_to_string(&file).map_err(|_| {
            Diagnostic::ty(format!(
                "require(\"{path}\") — no module at {} (--module-root \
                 anchors the tree; one file per dotted name)",
                file.display(),
            ))
            .with_site(Some(loc.line as usize))
        })?;
        let chunk = parse_module(&source, &self.surface).map_err(|ds| {
            for d in &ds {
                self.diags
                    .push(Diagnostic::ty(format!("module '{path}': {}", d.text)).with_site(d.site));
            }
            Diagnostic::ty(format!(
                "module '{path}' does not parse — the splice refuses \
                 to inline a chunk the front rejects",
            ))
            .with_site(Some(loc.line as usize))
        })?;
        let Some(Stmt::Return { value: Some(_), .. }) = chunk.last() else {
            return Err(Diagnostic::ty(format!(
                "module '{path}' returns nothing — a module's top-level \
                 'return <table>' is the binding its requirers receive",
            ))
            .with_site(Some(loc.line as usize)));
        };
        self.stack.push((resolved.clone(), path.to_string()));
        // a module fn that references its own table cannot ride the
        // record literal (the closure would need the table before the
        // constructor exists) — name it now instead of letting the
        // field call die downstream with a surface error
        for stmt in &chunk {
            if let Stmt::Assignment { name, expr, .. } = stmt
                && matches!(expr, Expr::Function { .. })
            {
                let parts: Vec<&str> = name.split('.').collect();
                if parts.len() == 2 && body_names_table(expr, parts[0]) {
                    self.stack.pop();
                    return Err(Diagnostic::ty(format!(
                        "module '{path}': 'function {}.{}' references \
                         '{}' — a self-referential module function is the \
                         closed-vtable lane's customer, not M3's; spell the \
                         state as captured locals between the functions",
                        parts[0], parts[1], parts[0],
                    ))
                    .with_site(Some(loc.line as usize)));
                }
            }
        }
        let chunk = p26_desugar(chunk, &mut self.counter);
        let body = self.splice_chunk(chunk);
        self.stack.pop();
        let i = self.counter;
        self.counter += 1;
        let fn_name = format!("mod$fn${i}");
        let cache_name = format!("mod$ret${i}");
        self.preamble.push(Stmt::LocalDecl {
            names: vec![fn_name.clone()],
            exprs: vec![Expr::Function {
                params: Vec::new(),
                body,
                id: NodeId::mint(),
            }],
            loc,
            id: NodeId::mint(),
        });
        self.preamble.push(Stmt::LocalDecl {
            names: vec![cache_name.clone()],
            exprs: vec![Expr::Call {
                callee: Box::new(Expr::Identifier {
                    name: fn_name,
                    id: NodeId::mint(),
                }),
                args: Vec::new(),
                id: NodeId::mint(),
            }],
            loc,
            id: NodeId::mint(),
        });
        self.cache.insert(resolved, cache_name.clone());
        // (trace receipt: mirror pokes TRACE_REQUIRE_SPLICE here; the
        // signal layer re-adds it.)
        Ok(cache_name)
    }

    /// Name every require the splice did not expand — the ones inside
    /// functions, nested blocks, and any other non-chunk position.
    fn census(&mut self, stmts: &[Stmt]) {
        struct LeftoverRequire {
            line: Option<usize>,
            hits: Vec<usize>,
        }
        impl Visitor for LeftoverRequire {
            type Break = Infallible;
            fn enter_stmt(&mut self, stmt: &Stmt) -> Result<(), Self::Break> {
                self.line = Some(stmt.loc().line as usize);
                Ok(())
            }
            fn visit_call(
                &mut self,
                callee: &Expr,
                _args: &[Expr],
                _id: NodeId,
            ) -> Result<(), Self::Break> {
                if matches!(callee, Expr::Identifier { name, .. } if name == "require")
                    && let Some(line) = self.line
                {
                    self.hits.push(line);
                }
                visit::walk_expr(self, callee)
            }
        }
        let mut v = LeftoverRequire {
            line: None,
            hits: Vec::new(),
        };
        let _ = visit::walk_stmts(&mut v, stmts);
        for line in v.hits {
            self.diags.push(
                Diagnostic::ty(
                    "require is top-level-only and binds a fresh local — \
                     'local M = require(\"dotted.path\")'; a site inside a \
                     function or nested block has no chunk of its own",
                )
                .with_site(Some(line)),
            );
        }
    }
}

fn is_require_call(expr: Option<&Expr>) -> bool {
    matches!(
        expr,
        Some(Expr::Call { callee, args, .. })
            if matches!(callee.as_ref(), Expr::Identifier { name, .. } if name == "require")
                && args.len() == 1
                && matches!(args.first(), Some(Expr::String { .. }))
    )
}

// -- the p26 desugar: `function T.f(...)` inside a module chunk
// becomes the pattern the engine probes already hand-write — a
// hoisted local function plus the field in the table's constructor
// literal, the only lane a closure may enter a record by.

fn ident_ok(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn p26_desugar(stmts: Vec<Stmt>, name_counter: &mut usize) -> Vec<Stmt> {
    // one-dot fn sugar over a function literal, keyed by its stmt
    // index; a fn body referencing its own table stays put (a forward
    // reference the dialect refuses — it keeps its in-chunk
    // dotted-binding semantics instead)
    let mut sugar: BTreeMap<usize, (String, String)> = BTreeMap::new();
    let mut fn_exprs: BTreeMap<usize, Expr> = BTreeMap::new();
    for (idx, stmt) in stmts.iter().enumerate() {
        if let Stmt::Assignment { name, expr, .. } = stmt
            && matches!(expr, Expr::Function { .. })
        {
            let parts: Vec<&str> = name.split('.').collect();
            if parts.len() == 2
                && parts.iter().all(|p| ident_ok(p))
                && !body_names_table(expr, parts[0])
            {
                sugar.insert(idx, (parts[0].to_string(), parts[1].to_string()));
                fn_exprs.insert(idx, expr.clone());
            }
        }
    }
    // the constructor each sugared table binds at chunk top level
    // (first literal wins; a table with no literal keeps its sugars)
    let mut ctor_idx: BTreeMap<String, usize> = BTreeMap::new();
    for (idx, stmt) in stmts.iter().enumerate() {
        if let Stmt::LocalDecl { names, exprs, .. } = stmt
            && names.len() == 1
            && matches!(exprs.first(), Some(Expr::TableCtor { .. }))
            && sugar.values().any(|(t, ..)| t == &names[0])
        {
            ctor_idx.entry(names[0].clone()).or_insert(idx);
        }
    }
    // ctor decl idx -> [(field, hoisted name, sugar stmt idx)]
    let mut hoist_plan: BTreeMap<usize, Vec<(String, String, usize)>> = BTreeMap::new();
    for (&idx, (table, field)) in &sugar {
        if let Some(&ci) = ctor_idx.get(table) {
            let name = format!("mod$sugar${}", *name_counter);
            *name_counter += 1;
            hoist_plan
                .entry(ci)
                .or_default()
                .push((field.clone(), name, idx));
        }
    }
    if hoist_plan.is_empty() {
        return stmts;
    }
    let mut out: Vec<Stmt> = Vec::with_capacity(stmts.len() + 4);
    let mut consumed: BTreeSet<usize> = BTreeSet::new();
    for (idx, mut stmt) in stmts.into_iter().enumerate() {
        if let Some(fields) = hoist_plan.get(&idx) {
            let loc = stmt.loc();
            // hoist each fn literal just ahead of the constructor —
            // after every name the chunk declared before it, so no
            // forward reference is minted
            for (_, hoisted, sugar_idx) in fields {
                let expr = fn_exprs.remove(sugar_idx).expect("the sugar map held it");
                consumed.insert(*sugar_idx);
                out.push(Stmt::LocalDecl {
                    names: vec![hoisted.clone()],
                    exprs: vec![expr],
                    loc,
                    id: NodeId::mint(),
                });
            }
            // the constructor gains the closure fields — the one lane
            // a closure may enter a record by
            if let Stmt::LocalDecl { exprs, .. } = &mut stmt
                && let Expr::TableCtor { entries, .. } = &mut exprs[0]
            {
                for (field, hoisted, _) in fields {
                    entries.push((
                        CtorKey::Str(field.clone()),
                        Expr::Identifier {
                            name: hoisted.clone(),
                            id: NodeId::mint(),
                        },
                    ));
                }
            }
            out.push(stmt);
            continue;
        }
        if consumed.contains(&idx) {
            // the sugar statement itself — its fn literal was hoisted
            continue;
        }
        out.push(stmt);
    }
    out
}
/// crude, conservative: does the fn body mention the table name at
/// all (shadowing ignored — a false positive only skips the desugar)
fn body_names_table(expr: &Expr, table: &str) -> bool {
    struct Find(bool, String);
    impl Visitor for Find {
        type Break = Infallible;
        fn visit_identifier(&mut self, name: &str, _id: NodeId) -> Result<(), Self::Break> {
            if name == self.1 {
                self.0 = true;
            }
            Ok(())
        }
    }
    let mut f = Find(false, table.to_string());
    let _ = visit::walk_expr(&mut f, expr);
    f.0
}

// -- the renamer: after a require site, the binding's name becomes
// the module's cache name for the rest of its chunk. Scope-aware:
// a redeclaration of the name shadows the rename from that point on,
// and function parameters shadow inside their bodies.

fn stmt_declares(stmt: &Stmt, name: &str) -> bool {
    match stmt {
        Stmt::LocalDecl { names, .. } => names.iter().any(|n| n == name),
        _ => false,
    }
}

fn rename_in_stmts(stmts: &mut [Stmt], from: &str, to: &str) {
    let mut shadowed = false;
    for s in stmts {
        if shadowed {
            return;
        }
        rename_in_stmt(s, from, to);
        if stmt_declares(s, from) {
            shadowed = true;
        }
    }
}

fn rename_in_stmt(stmt: &mut Stmt, from: &str, to: &str) {
    match stmt {
        Stmt::LocalDecl { exprs, .. } => {
            for e in exprs {
                rename_in_expr(e, from, to);
            }
        }
        Stmt::Assignment { expr, .. } => rename_in_expr(expr, from, to),
        Stmt::IndexAssign {
            obj, key, value, ..
        } => {
            rename_in_expr(obj, from, to);
            rename_in_expr(key, from, to);
            rename_in_expr(value, from, to);
        }
        Stmt::While {
            condition, body, ..
        } => {
            rename_in_expr(condition, from, to);
            rename_in_stmts(body, from, to);
        }
        Stmt::Do { body, .. } => rename_in_stmts(body, from, to),
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            rename_in_expr(condition, from, to);
            rename_in_stmts(then_body, from, to);
            rename_in_stmts(else_body, from, to);
        }
        Stmt::Print { exprs, .. } => {
            for e in exprs {
                rename_in_expr(e, from, to);
            }
        }
        Stmt::Expr { expr, .. } => rename_in_expr(expr, from, to),
        Stmt::Return { value, .. } => {
            if let Some(e) = value {
                rename_in_expr(e, from, to);
            }
        }
        Stmt::Break { .. } => {}
    }
}

fn rename_in_expr(expr: &mut Expr, from: &str, to: &str) {
    match expr {
        Expr::Identifier { name, .. } => {
            if name == from {
                *name = to.to_string();
            }
        }
        Expr::Function { params, body, .. } => {
            if !params.iter().any(|p| p == from) {
                rename_in_stmts(body, from, to);
            }
        }
        Expr::TableCtor { entries, .. } => {
            for (k, e) in entries.iter_mut() {
                if let CtorKey::Expr(ke) = k {
                    rename_in_expr(ke, from, to);
                }
                rename_in_expr(e, from, to);
            }
        }
        Expr::Index { obj, key, .. } => {
            rename_in_expr(obj, from, to);
            rename_in_expr(key, from, to);
        }
        Expr::BinaryOp { left, right, .. } => {
            rename_in_expr(left, from, to);
            rename_in_expr(right, from, to);
        }
        Expr::UnaryOp { expr, .. } => rename_in_expr(expr, from, to),
        Expr::Field { obj, .. } => rename_in_expr(obj, from, to),
        Expr::Call { callee, args, .. } => {
            rename_in_expr(callee, from, to);
            for a in args {
                rename_in_expr(a, from, to);
            }
        }
        Expr::Integer { .. }
        | Expr::Float { .. }
        | Expr::Boolean { .. }
        | Expr::String { .. }
        | Expr::Nil { .. }
        | Expr::SysAllocCount { .. }
        | Expr::SysExecCount { .. }
        | Expr::FfiModule { .. }
        | Expr::AsyncModule { .. } => {}
    }
}

fn parse_module(source: &str, surface: &Surface) -> Result<Vec<Stmt>, Vec<Diagnostic>> {
    let src = crate::source::SourceFile::new("<module>", source);
    let out = lexer::lex(&src);
    let mut diagnostics = Vec::new();
    if let Some(err) = &out.error {
        diagnostics.push(Diagnostic::syntax(err.text.clone()).with_site(Some(err.line)));
    }
    let tokens = out
        .tokens
        .into_iter()
        .map(|(t, span)| (t, span.start))
        .collect();
    let mut parser = parser::Parser::new(tokens, &src, surface);
    let ast = parser.parse_program();
    diagnostics.extend(parser.diagnostics);
    if diagnostics.is_empty() {
        Ok(ast)
    } else {
        Err(diagnostics)
    }
}
