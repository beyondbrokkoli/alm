//! The one compile pipeline (H10): source — or a pre-lexed token
//! stream — to `.ll` text, every phase the driver runs in order. Until
//! this fold the property harness carried a second, hand-maintained
//! copy of the walk (no ffi gate, no `references_arg`, no EntryKind
//! decision), so its batteries proved byte-identical locks for a
//! pipeline that was not quite the shipped one. Both callers converge
//! here: the driver passes its flags plus the canonicalized source
//! path with `walk_pins: true`; the harness passes `standalone: false`
//! with "property_case.lua" (EntryKind stays Lib, so its emitted bytes
//! are unchanged) and thereby GAINS the ffi gate the shipped path
//! always had — that surfaced drift is the fold's own dividend, pinned
//! in the property tests.
//!
//! No I/O lives here: file reads, `fail_build`, the `.ll` write,
//! clang, and the boundary host stay in main.rs; catch_unwind stays
//! test-side (the harness wraps these calls).

use crate::analysis;
use crate::ast::{self, Stmt};
use crate::backend;
use crate::diag::Diagnostic;
use crate::ir;
use crate::lexer;
use crate::lowerer;
use crate::parser::Parser;
use crate::shape;
use logos::Logos;

/// The knobs that name the two callers. The driver fills this from its
/// flags; the property harness fixes `standalone: false` and
/// "property_case.lua" so its artifact bytes are exactly its pre-fold
/// ones, flipping only `walk_pins` for the differential leg.
pub struct PipelineOpts {
    pub standalone: bool,
    pub source_file: std::path::PathBuf,
    pub walk_pins: bool,
}

/// Which phase rejected the source — the pipeline's only public error
/// shape. `Panicked` exists for the test-side catch_unwind wrappers
/// (the shipped driver diagnoses, never crashes, so it never sees one).
#[derive(Debug)]
pub enum Stage {
    #[cfg(test)]
    Panicked,
    Front,
    Ffi,
    Analyze,
    Lower,
    Backend,
}

impl Stage {
    #[cfg(test)]
    pub fn name(&self) -> &'static str {
        match self {
            Stage::Panicked => "panicked",
            Stage::Front => "front (lexer/parser)",
            Stage::Ffi => "ffi gate (exe-only surface)",
            Stage::Analyze => "shape analyzer + checker (one walk)",
            Stage::Lower => "lowerer",
            Stage::Backend => "backend",
        }
    }
}

/// The .so-mode refusal, verbatim the pre-fold driver text (probes pin
/// it by substring).
const FFI_EXE_ONLY: &str = "alm compiler error: the ffi surface (require(\"ffi\") / ffi.load / \
                            lib.sym) is --exe-only — rebuild with --exe; a shared object loading \
                            shared objects is not acyclic destiny";

/// The shipped compile: lex → parse → front gate → ffi gate → one walk
/// → lower → render, returning the `.ll` text or the rejecting stage
/// with its diagnostics.
pub fn compile(source: &str, opts: &PipelineOpts) -> Result<String, (Stage, Vec<Diagnostic>)> {
    let mut tokens = Vec::new();
    let mut offsets = Vec::new();
    let mut front_diagnostics: Vec<Diagnostic> = Vec::new();
    let mut lexer = lexer::Token::lexer(source);
    loop {
        match lexer.next() {
            Some(Ok(token)) => {
                offsets.push(lexer.span().start);
                tokens.push(token);
            }
            Some(Err(_)) => {
                let line = 1 + source.as_bytes()[..lexer.span().start]
                    .iter()
                    .filter(|b| **b == b'\n')
                    .count();
                // a lexer error LATCHES: the truncated stream still
                // parses, and both halves reject together at the gate
                // kind Syntax is the front gate's face — the bytes
                // stay the driver's ("Syntax Error: Lexer error")
                front_diagnostics.push(Diagnostic::syntax("Lexer error").with_site(Some(line)));
                break;
            }
            None => break,
        }
    }

    let mut parser = Parser::new(tokens.into_iter().zip(offsets).collect(), source);
    let ast = parser.parse_program();
    front_diagnostics.extend(parser.diagnostics);

    if !front_diagnostics.is_empty() {
        return Err((Stage::Front, front_diagnostics));
    }

    post_front(ast, opts)
}

/// The pipeline from a pre-lexed token stream — the token-soup fuzz leg
/// feeds mutated token vectors in here directly (offsets stay valid
/// byte indices of the same source, so diagnostics remain sound). No
/// lexer diagnostics can exist on this path.
#[cfg(test)]
pub fn compile_parts(
    tokens: Vec<(lexer::Token<'_>, usize)>,
    source: &str,
    opts: &PipelineOpts,
) -> Result<String, (Stage, Vec<Diagnostic>)> {
    let mut parser = Parser::new(tokens, source);
    let ast = parser.parse_program();
    if !parser.diagnostics.is_empty() {
        return Err((Stage::Front, parser.diagnostics));
    }
    post_front(ast, opts)
}

/// Everything past the front gate: the ffi gate, the one walk, the
/// lowerer, and the backend — the half both callers always shared.
fn post_front(ast: Vec<Stmt>, opts: &PipelineOpts) -> Result<String, (Stage, Vec<Diagnostic>)> {
    if uses_ffi(&ast) && !opts.standalone {
        return Err((Stage::Ffi, vec![Diagnostic::bare(FFI_EXE_ONLY)]));
    }

    let ctx = analysis::build_context(&ast);

    // one walk: the shape analyzer's recorded pass IS the checker (the
    // fold) — analyze returns the complete fact set plus diagnostics
    let shape = shape::analyze_with(&ctx, opts.walk_pins);
    if !shape.diagnostics.is_empty() {
        return Err((Stage::Analyze, shape.diagnostics));
    }

    let mut ir_lowerer = lowerer::IrLowerer::new(&shape, ctx.stmt_locs);
    let mut ir_program = ir_lowerer.lower_program(&ast);
    if !ir_lowerer.diagnostics.is_empty() {
        return Err((Stage::Lower, ir_lowerer.diagnostics));
    }

    ir_program.source_file = opts.source_file.clone();
    if opts.standalone {
        ir_program.entry = ir::EntryKind::Exe {
            args: references_arg(&ast),
        };
    }

    backend::generate_llvm_ir(&ir_program).map_err(|d| (Stage::Backend, d))
}

fn references_arg(stmts: &[Stmt]) -> bool {
    fn expr(e: &ast::Expr) -> bool {
        match e {
            ast::Expr::Identifier(name) => name == "arg",
            ast::Expr::TableCtor { entries, .. } => entries
                .iter()
                .any(|(k, v)| matches!(k, ast::CtorKey::Expr(ke) if expr(ke)) || expr(v)),
            ast::Expr::Index { obj, key } => expr(obj) || expr(key),
            ast::Expr::BinaryOp { left, right, .. } => expr(left) || expr(right),
            ast::Expr::UnaryOp { expr: inner, .. } => expr(inner),
            ast::Expr::Call { callee, args } => expr(callee) || args.iter().any(expr),
            ast::Expr::Function { body, .. } => go(body),
            ast::Expr::Integer(_)
            | ast::Expr::Float(_)
            | ast::Expr::Boolean(_)
            | ast::Expr::String(_)
            | ast::Expr::Nil
            | ast::Expr::SysAllocCount
            | ast::Expr::SysExecCount
            | ast::Expr::FfiModule
            | ast::Expr::CoroModule => false,
            ast::Expr::Field { obj, .. } => expr(obj),
        }
    }
    fn go(stmts: &[Stmt]) -> bool {
        stmts.iter().any(|s| match s {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => exprs.iter().any(expr),
            Stmt::Assignment { expr: value, .. } => expr(value),
            Stmt::IndexAssign {
                obj, key, value, ..
            } => expr(obj) || expr(key) || expr(value),
            Stmt::While {
                condition, body, ..
            } => expr(condition) || go(body),
            Stmt::Do { body, .. } => go(body),
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => expr(condition) || go(then_body) || go(else_body),
            Stmt::Expr { expr: inner, .. } => expr(inner),
            Stmt::Return { value, .. } => value.as_ref().is_some_and(expr),
            Stmt::Break { .. } => false,
        })
    }
    go(stmts)
}

fn uses_ffi(stmts: &[Stmt]) -> bool {
    fn expr(e: &ast::Expr) -> bool {
        match e {
            ast::Expr::FfiModule => true,
            ast::Expr::Field { obj, .. } => expr(obj),
            ast::Expr::TableCtor { entries, .. } => entries
                .iter()
                .any(|(k, v)| matches!(k, ast::CtorKey::Expr(ke) if expr(ke)) || expr(v)),
            ast::Expr::Index { obj, key } => expr(obj) || expr(key),
            ast::Expr::BinaryOp { left, right, .. } => expr(left) || expr(right),
            ast::Expr::UnaryOp { expr: inner, .. } => expr(inner),
            ast::Expr::Call { callee, args } => expr(callee) || args.iter().any(expr),
            ast::Expr::Function { body, .. } => go(body),
            ast::Expr::Integer(_)
            | ast::Expr::Float(_)
            | ast::Expr::Boolean(_)
            | ast::Expr::String(_)
            | ast::Expr::Nil
            | ast::Expr::SysAllocCount
            | ast::Expr::SysExecCount
            | ast::Expr::CoroModule
            | ast::Expr::Identifier(_) => false,
        }
    }
    fn go(stmts: &[Stmt]) -> bool {
        stmts.iter().any(|s| match s {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => exprs.iter().any(expr),
            Stmt::Assignment { expr: value, .. } => expr(value),
            Stmt::IndexAssign {
                obj, key, value, ..
            } => expr(obj) || expr(key) || expr(value),
            Stmt::While {
                condition, body, ..
            } => expr(condition) || go(body),
            Stmt::Do { body, .. } => go(body),
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => expr(condition) || go(then_body) || go(else_body),
            Stmt::Expr { expr: inner, .. } => expr(inner),
            Stmt::Return { value, .. } => value.as_ref().is_some_and(expr),
            Stmt::Break { .. } => false,
        })
    }
    go(stmts)
}
