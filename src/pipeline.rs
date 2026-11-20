//! The front leg of the pipeline: source → tokens → (desugared) AST →
//! require splice → shape walk.
//!
//! mirror's pipeline.rs @ 87aca4c holds the whole compiler flow in one
//! `compile`; alm grows stage by stage, so this file is that function's
//! front half plus the L3 stages (the Modules splice and the walk-only
//! Analyze). Everything after — the checker interleave, the ffi gate,
//! lower, backend — lands with its layer; nothing is stubbed. No
//! `PipelineOpts` struct ever ports (audit P3): the surface rides
//! `&Surface`, the module root is a plain parameter.

use crate::analysis;
use crate::ast::Stmt;
use crate::diag::Diagnostic;
use crate::lexer;
use crate::parser::Parser;
use crate::require;
use crate::shape;
use crate::source::SourceFile;
use crate::surface::Surface;
use std::path::Path;

pub struct FrontOutput {
    pub ast: Vec<Stmt>,
    pub diagnostics: Vec<Diagnostic>,
}

impl FrontOutput {
    pub fn is_ok(&self) -> bool {
        self.diagnostics.is_empty()
    }
}

/// The refusal tier a compile stopped at. Names are mirror's exact
/// strings — the walk-pin pins assert the Analyze stage's name
/// verbatim, and the (future) parity lanes classify by it. (mirror
/// gates `Panicked`/`name` behind cfg(test) because its harness lives
/// in the binary crate; alm's legs are integration tests, so the
/// variant is plain — the compiler itself never mints it.)
#[derive(Debug)]
pub enum Stage {
    Panicked,
    Front,
    Modules,
    Analyze,
}

impl Stage {
    pub fn name(&self) -> &'static str {
        match self {
            Stage::Panicked => "panicked",
            Stage::Front => "front (lexer/parser)",
            Stage::Modules => "require splice (module amalgamation)",
            Stage::Analyze => "shape analyzer + checker (one walk)",
        }
    }
}

/// Lex + parse + desugar.
///
/// The truncation law, mirror's exactly: a lexer refusal mints its
/// diagnostic and the parser still runs over the truncated stream, so
/// a refusal mid-expression yields the refusal plus a follow-on parse
/// diagnostic (`line N: … Lexer error: …` then `line M: Syntax Error:
/// Expected expression`). The first parse error stops (mirror
/// `parse_program`); a diagnostic-free parse is the L3 handoff shape.
pub fn front(src: &SourceFile, surface: &Surface) -> FrontOutput {
    let out = lexer::lex(src);
    let mut diagnostics = Vec::new();
    if let Some(err) = &out.error {
        diagnostics.push(Diagnostic::syntax(err.text.clone()).with_site(Some(err.line)));
    }
    let tokens = out
        .tokens
        .into_iter()
        .map(|(t, span)| (t, span.start))
        .collect();
    let mut parser = Parser::new(tokens, src, surface);
    let ast = parser.parse_program();
    diagnostics.extend(parser.diagnostics);
    FrontOutput { ast, diagnostics }
}

/// The L3 handoff: the spliced AST and the walk's facts travel
/// together — the dump renders both, and the L7 lowerer will take
/// `(&ShapeFacts, &Surface, &[Stmt])` from here.
pub struct Analyzed {
    pub ast: Vec<Stmt>,
    pub facts: shape::ShapeFacts,
}

/// Front → require splice → shape walk (L3's pipeline extent). The
/// walk runs with the recording gate the `walk_pins` lever arms;
/// surface laws ride `&Surface` (the P5 cure — the facts carry no
/// surface field), and `module_root` anchors the require splice as
/// plain pipeline configuration.
pub fn analyze_stage(
    src: &SourceFile,
    surface: &Surface,
    module_root: Option<&Path>,
    walk_pins: bool,
) -> Result<Analyzed, (Stage, Vec<Diagnostic>)> {
    let front = front(src, surface);
    if !front.is_ok() {
        return Err((Stage::Front, front.diagnostics));
    }
    // (mirror decision 8, kept: the splice runs ahead of the ffi gate
    // — inlining is compile-time and pure, and the amalgamated unit
    // carries ffi only if the source does. The gate itself lands with
    // the checker's verb table at L4.)
    let ast = require::expand(front.ast, surface, module_root).map_err(|d| (Stage::Modules, d))?;
    let ctx = analysis::build_context(&ast);
    let facts = shape::analyze(&ctx, walk_pins, surface);
    if !facts.diagnostics.is_empty() {
        return Err((Stage::Analyze, facts.diagnostics));
    }
    Ok(Analyzed { ast, facts })
}

#[cfg(test)]
mod tests {
    use super::front;
    use crate::source::SourceFile;
    use crate::surface::Surface;

    #[test]
    fn a_lexer_refusal_still_parses_the_truncated_stream() {
        // The truncation law on mirror's nul_string specimen: the NUL
        // refusal fires AND the parser adds its follow-on diagnostic on
        // the truncated stream. Two diagnostics, in that order.
        let src = SourceFile::new("nul.lua", "local s = \"before\0after\"\nprint(s)\n");
        let out = front(&src, &Surface::default());
        assert_eq!(out.diagnostics.len(), 2, "{:?}", out.diagnostics);
        assert!(
            out.diagnostics[0]
                .render()
                .starts_with("line 1: Syntax Error: Lexer error: embedded NUL byte"),
            "{:?}",
            out.diagnostics[0].render()
        );
        assert_eq!(
            out.diagnostics[1].render(),
            "line 1: Syntax Error: Expected expression"
        );
    }

    #[test]
    fn a_clean_parse_is_diagnostic_free() {
        let src = SourceFile::new(
            "ok.lua",
            "local t = {1, 2}\nfor i = 0, 1 do\n    t[i] = i\nend\n",
        );
        let out = front(&src, &Surface::default());
        assert!(out.is_ok(), "{:?}", out.diagnostics);
        assert_eq!(out.ast.len(), 2);
    }
}
