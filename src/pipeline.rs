//! The front leg of the pipeline: source → tokens → (desugared) AST.
//!
//! mirror's pipeline.rs @ 87aca4c holds the whole compiler flow in one
//! `compile`; alm grows stage by stage, so this file is that function's
//! front half (pipeline.rs:60-98 there). Everything after the front —
//! require splice, analysis, shape, lower, backend — lands with its
//! layer; nothing is stubbed.

use crate::ast::Stmt;
use crate::diag::Diagnostic;
use crate::lexer;
use crate::parser::Parser;
use crate::source::SourceFile;
use crate::surface::Surface;

pub struct FrontOutput {
    pub ast: Vec<Stmt>,
    pub diagnostics: Vec<Diagnostic>,
}

impl FrontOutput {
    pub fn is_ok(&self) -> bool {
        self.diagnostics.is_empty()
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
