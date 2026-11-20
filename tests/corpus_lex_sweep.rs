//! Layer-1 corpus sweep (REBASE_PLAN.md §4): the alm lexer must be
//! behavior-identical to mirror_experimental's, and the frozen corpus at
//! `mirror_experimental @ 87aca4c` is the witness.
//!
//! Two corpus files pin lexer refusals — they must fail with the exact
//! pinned diagnostics (verified against mirror's compiled binary):
//!   desugar_hygiene_dollar_rejected.lua → `line 7: Syntax Error: Lexer error`
//!   nul_string.lua → the embedded-NUL wording, `at byte 68`, line 2
//! Every other `.lua` under the corpus root (including `modules/`
//! fixtures) must lex with zero refusals, monotone non-overlapping byte
//! spans, and byte-identical determinism across two runs.

use alm::lexer::{self, kind_name};
use alm::source::SourceFile;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn cases_dir() -> PathBuf {
    if let Ok(custom) = std::env::var("ALM_MIRROR_CASES") {
        return PathBuf::from(custom);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../mirror_experimental/cases")
}

fn collect_lua_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("corpus dir {} unreadable: {e}", dir.display()));
    for entry in entries {
        let path = entry.expect("corpus entry").path();
        if path.is_dir() {
            collect_lua_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "lua") {
            out.push(path);
        }
    }
}

/// The variant-coverage golden: the frozen corpus exercises exactly this
/// set of token variants. The lexer unit tests enumerate every variant
/// independently, so a grammar change surfaces here as a diff against
/// the frozen set, never as silence.
const EXPECTED_KINDS: &[&str] = &[
    "And",
    "Assign",
    "Break",
    "Colon",
    "Comma",
    "Do",
    "Dot",
    "DotDot",
    "DoubleSlash",
    "Else",
    "ElseIf",
    "End",
    "Equal",
    "False",
    "Float",
    "For",
    "Function",
    "GreaterEq",
    "GreaterThan",
    "Identifier",
    "If",
    "Integer",
    "LeftBrace",
    "LeftBracket",
    "LeftParen",
    "Len",
    "LessEq",
    "LessThan",
    "Local",
    "Minus",
    "Nil",
    "Not",
    "NotEqual",
    "Or",
    "Percent",
    "Plus",
    "Print",
    "Return",
    "RightBrace",
    "RightBracket",
    "RightParen",
    "Slash",
    "Star",
    "String",
    "Then",
    "True",
    "While",
];

#[test]
fn corpus_lex_sweep_matches_mirror() {
    let root = cases_dir();
    assert!(
        root.is_dir(),
        "corpus root {} not found — point ALM_MIRROR_CASES at \
         mirror_experimental/cases (the frozen oracle, REBASE_PLAN.md §3.3)",
        root.display(),
    );

    let mut files = Vec::new();
    collect_lua_files(&root, &mut files);
    files.sort();
    assert!(
        files.len() >= 440,
        "corpus shrank to {} files — the frozen corpus of record is 449",
        files.len(),
    );

    let mut seen_kinds: BTreeSet<String> = BTreeSet::new();
    let mut refused: Vec<String> = Vec::new();

    for path in &files {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let src =
            SourceFile::read(path).unwrap_or_else(|e| panic!("corpus file {name} unreadable: {e}"));
        let out = lexer::lex(&src);

        // Determinism: an identical re-lex must be byte-identical.
        assert_eq!(out, lexer::lex(&src), "{name}: re-lex diverged");

        // Coverage: every token contributes its variant name.
        for (token, _) in &out.tokens {
            seen_kinds.insert(kind_name(token));
        }

        // Spans: monotone, non-overlapping, inside the file; a string
        // token's payload is exactly the source bytes it covers.
        let mut cursor = 0usize;
        for (token, span) in &out.tokens {
            assert!(
                span.start >= cursor,
                "{name}: span {span:?} overlaps the previous token ending at {cursor}"
            );
            assert!(
                span.end <= src.text().len(),
                "{name}: span {span:?} runs past end of file"
            );
            if let lexer::Token::String(slice) = token {
                assert_eq!(
                    *slice,
                    &src.text()[span.clone()],
                    "{name}: string slice mismatch"
                );
            }
            cursor = span.end;
        }

        match name.as_str() {
            // The two pinned refusals — exact diagnostics, verified
            // against mirror's binary at 87aca4c.
            "desugar_hygiene_dollar_rejected.lua" => {
                let err = out
                    .error
                    .expect("$ is not in the grammar — this case must refuse");
                assert_eq!(err.line, 7);
                assert_eq!(err.text, "Lexer error");
                assert_eq!(
                    alm::diag::Diagnostic::syntax(err.text)
                        .with_site(Some(err.line))
                        .render(),
                    "line 7: Syntax Error: Lexer error"
                );
            }
            "nul_string.lua" => {
                let err = out
                    .error
                    .expect("embedded NUL literal — this case must refuse");
                assert_eq!(err.line, 2);
                assert_eq!(
                    err.text,
                    "Lexer error: embedded NUL byte in string literal at byte 68 \
                     — alm strings are NUL-terminated, so the literal would \
                     silently truncate at print time"
                );
            }
            _ => {
                if let Some(err) = out.error {
                    refused.push(format!("{name}: line {}: {}", err.line, err.text));
                }
            }
        }
    }

    assert!(
        refused.is_empty(),
        "{} corpus files refused to lex (only the two pinned cases may): {}",
        refused.len(),
        refused.join(" | "),
    );

    let expected: BTreeSet<String> = EXPECTED_KINDS.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        seen_kinds, expected,
        "token variant coverage over the frozen corpus changed"
    );
}
