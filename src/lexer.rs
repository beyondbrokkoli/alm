use crate::source::SourceFile;
use logos::Logos;
use std::ops::Range;

/// Diagnostic text for a match the lexer refused: a slice carrying an
/// embedded NUL was a string literal the String callback rejected — spell
/// out the law; anything else is the generic lexer error. Ported
/// verbatim from mirror (single source, so the wording cannot drift);
/// both front-end Err arms there routed through one function for the
/// same reason.
pub fn rejected_match_text(slice: &str, off: usize) -> String {
    if slice.contains('\0') {
        format!(
            "Lexer error: embedded NUL byte in string literal at byte {off} \
             — alm strings are NUL-terminated, so the literal would \
             silently truncate at print time"
        )
    } else {
        "Lexer error".to_string()
    }
}

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip(r"[ \t\n\r\f\v]+"))]
#[logos(skip(r"(?s)--\[\[.*?\]\]"))]
#[logos(skip(r"--[^\n]*|#![^\n]*", allow_greedy = true))]
pub enum Token<'a> {
    #[token("local")]
    Local,
    #[token("=")]
    Assign,
    #[token("do")]
    Do,
    #[token("end")]
    End,
    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("nil")]
    Nil,
    #[token("print")]
    Print,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("elseif")]
    ElseIf,
    #[token("else")]
    Else,
    #[token("while")]
    While,
    #[token("for")]
    For,
    #[token("break")]
    Break,
    #[token("return")]
    Return,
    #[token("function")]
    Function,
    #[token("not")]
    Not,
    #[token("and")]
    And,
    #[token("or")]
    Or,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("<")]
    LessThan,
    #[token("<=")]
    LessEq,
    #[token(">")]
    GreaterThan,
    #[token(">=")]
    GreaterEq,
    #[token("==")]
    Equal,
    #[token("~=")]
    NotEqual,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("//")]
    DoubleSlash,
    #[token("%")]
    Percent,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[token("..")]
    DotDot,
    #[token(":")]
    Colon,
    #[token("{")]
    LeftBrace,
    #[token("}")]
    RightBrace,
    #[token("[")]
    LeftBracket,
    #[token("]")]
    RightBracket,
    #[token("#")]
    Len,

    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*")]
    Identifier(&'a str),

    #[regex(r"[0-9]+", |lex| lex.slice().parse().ok())]
    Integer(i64),

    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice().parse().ok())]
    Float(f64),

    // A literal carrying an embedded NUL rejects its match (None): the
    // front end's Err arm turns the failed span into the embedded-NUL
    // diagnostic. alm strings are NUL-terminated, so the literal would
    // silently truncate at print time — a diagnostic, never a panic.
    #[regex(r#""[^"]*""#, |lex| {
        let s = lex.slice();
        (!s.contains('\0')).then_some(s)
    })]
    String(&'a str),
}

/// A refused match: where it happened and the exact diagnostic mirror's
/// front end would mint for it. `text` is `rejected_match_text` output;
/// `line` is the 1-based source line of the span start.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    pub span: Range<usize>,
    pub line: usize,
    pub text: String,
}

/// The lex of one whole file: every token accepted before the first
/// refusal (mirror's front end stops at the first lexer error — parity),
/// plus that refusal if there was one. Tokens carry full byte spans;
/// L2's parser adapts to start-offsets with one map.
#[derive(Debug, Clone, PartialEq)]
pub struct LexOutput<'a> {
    pub tokens: Vec<(Token<'a>, Range<usize>)>,
    pub error: Option<LexError>,
}

/// Lex a source file. One implementation of the collect loop (mirror had
/// it inline in pipeline.rs and duplicated in require.rs); the loop body
/// and the diagnostic mint are behavior-identical.
pub fn lex(src: &SourceFile) -> LexOutput<'_> {
    let mut tokens = Vec::new();
    let mut lexer = Token::lexer(src.text());
    loop {
        match lexer.next() {
            Some(Ok(token)) => tokens.push((token, lexer.span())),
            Some(Err(_)) => {
                let span = lexer.span();
                let error = LexError {
                    span: span.clone(),
                    line: src.line_of(span.start),
                    text: rejected_match_text(lexer.slice(), span.start),
                };
                return LexOutput {
                    tokens,
                    error: Some(error),
                };
            }
            None => {
                return LexOutput {
                    tokens,
                    error: None,
                };
            }
        }
    }
}

/// The token's variant name without payload — `Identifier("x")` yields
/// `Identifier`. The corpus sweep uses it as a coverage key; the unit
/// tests enumerate every variant, so a new variant appears here as a new
/// name, never as a silent gap.
pub fn kind_name(token: &Token<'_>) -> String {
    let debug = format!("{token:?}");
    match debug.find('(') {
        Some(at) => debug[..at].to_string(),
        None => debug,
    }
}

#[cfg(test)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::SourceFile;

    /// Lex `text` cleanly, binding the owner and its output in the
    /// caller's scope: `lex_ok!(src, out, "..")` — the tokens borrow from
    /// `src`, so the two must share a scope.
    macro_rules! lex_ok {
        ($src:ident, $out:ident, $text:expr) => {
            let $src = SourceFile::new("test.lua", $text);
            let $out = lex(&$src);
            assert!($out.error.is_none(), "expected clean lex of {:?}", $text);
        };
    }

    fn lex_err(text: &str) -> LexError {
        let src = SourceFile::new("test.lua", text);
        let out = lex(&src);
        out.error
            .unwrap_or_else(|| panic!("expected a lex error for {text:?}"))
    }

    /// Kind names joined with commas — the readable form of a token soup.
    fn kinds(text: &str) -> String {
        lex_ok!(src, out, text);
        out.tokens
            .iter()
            .map(|(t, _)| kind_name(t))
            .collect::<Vec<_>>()
            .join(",")
    }

    // -- keywords: exact spellings, and nothing else is one ------------

    #[test]
    fn all_keywords_are_their_own_token() {
        let kws = [
            ("local", "Local"),
            ("do", "Do"),
            ("end", "End"),
            ("true", "True"),
            ("false", "False"),
            ("nil", "Nil"),
            ("print", "Print"),
            ("if", "If"),
            ("then", "Then"),
            ("elseif", "ElseIf"),
            ("else", "Else"),
            ("while", "While"),
            ("for", "For"),
            ("break", "Break"),
            ("return", "Return"),
            ("function", "Function"),
            ("not", "Not"),
            ("and", "And"),
            ("or", "Or"),
        ];
        for (spelling, name) in kws {
            assert_eq!(kinds(spelling), name, "keyword {spelling}");
        }
    }

    #[test]
    fn keywords_are_case_sensitive_and_prefix_free() {
        // No lowercasing in the grammar: LOCAL is a name.
        assert_eq!(kinds("LOCAL"), "Identifier");
        // Longest match wins: a keyword prefix of an identifier loses.
        assert_eq!(kinds("printf"), "Identifier");
        assert_eq!(kinds("localx"), "Identifier");
        assert_eq!(kinds("elseifx"), "Identifier");
        assert_eq!(kinds("elseif"), "ElseIf");
    }

    // -- operators and punctuation ------------------------------------

    #[test]
    fn all_operators_and_punctuation() {
        let ops = [
            ("=", "Assign"),
            ("+", "Plus"),
            ("-", "Minus"),
            ("<", "LessThan"),
            ("<=", "LessEq"),
            (">", "GreaterThan"),
            (">=", "GreaterEq"),
            ("==", "Equal"),
            ("~=", "NotEqual"),
            ("*", "Star"),
            ("/", "Slash"),
            ("//", "DoubleSlash"),
            ("%", "Percent"),
            (",", "Comma"),
            (".", "Dot"),
            ("..", "DotDot"),
            (":", "Colon"),
            ("{", "LeftBrace"),
            ("}", "RightBrace"),
            ("[", "LeftBracket"),
            ("]", "RightBracket"),
            ("(", "LeftParen"),
            (")", "RightParen"),
            ("#", "Len"),
        ];
        for (spelling, name) in ops {
            assert_eq!(kinds(spelling), name, "operator {spelling}");
        }
    }

    #[test]
    fn longest_match_splits_neighbors() {
        assert_eq!(kinds("1..2"), "Integer,DotDot,Integer");
        assert_eq!(
            kinds("a<=b>=c==d~=e"),
            "Identifier,LessEq,Identifier,GreaterEq,Identifier,Equal,Identifier,NotEqual,Identifier"
        );
        assert_eq!(kinds("a//b"), "Identifier,DoubleSlash,Identifier");
    }

    // -- identifiers ----------------------------------------------------

    #[test]
    fn identifiers_allow_underscores_and_inner_digits() {
        assert_eq!(
            kinds("_ _x x1 a_b_c9 z"),
            "Identifier,Identifier,Identifier,Identifier,Identifier"
        );
        // A digit cannot start a name — but the digits and the name are
        // both ordinary tokens.
        assert_eq!(kinds("9x"), "Integer,Identifier");
    }

    #[test]
    fn dollar_refuses_and_keeps_earlier_tokens() {
        // The pinned desugar-hygiene refusal (mirror case
        // desugar_hygiene_dollar_rejected.lua): `$` is not in the
        // grammar, so the synthetic namespace (for$limit, tuple$tN) is
        // unreachable from source. Tokens before the refusal survive.
        let src = SourceFile::new("t.lua", "local tuple$t0 = 1");
        let out = lex(&src);
        assert_eq!(out.tokens.len(), 2); // local, tuple
        let err = out.error.expect("$ refuses");
        assert_eq!(err.text, "Lexer error");
        assert_eq!(err.span, 11..12);
        assert_eq!(err.line, 1);
    }

    // -- numbers ---------------------------------------------------------

    #[test]
    fn integers_parse_as_i64() {
        lex_ok!(_src, out, "0 42 9223372036854775807");
        assert_eq!(
            out.tokens
                .iter()
                .map(|(t, _)| t.clone())
                .collect::<Vec<_>>(),
            vec![
                Token::Integer(0),
                Token::Integer(42),
                Token::Integer(i64::MAX)
            ]
        );
    }

    #[test]
    fn integer_overflow_refuses_the_match() {
        // Parity: the callback's `.parse().ok()` returning None makes
        // logos treat the slice as an error — big literals are lexer
        // errors, not wraps, not parser problems.
        let err = lex_err("9223372036854775808");
        assert_eq!(err.text, "Lexer error");
        assert_eq!(err.span, 0..19);
    }

    #[test]
    fn floats_require_digits_on_both_sides_of_the_dot() {
        lex_ok!(_src, out, "1.5 0.0 10.25");
        assert_eq!(
            out.tokens
                .iter()
                .map(|(t, _)| t.clone())
                .collect::<Vec<_>>(),
            vec![Token::Float(1.5), Token::Float(0.0), Token::Float(10.25)]
        );
        // `1.` is an integer then a dot; `.5` is a dot then an integer.
        assert_eq!(kinds("1."), "Integer,Dot");
        assert_eq!(kinds(".5"), "Dot,Integer");
        // No exponent syntax exists in the grammar: `1.5e3` is 1.5, then
        // a name starting with `e`.
        assert_eq!(kinds("1.5e3"), "Float,Identifier");
        // `1.5.6`: longest match takes 1.5, then the dot, then 6.
        assert_eq!(kinds("1.5.6"), "Float,Dot,Integer");
    }

    // -- strings -----------------------------------------------------------

    #[test]
    fn strings_are_raw_double_quoted_slices() {
        lex_ok!(_src, out, r#""hi" "" "a b c""#);
        assert_eq!(
            out.tokens
                .iter()
                .map(|(t, _)| t.clone())
                .collect::<Vec<_>>(),
            vec![
                Token::String(r#""hi""#),
                Token::String(r#""""#),
                Token::String(r#""a b c""#)
            ]
        );
    }

    #[test]
    fn strings_have_no_escape_forms() {
        // Parity: the grammar is "[^"]*" — a backslash is an ordinary
        // byte, so the second quote CLOSES the string; nothing escapes.
        lex_ok!(_src, out, r#""a\""#); // " a \ "
        assert_eq!(out.tokens.len(), 1);
        assert_eq!(out.tokens[0].0, Token::String(r#""a\""#));
        assert_eq!(out.tokens[0].1, 0..4);
    }

    #[test]
    fn embedded_nul_refuses_with_the_exact_diagnostic() {
        let src = SourceFile::new("t.lua", "local s = \"before\0after\"\n");
        let out = lex(&src);
        // Tokens before the refusal survive; lexing stops there. The
        // refused span is the whole literal (byte offsets count the
        // opening quote), matching mirror's pipeline Err arm.
        assert_eq!(out.tokens.len(), 3); // local, s, =
        let err = out.error.expect("NUL literal refuses");
        assert_eq!(err.span, 10..24);
        assert_eq!(err.line, 1);
        assert_eq!(
            err.text,
            "Lexer error: embedded NUL byte in string literal at byte 10 \
             — alm strings are NUL-terminated, so the literal would \
             silently truncate at print time"
        );
    }

    #[test]
    fn unterminated_string_refuses() {
        let err = lex_err("\"open");
        assert_eq!(err.text, "Lexer error");
    }

    // -- comments and skips -----------------------------------------------

    #[test]
    fn line_comments_and_shebang_skip_to_end_of_line() {
        assert_eq!(kinds("-- a comment\n1"), "Integer");
        assert_eq!(kinds("----\n2"), "Integer");
        assert_eq!(kinds("#!/usr/bin/env alm\n3"), "Integer");
        assert_eq!(kinds("1 -- trailing\n2"), "Integer,Integer");
        // A lone # is the len operator, not a comment.
        assert_eq!(kinds("#t"), "Len,Identifier");
    }

    #[test]
    fn long_comments_span_until_the_first_close() {
        assert_eq!(kinds("--[[ multi\nline ]] 1"), "Integer");
        // Longest match wins among skips too: a long comment that ends
        // mid-line loses to the line-comment rule when that would reach
        // further (to end of line). `--[[a]] 2` is 7 bytes as a long
        // comment but 9 as a line comment — so the 2 is swallowed. This
        // is mirror behavior (same enum, same logos), pinned here.
        assert_eq!(kinds("--[[ multi\nline ]] 1 --[[a]] 2"), "Integer");
        assert_eq!(kinds("1 --[[a]]\n2"), "Integer,Integer");
        // A single-line long comment with trailing code loses the same
        // way: the whole line is a line comment, nothing lexes.
        assert_eq!(kinds("--[[ outer --[[ inner ]] 1 ]] 2"), "");
    }

    #[test]
    fn unterminated_long_comment_falls_back_to_a_line_comment() {
        // Parity: the long-comment skip needs its closing ]]; without one
        // it cannot match, and the line-comment skip `--[^\n]*` takes the
        // first line instead. The body then lexes as ordinary code.
        assert_eq!(kinds("--[[ never closed\n1 2"), "Integer,Integer");
    }

    #[test]
    fn all_whitespace_classes_skip() {
        // space, \t, \n, \r, \f, \v — the corpus pins \f and \v via
        // comment_form_feed.lua; \r appears with CRLF sources.
        assert_eq!(
            kinds("1 \t\n2\r3\u{c}4\u{b}5"),
            "Integer,Integer,Integer,Integer,Integer"
        );
    }

    // -- spans and refusal metadata ----------------------------------------

    #[test]
    fn spans_are_exact_byte_offsets() {
        lex_ok!(_src, out, "local x = 1.5 -- c\nprint(x)");
        let spans: Vec<Range<usize>> = out.tokens.iter().map(|(_, s)| s.clone()).collect();
        assert_eq!(
            spans,
            vec![
                0..5,   // local
                6..7,   // x
                8..9,   // =
                10..13, // 1.5
                19..24, // print
                24..25, // (
                25..26, // x
                26..27, // )
            ]
        );
    }

    #[test]
    fn spans_are_byte_offsets_not_char_offsets() {
        // Multibyte content in a comment and a string: offsets count
        // bytes, matching mirror's byte-offset spans.
        let src = SourceFile::new("t.lua", "-- é\nx = \"λ\"");
        let out = lex(&src);
        assert!(out.error.is_none());
        assert_eq!(out.tokens[0].1, 6..7); // x (é is 2 bytes in the comment)
        assert_eq!(out.tokens[2].1, 10..14); // "λ" — quote + 2 bytes + quote
        assert_eq!(out.tokens[2].0, Token::String("\"λ\""));
    }

    #[test]
    fn the_error_line_is_one_based_and_counts_prior_lines() {
        let src = SourceFile::new("t.lua", "local a = 1\nlocal b = 2\nlocal c = `");
        let out = lex(&src);
        assert_eq!(out.tokens.len(), 11); // two full statements + `local c =`
        let err = out.error.expect("backtick refuses");
        assert_eq!(err.line, 3);
        assert_eq!(err.span.start, 34);
    }

    #[test]
    fn lexing_stops_at_the_first_refusal() {
        let src = SourceFile::new("t.lua", "1 $ 2");
        let out = lex(&src);
        assert_eq!(out.tokens.len(), 1);
        assert!(out.error.is_some());
    }

    #[test]
    fn kind_name_strips_payloads() {
        lex_ok!(_src, out, "x 1 2.5 \"s\"");
        let names: Vec<String> = out.tokens.iter().map(|(t, _)| kind_name(t)).collect();
        assert_eq!(names, vec!["Identifier", "Integer", "Float", "String"]);
    }

    #[test]
    fn determinism_two_lexes_agree() {
        let src = SourceFile::new("t.lua", "local t = {1, 2} -- [[not long]]\nprint(#t)");
        assert_eq!(lex(&src), lex(&src));
    }
}
