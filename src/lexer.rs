use logos::Logos;

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

    #[regex(r#""[^"]*""#, |lex| {
        let s = lex.slice();
        if s.contains('\0') {
            let off = lex.span().start;
            let line = 1 + lex.source().as_bytes()[..off]
                .iter()
                .filter(|b| **b == b'\n')
                .count();
            panic!(
                "line {line}: Lexer error: embedded NUL byte in string literal at byte {off} \
                 — glm strings are NUL-terminated, so the literal would \
                 silently truncate at print time"
            );
        }
        Some(s)
    })]
    String(&'a str),
}
