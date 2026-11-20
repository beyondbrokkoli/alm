use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagKind {
    Bare,
    Syntax,
    Type,
    Scope,
    Lifetime,
    Lower,
    Bounds,
}

impl DiagKind {
    fn prefix(self) -> Option<&'static str> {
        match self {
            DiagKind::Bare => None,
            DiagKind::Syntax => Some("Syntax Error"),
            DiagKind::Type => Some("Type Error"),
            DiagKind::Scope => Some("Scope Error"),
            DiagKind::Lifetime => Some("Lifetime Error"),
            DiagKind::Lower => Some("Lower Error"),
            DiagKind::Bounds => Some("Table Bounds Error"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub site: Option<usize>,
    pub kind: DiagKind,
    pub text: String,
}

impl Diagnostic {
    pub fn bare(text: impl Into<String>) -> Self {
        Self::mint(DiagKind::Bare, text)
    }
    pub fn syntax(text: impl Into<String>) -> Self {
        Self::mint(DiagKind::Syntax, text)
    }
    pub fn ty(text: impl Into<String>) -> Self {
        Self::mint(DiagKind::Type, text)
    }
    pub fn scope(text: impl Into<String>) -> Self {
        Self::mint(DiagKind::Scope, text)
    }
    pub fn lifetime(text: impl Into<String>) -> Self {
        Self::mint(DiagKind::Lifetime, text)
    }
    pub fn lower(text: impl Into<String>) -> Self {
        Self::mint(DiagKind::Lower, text)
    }
    pub fn bounds(text: impl Into<String>) -> Self {
        Self::mint(DiagKind::Bounds, text)
    }

    fn mint(kind: DiagKind, text: impl Into<String>) -> Self {
        Diagnostic {
            site: None,
            kind,
            text: text.into(),
        }
    }

    pub fn with_site(mut self, site: Option<usize>) -> Self {
        self.site = site;
        self
    }

    pub fn render(&self) -> String {
        let mut out = String::with_capacity(self.text.len() + 32);
        if let Some(line) = self.site {
            out.push_str(&format!("line {line}: "));
        }
        if let Some(prefix) = self.kind.prefix() {
            out.push_str(prefix);
            out.push_str(": ");
        }
        out.push_str(&self.text);
        out
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.render())
    }
}

#[cfg(test)]
mod tests {
    use super::Diagnostic;

    // Render parity with mirror's front end: the lexer-refusal pins in
    // the corpus (`line 7: Syntax Error: Lexer error`) flow through this
    // exact formatting.
    #[test]
    fn render_matches_the_front_end_format() {
        assert_eq!(
            Diagnostic::syntax("Lexer error")
                .with_site(Some(7))
                .render(),
            "line 7: Syntax Error: Lexer error"
        );
        assert_eq!(
            Diagnostic::bare("no line, no prefix").render(),
            "no line, no prefix"
        );
        assert_eq!(
            Diagnostic::bounds("out").with_site(Some(3)).render(),
            "line 3: Table Bounds Error: out"
        );
    }
}
