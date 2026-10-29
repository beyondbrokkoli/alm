//! Typed diagnostics (H11). Until this fold every phase minted its
//! rejections as pre-formatted strings — `format!("line {n}: Kind: text")`
//! hand-stamped at ~a dozen boundary sites, the kind prefix hand-embedded
//! in ~a hundred message literals, and the walk-desync protocol a
//! SUBSTRING check (`text.contains("disagree")`) re-run over the finished
//! text by every consumer (the lowerer's bail arms, the checker's, the
//! property harness's desync filter) — desync-ness riding the message
//! bytes instead of the type. One representation, three hand-maintained
//! agreements on its shape: the same disease the arc kills everywhere.
//!
//! The law now: a diagnostic is MINTED as `{ site, kind, text }` where it
//! is discovered — kind names the face once (the variant replaces the
//! embedded prefix), text carries only the message body, and the site is
//! stamped by the phase that knows the birth line. ONE formatter
//! (`render`) derives the `"line N: Kind: text"` bytes; nothing else in
//! the tree formats a diagnostic, so the rendered shape cannot drift
//! between mints. The rendered bytes are pinned byte-stable (the corpus
//! EXPECTs and the harness compare them).
//!
//! The desync protocol is the `Desync` variant: the halves' disagreement
//! is a KIND, detected by construction instead of by sniffing the text.
//! A desync's text keeps its face and its "— … disagree" tail inline —
//! the disagreeing halves are message CONTENT (which half owns the
//! truth), not format; `render` adds no prefix over them. H12's 7c
//! deletes the variant with the class it names.
//!
//! `site` is the birth LINE today, looked up from the loc-derived maps;
//! H6 re-keys it from a looked-up line to the node's own id, and H12's
//! instances key straight into it — sites become ids, not lookups.

use std::fmt;

/// The face a diagnostic renders under. The regular faces each own their
/// prefix; `Bare` renders none (driver-face refusals and harness wraps
/// that were never source-located — the ffi gate's bespoke text, the
/// panic wraps); `Desync` renders none either, because its text carries
/// its face inline (see the module law).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagKind {
    Bare,
    Syntax,
    Type,
    Scope,
    Lifetime,
    Lower,
    /// The dialect's table-bounds guard (index overflow at parse and at
    /// the walk's key inference).
    Bounds,
    /// The walk-desync protocol (was `contains("disagree")`): the two
    /// representations disagree. The class H12 retires.
    Desync,
}

impl DiagKind {
    fn prefix(self) -> Option<&'static str> {
        match self {
            DiagKind::Bare | DiagKind::Desync => None,
            DiagKind::Syntax => Some("Syntax Error"),
            DiagKind::Type => Some("Type Error"),
            DiagKind::Scope => Some("Scope Error"),
            DiagKind::Lifetime => Some("Lifetime Error"),
            DiagKind::Lower => Some("Lower Error"),
            DiagKind::Bounds => Some("Table Bounds Error"),
        }
    }
}

/// One rejection: where it was born (`site`, None when the minting phase
/// has no line — root-exit and root-free refusals render without the
/// prefix), which face it renders under, and the message body (no
/// prefix, no site — `render` adds both).
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
    /// The desync protocol: mint the halves' disagreement. The text is
    /// the full bespoke bug report — face and "disagree" tail inline.
    pub fn desync(text: impl Into<String>) -> Self {
        Self::mint(DiagKind::Desync, text)
    }

    fn mint(kind: DiagKind, text: impl Into<String>) -> Self {
        Diagnostic {
            site: None,
            kind,
            text: text.into(),
        }
    }

    /// The boundary stamp: the phase that knows the birth line writes it
    /// once, here — the only place a line enters a diagnostic.
    pub fn with_site(mut self, site: Option<usize>) -> Self {
        self.site = site;
        self
    }

    /// Desync-ness is the variant, never the bytes.
    pub fn is_desync(&self) -> bool {
        matches!(self.kind, DiagKind::Desync)
    }

    /// The one formatter: `"line N: Kind: text"` derived from the
    /// structure. Byte-stable law — the corpus EXPECTs and the harness
    /// compare this output.
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
