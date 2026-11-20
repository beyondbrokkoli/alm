/// [surface] The resolved surface: one struct, private fields, built
/// only via `Flag::apply`, passed by reference, read at named seams
/// (REBASE_PLAN.md §1: surface is data). L2 carries two fields; every
/// later toggle adds a field here and nowhere else — mirror's
/// `PipelineOpts`/`RequireOpts`/builder fan-out (audit P3) has no port.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Surface {
    pub(crate) index_base: i64,
    pub(crate) for_limit_inclusive: bool,
}

impl Surface {
    /// [index-base] The base the parser's ctor-key mint shifts by.
    /// Read at that seam only.
    pub fn index_base(&self) -> i64 {
        self.index_base
    }

    /// [for-limit] True is inclusive: the desugar latch folds
    /// `limit + 1` once. Read at that seam only.
    pub fn for_limit_inclusive(&self) -> bool {
        self.for_limit_inclusive
    }
}

/// [surface] One command-line toggle. The flag loop folds these into a
/// `Surface`; a new toggle is a new variant and every consumer decides.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Flag {
    /// [index-base] `--index-base=0|1` — strictly a toggle.
    IndexBase(i64),
    /// [for-limit] `--for-limit=exclusive|inclusive`.
    ForLimitInclusive(bool),
}

impl Flag {
    /// Parses one `--flag=value` word. Refusals carry mirror's exact
    /// wording (mirror main.rs @ 87aca4c) — the surface is a declared
    /// toggle, not a number, and the error says so.
    pub fn parse(word: &str) -> Result<Flag, String> {
        if let Some(raw) = word.strip_prefix("--index-base=") {
            match raw.parse::<i64>() {
                Ok(0) => Ok(Flag::IndexBase(0)),
                Ok(1) => Ok(Flag::IndexBase(1)),
                _ => Err(format!(
                    "alm compiler error: --index-base must be 0 or 1, got '{raw}' \
                     (the machinery is base-parametric; the surface is a toggle)"
                )),
            }
        } else if let Some(raw) = word.strip_prefix("--for-limit=") {
            match raw {
                "exclusive" => Ok(Flag::ForLimitInclusive(false)),
                "inclusive" => Ok(Flag::ForLimitInclusive(true)),
                _ => Err(format!(
                    "alm compiler error: --for-limit must be 'exclusive' or 'inclusive', \
                     got '{raw}' (inclusive latches limit + 1 and keeps the guard; \
                     the value is a declared surface, not a number)"
                )),
            }
        } else {
            Err(format!(
                "alm compiler error: Unknown flag '{word}'. Flags must come before the source file."
            ))
        }
    }

    /// [surface] The one write path into a `Surface`.
    pub fn apply(self, surface: &mut Surface) {
        match self {
            Flag::IndexBase(base) => surface.index_base = base,
            Flag::ForLimitInclusive(inclusive) => surface.for_limit_inclusive = inclusive,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Flag, Surface};

    fn surface_of(words: &[&str]) -> Surface {
        let mut surface = Surface::default();
        for word in words {
            Flag::parse(word)
                .expect("test uses legal flags only")
                .apply(&mut surface);
        }
        surface
    }

    #[test]
    fn default_is_base_zero_exclusive() {
        let s = Surface::default();
        assert_eq!(s.index_base(), 0);
        assert!(!s.for_limit_inclusive());
    }

    #[test]
    fn flags_fold_into_the_surface() {
        let s = surface_of(&["--index-base=1", "--for-limit=inclusive"]);
        assert_eq!(s.index_base(), 1);
        assert!(s.for_limit_inclusive());
        // Last write wins, as in mirror's plain assignment loop.
        let s = surface_of(&["--index-base=1", "--index-base=0"]);
        assert_eq!(s.index_base(), 0);
    }

    #[test]
    fn index_base_refusal_wording_is_mirror_exact() {
        assert_eq!(
            Flag::parse("--index-base=2").unwrap_err(),
            "alm compiler error: --index-base must be 0 or 1, got '2' \
             (the machinery is base-parametric; the surface is a toggle)"
        );
        assert_eq!(
            Flag::parse("--index-base=x").unwrap_err(),
            "alm compiler error: --index-base must be 0 or 1, got 'x' \
             (the machinery is base-parametric; the surface is a toggle)"
        );
    }

    #[test]
    fn for_limit_refusal_wording_is_mirror_exact() {
        assert_eq!(
            Flag::parse("--for-limit=both").unwrap_err(),
            "alm compiler error: --for-limit must be 'exclusive' or 'inclusive', \
             got 'both' (inclusive latches limit + 1 and keeps the guard; \
             the value is a declared surface, not a number)"
        );
    }

    #[test]
    fn unknown_flag_refusal_wording_is_mirror_exact() {
        assert_eq!(
            Flag::parse("--module-root=cases/modules").unwrap_err(),
            "alm compiler error: Unknown flag '--module-root=cases/modules'. \
             Flags must come before the source file."
        );
    }
}
