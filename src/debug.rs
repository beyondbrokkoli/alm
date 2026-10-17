//! Opt-in battle diagnostics. The shape/lowerer diagnosis lines from the
//! strkey/break campaign (join→Conflict traces, decide rewrites, fixpoint
//! pass counts, repr mismatches) stay available for the next lattice
//! fight — silent unless `GLM_DBG` is set in the environment, so the
//! default compile output stays clean.

use std::sync::OnceLock;

pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("GLM_DBG").is_some())
}

/// A shape/lowerer diagnosis line, suppressed unless `GLM_DBG` is set.
#[macro_export]
macro_rules! glm_dbgln {
    ($($arg:tt)*) => {
        if $crate::debug::enabled() {
            eprintln!($($arg)*);
        }
    };
}
