//! The alm compiler, rebuilt from mirror_experimental @ 87aca4c.
//!
//! Layer 1 of the rebase (REBASE_PLAN.md §4): source loading, the
//! `logos` lexer, and the diagnostic currency of the front end. Later
//! layers port on top; nothing here may change behavior relative to the
//! mirror compiler.

pub mod diag;
pub mod lexer;
pub mod source;
