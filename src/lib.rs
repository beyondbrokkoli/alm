//! The alm compiler, rebuilt from mirror_experimental @ 87aca4c.
//!
//! Layer 2 of the rebase (REBASE_PLAN.md §4): source loading, the
//! `logos` lexer, the parser with both desugar latches, the surface's
//! first two fields, and the diagnostic currency of the front end.
//! Later layers port on top; nothing here may change behavior relative
//! to the mirror compiler.

pub mod ast;
pub mod diag;
pub mod dump;
pub mod elaborate;
pub mod lexer;
pub mod parser;
pub mod pipeline;
pub mod source;
pub mod surface;
