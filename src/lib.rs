//! The alm compiler, rebuilt from mirror_experimental @ 87aca4c.
//!
//! Layer 3 of the rebase (REBASE_PLAN.md §4): the front end (L2), the
//! require splice, the analysis context, and the shape walk with the
//! `Ty` lattice — walk-only, `ShapeFacts` as its output and `Surface`
//! as its second input (the P5 cure). The checker interleave, fast
//! lane, and ownership exit planning land with L4–L6; nothing here may
//! change behavior relative to the mirror compiler.

pub mod analysis;
pub mod ast;
pub mod debug;
pub mod diag;
pub mod dump;
pub mod elaborate;
pub mod lexer;
pub mod parser;
pub mod pipeline;
pub mod require;
pub mod shape;
pub mod source;
pub mod surface;
pub mod visit;
