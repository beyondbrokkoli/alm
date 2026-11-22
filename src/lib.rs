//! The alm compiler, rebuilt from mirror_experimental @ 87aca4c.
//!
//! Layer 4 of the rebase (REBASE_PLAN.md §4): the front end (L2), the
//! require splice (L3), the shape walk with the `Ty` lattice (L3), and
//! the interleaved checker (L4) — `ShapeFacts` as the merged output
//! and `Surface` as the walk's second input (the P5 cure). The ffi
//! gate rides the pipeline behind the checker's verb table. The fast
//! lane and ownership exit planning land with L5–L6; nothing here may
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
