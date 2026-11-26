//! The alm compiler, rebuilt from mirror_experimental @ 87aca4c.
//!
//! Layer 5 of the rebase (REBASE_PLAN.md §4): the front end (L2), the
//! require splice (L3), the shape walk with the `Ty` lattice (L3), the
//! interleaved checker (L4), and the fast lane (L5) — the fill-loop
//! detector's reserve plans plus the post-walk scan's store
//! eligibility facts, minted at one chokepoint. `ShapeFacts` is the
//! merged output and `Surface` the walk's second input (the P5 cure).
//! The ffi gate rides the pipeline behind the checker's verb table.
//! Layer 6 of the rebase adds the ownership exit planner: temp fates,
//! scope-death and root frees, and the return and break edges — the
//! frees/keeps algebra the lowerer will emit — and the omni watcher,
//! an `ALM_OMNI`-gated observer of the scope law that writes to
//! stderr only, and only when enabled. Nothing here may change
//! behavior relative to the mirror compiler.

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
