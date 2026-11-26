//! The checker (L4): the statement-order type checker that interleaves
//! with the recorded walk pass — one `check_stmt` after every
//! `walk_stmt`, reading the walk's snapshots and minting the
//! chk-owned fact families. mirror's `checker/mod.rs` @ 87aca4c with
//! the ten `include!` files dissolved into real modules (Class A1):
//! bodies verbatim, cross-file methods `pub(super)`.
//!
//! Receipts vs mirror: `alm_rt` signals never port (§B); the omni
//! watchers landed at L6 (6.4), verbatim less their plate pokes;
//! `mint_instance` re-homes from a process-global `AtomicU32` to the
//! Checker's own counter (per-compile deterministic — same sequence
//! mirror's first compile mints, and the in-process sweeps compare
//! equal).

use super::WalkState;
use super::omni;
use crate::shape::TableShape;
use crate::shape::facts::{BuiltinVerb, FfiMint, FfiVerb, FnDef, InstanceId, InstanceInfo};

use crate::ast::NodeId;
use crate::diag::Diagnostic;
use crate::shape::ty::Ty;
use std::collections::{BTreeMap, BTreeSet};
pub(super) use type_helpers::type_name;

mod expand_call;
mod impl_closure_faces;
mod impl_core;
mod impl_expr;
mod impl_expr_helpers;
mod impl_fact_writers;
mod impl_ffi;
mod impl_scopes;
mod impl_stmt;
mod type_helpers;

fn snap_of(walk: &WalkState, severed: &BTreeMap<String, BTreeSet<usize>>) -> WalkSnap {
    // D3: WalkSnap stays flat this phase — the depth-0 bindings
    // project back to the three flat faces the checker's read sites
    // consume (binds/scalars/fns). Fusing the checker's own snapshot
    // is a separate session.
    let mut binds = BTreeMap::new();
    let mut scalars = BTreeMap::new();
    let mut fns = BTreeMap::new();
    for (name, bind) in &walk.scopes[0] {
        binds.insert(name.clone(), bind.shape.clone());
        if let Some(id) = bind.scalar_node {
            scalars.insert(name.clone(), id);
        }
        fns.insert(name.clone(), bind.fn_ptr);
    }
    WalkSnap {
        binds,
        scalars,
        fns,
        severed: severed
            .iter()
            .filter(|(name, _)| walk.scopes[0].contains_key(*name))
            .map(|(name, sites)| (name.clone(), sites.clone()))
            .collect(),
    }
}

#[derive(Clone)]
enum ReturnCtx {
    Boundary,
    Internal(Ty),
}

struct Frame {
    types: BTreeMap<String, Ty>,
    fns: BTreeMap<String, Option<NodeId>>,
    /// The fn names DECLARED at this frame — the binding's birthplace.
    /// `declare_fn_binding` mints a fresh binding at the innermost
    /// frame (or the root home), so a face in `fns` whose name is here
    /// was BORN with this frame and dies with it: the scope's own
    /// grave, not an orphan. An `assign_fn_binding` write never adds a
    /// name — it rebinds where the binding already lives — so every
    /// `fns` entry's name is in the `born` set of the frame it was
    /// minted at. A dying frame carrying a face NOT in its `born` set
    /// would mean a write landed somewhere its binding does not live —
    /// the burial law's trip shape.
    born: BTreeSet<String>,
    /// Names this frame declares as CAPTURE VIEWS: an expansion frame's
    /// depth-0 capture entries. A capture view reads the owner binding
    /// (the boundary root for depth 0) — caller shadows below the
    /// expansion cannot re-point it, mirroring the lowerer's capture
    /// slots. The entry dies with its frame; the owner's type never
    /// moves (the monomorphic law keeps the two identical anyway).
    captures: BTreeSet<String>,
}

/// The cdef grammar's scalar tier: kinds that map onto the existing
/// esize lanes. `name`/`elem`/`capacity`/`reject-surface` are the
/// registry row's projections.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ScalarElem {
    Int,
    Flt,
    Bool,
}

impl ScalarElem {
    /// The one reader that maps a cdef scalar onto the checker's Ty
    /// lanes — every consumer projects through here.
    fn ty(self) -> Ty {
        match self {
            ScalarElem::Int => Ty::Int,
            ScalarElem::Flt => Ty::Flt,
            ScalarElem::Bool => Ty::Bool,
        }
    }

    /// esize in bytes, per the runtime's esize lanes ({1,8,16}).
    fn esize(self) -> i64 {
        match self {
            ScalarElem::Int | ScalarElem::Flt => 8,
            ScalarElem::Bool => 1,
        }
    }
}

/// One `ffi.cdef` registry row. `elem: None` is a struct/union name —
/// registered so later milestones can hang typed rows off it, but
/// `ffi.new` over it rejects by name.
#[derive(Clone, Debug)]
pub(super) struct CdefRow {
    pub elem: Option<ScalarElem>,
    pub capacity: Option<i64>,
}

#[derive(Clone)]
pub(super) struct WalkSnap {
    binds: BTreeMap<String, TableShape>,
    scalars: BTreeMap<String, usize>,
    fns: BTreeMap<String, Option<NodeId>>,
    severed: BTreeMap<String, BTreeSet<usize>>,
}

pub(super) struct CheckCtx {
    /// [index-base] The compile's physical-key base, for the mint
    /// bounds check — minted at the one `Checker::new` seam in
    /// `analyze` (`surface.index_base()`).
    pub index_base: i64,
    pub adopt_lines: BTreeMap<String, usize>,
    pub sites: BTreeMap<NodeId, usize>,
    pub elems: Vec<Ty>,
    pub fn_def_sites: BTreeMap<NodeId, BTreeMap<String, Option<NodeId>>>,
    pub fn_captures: BTreeMap<NodeId, BTreeSet<String>>,
    pub fn_capture_depths: BTreeMap<NodeId, BTreeMap<String, usize>>,
}

pub(super) struct CheckFacts {
    pub local_types: BTreeMap<(NodeId, InstanceId, String), Ty>,
    pub fn_defs: BTreeMap<NodeId, FnDef>,
    pub call_fns: BTreeMap<NodeId, BTreeSet<NodeId>>,
    pub env_faces: BTreeMap<NodeId, BTreeMap<String, Ty>>,
    pub env_face_depths: BTreeMap<NodeId, BTreeMap<String, usize>>,
    /// Every fn literal's capture name -> its binding's walk-scope
    /// depth, minted or not (the walk stamps it at definition). The
    /// lowerer's direct-expansion capture slots key off this — a
    /// never-minted fn has no env_face_depths to read.
    pub fn_capture_depths: BTreeMap<NodeId, BTreeMap<String, usize>>,
    pub closure_fields: BTreeMap<(usize, String), NodeId>,
    pub ffi_verbs: BTreeMap<NodeId, FfiVerb>,
    pub builtin_verbs: BTreeMap<NodeId, BuiltinVerb>,
    pub ffi_mints: BTreeMap<NodeId, FfiMint>,
    pub instances: BTreeMap<InstanceId, InstanceInfo>,
    pub boundary_elem: Option<Ty>,
    pub diagnostics: Vec<Diagnostic>,
}

pub(super) struct Checker {
    frames: Vec<Frame>,
    /// The rider's root fn-face home — the checker-side twin of the
    /// walk's `boundary_root_scope` (d0). Top-level fn faces live
    /// HERE, on the checker's own statement-order timeline, instead
    /// of dropping to the master snapshot. The phase-1 receipts
    /// (✎checker-fn DROPPED, tier=master-snapshot at top level) were
    /// this map's absence; the phase-2 plug-in is this map.
    ///
    /// Its laws mirror the walk's face timeline exactly (the judge's
    /// law, 2026-11-14): sequential and `do` writes persist, if-arm
    /// and while-body writes die with their scope (`cond_depth` is
    /// the standing mask for exactly those contexts), and a call
    /// expansion's body write moves the root face at call time — the
    /// defcollection drag's correct twin. `resolve_fn_binding`
    /// answers through it BEFORE the master snapshot, so a top-level
    /// call resolves at its binding point's state (the
    /// fn_defcollection_order law).
    root_fns: BTreeMap<String, Option<NodeId>>,
    top: BTreeMap<String, Ty>,
    cur_decls: BTreeSet<String>,
    snap: WalkSnap,
    decl_snap: WalkSnap,
    ctx: CheckCtx,
    return_ctxs: Vec<ReturnCtx>,
    inline_stack: Vec<NodeId>,
    expansion_frame_bases: Vec<usize>,
    expansion_params: Vec<Vec<String>>,
    instance_stack: Vec<InstanceId>,
    expansion_break_bases: Vec<usize>,
    seed_read: bool,
    len_deferrals: Vec<(Ty, Option<usize>)>,
    cur_stmt: Option<NodeId>,
    cur_stmt_line: Option<usize>,
    loop_depth: usize,
    fn_defs: BTreeMap<NodeId, FnDef>,
    call_fns: BTreeMap<NodeId, BTreeSet<NodeId>>,
    env_faces: BTreeMap<NodeId, BTreeMap<String, Ty>>,
    env_face_depths: BTreeMap<NodeId, BTreeMap<String, usize>>,
    closure_fields: BTreeMap<(usize, String), NodeId>,
    expansion_envs: Vec<Option<BTreeMap<String, Ty>>>,
    env_overrides: Vec<BTreeMap<String, Ty>>,
    cond_depth: usize,
    ffi_verbs: BTreeMap<NodeId, FfiVerb>,
    builtin_verbs: BTreeMap<NodeId, BuiltinVerb>,
    ffi_mints: BTreeMap<NodeId, FfiMint>,
    /// The compile-time cdef declaration registry — `name -> row`.
    /// Lives and dies with the checker; nothing about it reaches the
    /// runtime or the plate.
    cdef_registry: BTreeMap<String, CdefRow>,
    /// The declared capacity of the name's current mint binding, for
    /// the static-key bounds check. Maintained at the local-decl and
    /// assignment choke points.
    mint_caps: BTreeMap<String, i64>,
    /// [index-base] The compile's index base, for physical-key
    /// comparison at the mint bounds check.
    index_base: i64,
    instances: BTreeMap<InstanceId, InstanceInfo>,
    /// The instance-id minter's counter — per-compile deterministic
    /// (mirror rode a process-global atomic; see the module receipt).
    instance_next: u32,
    local_types: BTreeMap<(NodeId, InstanceId, String), Ty>,
    bare_sites: BTreeMap<(NodeId, InstanceId, String), usize>,
    boundary_elem: Option<Ty>,
    diagnostics: Vec<Diagnostic>,
    stmt_position_call: bool,
}
