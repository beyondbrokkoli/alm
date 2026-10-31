// AST -> SSA IR lowering. Every acceptance decision rides facts
// (ShapeFacts); this walk lowers and never re-derives.

mod bridges;

use crate::ast::{BinOp, CtorKey, Expr, NodeId, Stmt, UnOp};
use crate::diag::Diagnostic;
use crate::ir::{
    AnyReg, BasicBlock, BlockId, Bool, CellRepr, DbgBind, Instruction, Int, IrProgram, Ptr, Reg,
    RegId, RegKind, SourceLoc, TableKey, Terminator, repr_of,
};
use crate::shape::{
    ArmFreeEntry, DoExitFree, FfiVerb, Keep, KeyLane, LayoutVerdict, ShapeFacts, TagSrc, Ty,
};
use alm_rt::{signal, trace};
use bridges::{
    NumPair, NumSingle, OrdPair, any_of, bool_of, int_of, num_pair, num_single, ord_pair, phi_of,
    phi_push, pooled_ptr_of, ptr_of, str_lane, string_repr,
};
use std::collections::{BTreeMap, BTreeSet};

/// A lowering rejection — a typed `Diagnostic` (H11); desync-ness is
/// the `Desync` variant on the payload, matched by kind.
pub struct LowerError(pub Diagnostic);

impl LowerError {
    pub fn is_desync(&self) -> bool {
        self.0.is_desync()
    }
}

pub fn boundary_elem_of(elem: Ty) -> alm_rt::AlmElem {
    match elem {
        Ty::Flt => alm_rt::AlmElem::Float,
        Ty::Bool => alm_rt::AlmElem::Boolean,
        Ty::Str => alm_rt::AlmElem::String,
        Ty::Any => alm_rt::AlmElem::Any,
        Ty::Int | Ty::Tbl(_) | Ty::Unknown(_) => alm_rt::AlmElem::Integer,
        Ty::Ffi | Ty::FfiLib | Ty::Coro => alm_rt::AlmElem::Integer,
        // a closure never rides the boundary (W3-R5's reject pin) —
        // the boundary elem fact is scalar-only by construction
        Ty::Closure(_) => unreachable!("a closure never rides the boundary elem"),
        // the boundary elem fact is a resolved checker value — flow
        // state never rides the artifact path
        Ty::Pending | Ty::Conflict => unreachable!("flow state never rides the artifact path"),
    }
}

fn join_phi_ty(a: &Ty, b: &Ty) -> Ty {
    if a == b {
        return a.clone();
    }
    let heap = |t: &Ty| matches!(t, Ty::Tbl(_));
    if heap(a) { a.clone() } else { b.clone() }
}

enum ReturnKind {
    Boundary,
    Inline { ty: Ty },
}

struct ReturnCtx {
    kind: ReturnKind,
    exit: Option<BlockId>,
    args: Vec<(BlockId, AnyReg)>,
}

#[derive(Clone)]
struct Local {
    reg: AnyReg,
    ty: Ty,
    layout: LayoutVerdict,
}

#[derive(Clone)]
struct TypedReg {
    reg: AnyReg,
    ty: Ty,
}

struct LoopCtx {
    guard_reg: RegId,
    reserved: Vec<RegId>,
    nested_fills: Vec<(String, Reg<Int>)>,
}

/// One per ACTIVE loop (pushed for every While, not just fill-converted
/// ones): breaks record (block, snapshot of phi_order locals) and the exit
/// block gains one phi per loop-carried var ONLY when breaks exist — so
/// break-free while loops lower bit-for-bit as before.
struct BreakCtx {
    exit_block: BlockId,
    phi_vars: Vec<String>,
    breaks: Vec<(BlockId, Vec<Local>)>,
}

struct FreeHandles {
    site_regs: BTreeMap<usize, (Reg<Ptr>, u32)>,
}

struct FillCtxs {
    loop_ctxs: Vec<LoopCtx>,
}

pub struct IrLowerer<'a> {
    pub blocks: Vec<BasicBlock>,
    pub diagnostics: Vec<Diagnostic>,
    current_block: BlockId,
    free_reg: RegId,
    scopes: Vec<BTreeMap<String, Local>>,
    fills: FillCtxs,
    handles: FreeHandles,
    shape: &'a ShapeFacts,
    cur_loc: Option<SourceLoc>,
    ghost_keeps: BTreeMap<usize, Reg<Ptr>>,
    if_tag_regs: BTreeMap<NodeId, Reg<Bool>>,
    call_tag_regs: BTreeMap<NodeId, Reg<Bool>>,

    ctrl_depth: u32,
    return_ctxs: Vec<ReturnCtx>,
    break_ctxs: Vec<BreakCtx>,
    inline_stack: Vec<NodeId>,
    /// the OUTERMOST call expr of every inline expansion currently being
    /// lowered (bottom = outermost site) — the lowerer's derivation of
    /// the `(call expr, expansion site)` fact keys it shares with the
    /// checker. Derived from this stack alone: both halves walk the
    /// identical AST in the identical order, so the sites agree without
    /// any shared counter.
    expansion_sites: Vec<NodeId>,
    /// the break-ctx depth each expansion began at — defense in depth:
    /// a break inside an expansion may only bind a loop of its OWN
    /// body, never the caller's (whose ctx would sit below the base).
    expansion_break_bases: Vec<usize>,
    /// W3a: the per-statement env mint memo — every closure created by
    /// ONE statement shares ONE env (sibling sharing, L3); the memo
    /// resets at each statement lowering. `stored` guards the union:
    /// a later creation in the same statement only stores its
    /// not-yet-stored captures.
    env_memo: Option<EnvMemo>,
    /// W3a: every minted env — freed at ROOT exit (W3-R1: module
    /// lifetime; the deep free reclaims boxes and moved tables).
    env_regs: Vec<Reg<Ptr>>,
    /// W3a: per ACTIVE call-through expansion — the env register and
    /// the face (capture name → cell type). Captures materialize as
    /// ordinary vars at entry; scalar rebinds write the box back.
    env_ctxs: Vec<EnvCtx>,
    /// the statement currently lowering (the env memo's key).
    cur_stmt: Option<NodeId>,
}

/// W3a's env representation: a strkey table whose EVERY cell is a
/// table pointer — captured tables ride their own headers, captured
/// scalars ride one-cell dense boxes of their own elem (the runtime's
/// deep free chases only pointer cells, so a mixed env must keep
/// every cell pointer-shaped; boxes carry contains_tables=0 and are
/// freed as headers, their scalar payloads never chased).
struct EnvMemo {
    stmt: NodeId,
    reg: Reg<Ptr>,
    stored: BTreeSet<String>,
}

struct EnvCtx {
    reg: Reg<Ptr>,
    faces: BTreeMap<String, Ty>,
}
impl Clone for EnvCtx {
    fn clone(&self) -> Self {
        EnvCtx {
            reg: self.reg,
            faces: self.faces.clone(),
        }
    }
}

// --- Included Units (100% Verbatim; include! order is document order) ---
// The impl_* files are method-boundary fragments of the ONE
// `impl<'a> IrLowerer<'a>` (multiple impl blocks for one type are
// semantically identical — the seams are the only additive text in the
// tree, and the reconstruction assert in split_lowerer.py re-derives
// the original bytes exactly). bridges.rs predates the split and is
// untouched.
include!("impl_core.rs"); // regs/blocks/frees/vars plumbing (new .. null_moves_of)
include!("impl_program.rs"); // lower_program, zero_reg, finalize_return_ctx
include!("impl_fact_reads.rs"); // fact_site, lower_index_key, elem_face_of — the fact-read family
include!("impl_stmt.rs"); // lower_stmt
include!("impl_layout_ffi.rs"); // lookup_layout_for, lower_ffi_call
include!("impl_env.rs"); // W3a: mint_env .. env_write_back
include!("impl_expr.rs"); // lower_expr (the Call arm — 7b's battle zone)
include!("collectors.rs"); // the phi collectors family + small free fns
include!("desync_class_tests.rs");
include!("break_gate_tests.rs");
