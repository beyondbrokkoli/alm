use crate::analysis::AnalysisContext;
use crate::ast::{BinOp, CtorKey, Expr, NodeId, Stmt, UnOp};
use std::collections::{BTreeMap, BTreeSet};

use super::core::{
    BOUNDARY_ROOT, BOUNDS_FAIL_THRESHOLD, DECL_PENDING, LayoutVerdict, MOVED_ROOT, NULL_ROOT,
    RowLineage, SPARSE_THRESHOLD, TableShape, is_ghost, is_root,
};
use super::facts;
use super::facts::{FastStoreElig, KeyShape, ReservePlan, ShapeFacts};
use super::helpers::{const_key_value, extract_guard, guard_key_shape};
use super::ty::{Ty, arith_ty, contains_any, decided, join_ty, pinned_scalar, value_kind};
pub(super) use crate::diag::Diagnostic;
use crate::surface::Surface;
use Ty::{Any, Async, Bool, Conflict, Ffi, FfiLib, Flt, Int, Pending, Str, Tbl};

mod checker;
mod checks;
mod constraints;
mod exits;
mod fast_lane;
mod functions;
mod infer;
mod lattice;
mod pins;
mod rebind;
mod rows;
mod walk;

use infer::*;
use lattice::*;
use rebind::*;
use rows::*;

struct ShapeError(pub Diagnostic);

fn boundary_root_scope() -> Scope {
    let mut scope = Scope::new();
    scope.insert(
        "arg".to_string(),
        Binding::new(TableShape {
            ty: Tbl(Box::new(Pending)),
            layout: LayoutVerdict::default(),
            aliases: BTreeSet::from([BOUNDARY_ROOT]),
            lineage: BTreeMap::new(),
        }),
    );
    scope
}

/// The shape face of a pre-bound target: pending, and marked
/// DECL_PENDING so shape reads skip the binding and resolve outward —
/// the D1 window, carried by the type instead of by a missing map
/// entry (see `WalkState::resolve`).
fn decl_pending_shape() -> TableShape {
    TableShape {
        ty: Pending,
        layout: LayoutVerdict::default(),
        aliases: BTreeSet::from([DECL_PENDING]),
        lineage: BTreeMap::new(),
    }
}

/// Everything the walk knows about one name at one depth. A binding's
/// faces are born, live, and die with the same map entry at the same
/// depth — there is nowhere else for them to be. `TableShape` stays the
/// currency everywhere else (fn_rets, join_arm_shapes, merge joins, the
/// checker's snapshots); Binding is what the scope carries.
#[derive(Clone, Debug, PartialEq)]
struct Binding {
    /// The shape face — the master's own payload (ty, layout, aliases,
    /// lineage).
    shape: TableShape,
    /// The fn face — Some(ptr) when the binding holds a function
    /// literal, None when it does not. The old key-presence bit had one
    /// exception (the boundary `arg` bound with no fn entry — the p30
    /// orphan precondition); here every binding carries the face, and
    /// `arg`'s is simply None.
    fn_ptr: Option<NodeId>,
    /// The provenance face — was `prov[d][name]`.
    prov: Option<Prov>,
    /// The scalar-node face — was `scalar_nodes[d][name]`, where key
    /// presence meant the node id and absence meant no node. Here a
    /// plain Option: the note_* remove-on-no-node dance folds into an
    /// assignment.
    scalar_node: Option<usize>,
}

impl Binding {
    /// The only way to mint a binding: all faces declared, none
    /// implicit. Every construction site names its faces.
    fn new(shape: TableShape) -> Self {
        Binding {
            shape,
            fn_ptr: None,
            prov: None,
            scalar_node: None,
        }
    }

    fn with_fn(shape: TableShape, fn_ptr: Option<NodeId>) -> Self {
        Binding {
            shape,
            fn_ptr,
            prov: None,
            scalar_node: None,
        }
    }
}

/// One depth of the walk.
type Scope = BTreeMap<String, Binding>;

struct WalkState {
    scopes: Vec<Scope>,
    changed: bool,
}

/// The recorded pass's gate: fixpoint passes run unrecorded (`None`),
/// the final pass runs recorded (`Some`) — the walk replays identically
/// while the pin machinery arms and the rec-gated fact minters fire.
/// (The checker interleave returned with L4, the fill-loop detector
/// with L5; the exit-fate minters are the gate's remaining historical
/// consumers, L6.)
#[derive(Clone, Copy)]
struct Recording {
    _priv: (),
}

type Gate = Option<Recording>;

trait GateOn {
    fn on(self) -> bool;
}

impl GateOn for Option<Recording> {
    fn on(self) -> bool {
        self.is_some()
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Prov {
    If(NodeId),
    Call(NodeId),
}

impl WalkState {
    /// The Oracle — the single resolution path. The master stack is the
    /// only place a binding lives; every face reads off the same
    /// Binding at the same depth. The old `.iter().rev().find_map()`
    /// scans (resolve over scopes, resolve_fn over fn_scopes, name_node
    /// over scalar_nodes — each blind to binding depth in its own way)
    /// collapse into these methods and their projectors.
    fn binding_at(&self, name: &str) -> Option<(usize, &Binding)> {
        self.scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(depth, scope)| scope.get(name).map(|bind| (depth, bind)))
    }

    /// Home-depth mutable access — the one write path for faces. There
    /// is no rider stack to pick a depth from.
    fn binding_at_mut(&mut self, name: &str) -> Option<(usize, &mut Binding)> {
        self.scopes
            .iter_mut()
            .enumerate()
            .rev()
            .find_map(|(depth, scope)| scope.get_mut(name).map(|bind| (depth, bind)))
    }

    /// The shape face, producing the undeclared diagnostic. A
    /// DECL_PENDING binding is skipped: its shape face is still pending,
    /// and a shape read answers as if the binding were not there yet —
    /// the D1 window, carried by the marker instead of by a missing map
    /// entry.
    fn resolve(&self, name: &str) -> Result<(usize, TableShape), ShapeError> {
        for (depth, scope) in self.scopes.iter().enumerate().rev() {
            if let Some(bind) = scope.get(name) {
                if bind.shape.aliases.contains(&DECL_PENDING) {
                    continue;
                }
                return Ok((depth, bind.shape.clone()));
            }
        }
        Err(ShapeError(Diagnostic::scope(format!(
            "reference to undeclared variable '{}'",
            name
        ))))
    }

    /// The fn face: the innermost binding's fn_ptr. An inner non-fn
    /// binding shadows the outer fn (None wins) — exactly the old
    /// fn_scopes rev-scan, minus the drift. The p30 law ("a fn entry
    /// rides its name's binding depth") is no longer a written
    /// agreement; it is the only thing that can happen.
    fn resolve_fn(&self, name: &str) -> Option<NodeId> {
        self.binding_at(name)?.1.fn_ptr
    }

    /// The scalar-node face — what name_node scanned for, blind to
    /// binding depth. Reads the binding: the blind spot is unwritable.
    fn scalar_node(&self, name: &str) -> Option<usize> {
        self.binding_at(name)?.1.scalar_node
    }

    /// The provenance face at an explicit depth (join sites, rebind
    /// writers).
    fn prov_at(&self, depth: usize, name: &str) -> Option<Prov> {
        self.scopes[depth].get(name)?.prov
    }
}

struct LatticeState {
    sites: BTreeMap<NodeId, usize>,
    site_elem: Vec<Ty>,
    needed: Vec<bool>,
    child_sites: BTreeMap<usize, BTreeSet<usize>>,
    ghost_next: usize,
    row_ghosts: BTreeMap<NodeId, usize>,
    row_ghost_next: usize,
    ghost_mints: BTreeMap<usize, GhostMint>,
    site_slots: BTreeMap<usize, BTreeMap<i64, usize>>,
    ghost_site: BTreeMap<usize, usize>,
    housed_ghosts: BTreeSet<usize>,
    claimed_ghosts: BTreeSet<usize>,
    adopt_witness: BTreeMap<usize, usize>,
    unknowns: constraints::UnknownStore,
}

struct GhostMint {
    bases: BTreeSet<usize>,
    #[allow(dead_code)]
    key: Option<i64>,
}

struct OwnershipState {
    free_sites: BTreeSet<NodeId>,
    free_keeps: BTreeMap<NodeId, Vec<super::facts::Keep>>,
    do_exit_frees: BTreeMap<(NodeId, u8), Vec<super::facts::DoExitFree>>,
    root_exit_frees: Vec<super::facts::DoExitFree>,
    stmt_temp_frees: BTreeMap<NodeId, Vec<usize>>,
    cond_temp_frees: BTreeMap<NodeId, Vec<usize>>,
    arm_temp_frees: BTreeMap<NodeId, Vec<usize>>,
    rebind_grants: BTreeMap<NodeId, BTreeMap<String, Vec<super::facts::Keep>>>,
    stored_ctor_parents: BTreeSet<usize>,
    /// [fast-lane] Every IndexAssign whose value inferred table-typed —
    /// the same predicate the lowerer's `contains_tables` ownership bit
    /// keys on. The fast lane reads it so a store's row kind survives a
    /// non-ctor spelling (`t[i] = r`), which the lane's syntactic
    /// `TableCtor` check alone would miss and mark nothing.
    row_value_stores: BTreeSet<NodeId>,
    move_poisons: BTreeMap<NodeId, BTreeSet<String>>,
    store_ghost_keeps: BTreeMap<NodeId, Vec<usize>>,
    ctor_ghost_keeps: BTreeMap<NodeId, Vec<(usize, usize)>>,
    arm_free_sites: BTreeMap<NodeId, Vec<super::facts::ArmFreeEntry>>,
    arm_rebind_frees: BTreeMap<NodeId, Vec<super::facts::ArmFreeEntry>>,
    arm_do_exit_frees: BTreeMap<(NodeId, u8), Vec<super::facts::ArmFreeEntry>>,
    arm_root_exit_frees: Vec<super::facts::ArmFreeEntry>,
}

struct HoldsState {
    hold_edges: BTreeMap<usize, BTreeSet<usize>>,
    cyclic_stores: BTreeMap<String, (String, usize)>,
    /// [fast-lane] Guard arithmetic shapes, written by every decl and
    /// assignment the walk passes; the fill-loop detector is the read
    /// side (guard nonneg/lower-bound/ascends facts).
    num_assigns: BTreeMap<String, Vec<NumExpr>>,
    nil_severed: BTreeMap<String, BTreeSet<usize>>,
    moved_severed: BTreeMap<String, BTreeSet<usize>>,
}

struct ReadSideState {
    tbl_value_stores: BTreeSet<usize>,
    nested_store_bases: BTreeMap<usize, String>,
    row_reads: BTreeMap<usize, (String, usize)>,
    row_links: BTreeMap<usize, BTreeSet<usize>>,
    user_store_sites: BTreeSet<usize>,
    boundary_fed: BTreeSet<usize>,
}

struct LayoutFactsState {
    /// [fast-lane] The (name, depth) pairs a fill loop proved dense —
    /// the reserve plan builder's own read-back, the scan's scratch.
    name_dense: BTreeMap<(String, usize), bool>,
    fast_stores: BTreeMap<NodeId, super::facts::FastStoreElig>,
    reserve_plans: BTreeMap<NodeId, super::facts::ReservePlan>,
    verdicts: Vec<LayoutVerdict>,
}

/// The ctor sites a body mentions — rides the traversal engine; the site
/// read at every expression is the enter_expr hook.
struct BodySites<'a> {
    sites: &'a BTreeMap<NodeId, usize>,
    out: BTreeSet<usize>,
}

impl crate::visit::Visitor for BodySites<'_> {
    type Break = std::convert::Infallible;

    fn enter_expr(&mut self, expr: &Expr) -> Result<(), Self::Break> {
        if let Some(&id) = self.sites.get(&expr.id()) {
            self.out.insert(id);
        }
        Ok(())
    }

    // NOTE historical shape: the hand walker never descended a Field's
    // obj (a ctor inside `t[..].k` went unseen). Kept bit-for-bit — the
    // goldens lock it; revisit as its own change if ever needed.
    fn visit_field(&mut self, _obj: &Expr, _name: &str, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }
}

fn collect_body_sites(stmts: &[Stmt], sites: &BTreeMap<NodeId, usize>, out: &mut BTreeSet<usize>) {
    let mut v = BodySites {
        sites,
        out: std::mem::take(out),
    };
    let _ = crate::visit::walk_stmts(&mut v, stmts);
    *out = v.out;
}

/// Bases stored into by a body — rides the traversal engine; the base of
/// every IndexAssign obj is read before its children.
struct StoredBases {
    out: BTreeSet<String>,
}

impl crate::visit::Visitor for StoredBases {
    type Break = std::convert::Infallible;

    fn visit_index_assign(
        &mut self,
        obj: &Expr,
        key: &Expr,
        value: &Expr,
        _loc: crate::ast::Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        if let Some(base) = stmt_base(obj) {
            self.out.insert(base);
        }
        crate::visit::walk_expr(self, obj)?;
        crate::visit::walk_expr(self, key)?;
        crate::visit::walk_expr(self, value)
    }

    // NOTE historical shape: same Field-obj blindness as the body-sites
    // scan above — kept bit-for-bit for the goldens.
    fn visit_field(&mut self, _obj: &Expr, _name: &str, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }
}

fn stmt_base(e: &Expr) -> Option<String> {
    // C: index-chain classifier — only an Identifier or an Index spine
    // names a base
    match e {
        Expr::Identifier { name: n, .. } => Some(n.clone()),
        Expr::Index { obj, .. } => stmt_base(obj),
        // C: every other expression form is not an lvalue base
        Expr::Integer { .. }
        | Expr::Float { .. }
        | Expr::Boolean { .. }
        | Expr::String { .. }
        | Expr::Nil { .. }
        | Expr::TableCtor { .. }
        | Expr::BinaryOp { .. }
        | Expr::UnaryOp { .. }
        | Expr::SysAllocCount { .. }
        | Expr::SysExecCount { .. }
        | Expr::FfiModule { .. }
        | Expr::AsyncModule { .. }
        | Expr::Field { .. }
        | Expr::Function { .. }
        | Expr::Call { .. } => None,
    }
}

fn collect_stored_bases(stmts: &[Stmt]) -> BTreeSet<String> {
    let mut v = StoredBases {
        out: BTreeSet::new(),
    };
    let _ = crate::visit::walk_stmts(&mut v, stmts);
    v.out
}

struct Analyzer {
    walk: WalkState,
    ledger: Ledger,
    lattice: LatticeState,
    own: OwnershipState,
    holds: HoldsState,
    reads: ReadSideState,
    layout: LayoutFactsState,
    walk_pins: bool,
    /// [surface] The resolved surface, the walk's second input (the P5
    /// cure: facts stay base-free; the `[index-base]` seams read this).
    surface: Surface,
    pin_derived_exprs: BTreeSet<NodeId>,
    pin_justified_names: BTreeSet<String>,
    ctor_lines: Vec<usize>,
    fn_rets: Vec<Option<TableShape>>,
    fn_edge_frames: Vec<Vec<TableShape>>,
    fn_ret_shapes: BTreeMap<NodeId, TableShape>,
    fn_ret_edge_shapes: BTreeMap<NodeId, Vec<TableShape>>,
    join_arm_shapes: BTreeMap<(NodeId, String), (TableShape, TableShape)>,
    join_tags: BTreeMap<NodeId, bool>,
    call_tags: BTreeMap<NodeId, Vec<bool>>,
    fn_scope_keys: BTreeMap<NodeId, (NodeId, u8)>,
    fn_body_sites: BTreeSet<usize>,
    fn_params: BTreeMap<NodeId, Vec<String>>,
    fn_store_params: BTreeMap<NodeId, BTreeSet<String>>,
    fn_param_sites: BTreeSet<usize>,
    fn_moved_params: BTreeMap<NodeId, BTreeSet<String>>,
    fn_ret_params: BTreeMap<NodeId, BTreeSet<usize>>,
    fn_ret_reach: BTreeMap<NodeId, BTreeSet<usize>>,
    fn_ret_reaches: Vec<BTreeSet<usize>>,
    fn_walk: Vec<(NodeId, Vec<String>)>,
    fn_scope_entries: Vec<usize>,
    fn_def_sites: BTreeMap<NodeId, BTreeMap<String, Option<NodeId>>>,
    fn_captures: BTreeMap<NodeId, BTreeSet<String>>,
    fn_capture_depths: BTreeMap<NodeId, BTreeMap<String, usize>>,
    /// Each fn literal's body-scope walk depth: the index its body
    /// scope occupies on the walk stack at the definition site. The
    /// lowerer adds its expansion-frame offset to this to recover any
    /// declare site's walk depth — the box-on-declare gate's key.
    fn_body_depths: BTreeMap<NodeId, usize>,
    loop_scope_entries: Vec<usize>,
}

struct Ledger {
    diagnostics: Vec<Diagnostic>,
    conflict_reported: BTreeSet<usize>,
}

/// [surface] The walk boundary: `ShapeFacts` out, `Surface` in as the
/// second input — the P5 cure made structural (mirror's
/// `analyze_with_base(ctx, walk_pins, index_base)` never ports; the
/// facts carry no surface field for a lowerer to read later).
pub fn analyze(ctx: &AnalysisContext<'_>, walk_pins: bool, surface: &Surface) -> ShapeFacts {
    let n = ctx.sites.len();
    let mut a = Analyzer {
        walk_pins,
        surface: *surface,
        pin_derived_exprs: BTreeSet::new(),
        pin_justified_names: BTreeSet::new(),
        walk: WalkState {
            scopes: vec![boundary_root_scope()],
            changed: false,
        },
        ledger: Ledger {
            diagnostics: Vec::new(),
            conflict_reported: BTreeSet::new(),
        },
        lattice: LatticeState {
            sites: ctx.sites.clone(),
            site_elem: vec![Pending; n],
            needed: vec![false; n],
            child_sites: BTreeMap::new(),
            ghost_next: usize::MAX / 2,
            row_ghosts: BTreeMap::new(),
            row_ghost_next: super::core::ROW_GHOST_FLOOR + 1,
            ghost_mints: BTreeMap::new(),
            site_slots: BTreeMap::new(),
            ghost_site: BTreeMap::new(),
            housed_ghosts: BTreeSet::new(),
            claimed_ghosts: BTreeSet::new(),
            adopt_witness: BTreeMap::new(),
            unknowns: constraints::UnknownStore::new(),
        },
        own: OwnershipState {
            free_sites: BTreeSet::new(),
            free_keeps: BTreeMap::new(),
            do_exit_frees: BTreeMap::new(),
            root_exit_frees: Vec::new(),
            stmt_temp_frees: BTreeMap::new(),
            cond_temp_frees: BTreeMap::new(),
            arm_temp_frees: BTreeMap::new(),
            rebind_grants: BTreeMap::new(),
            stored_ctor_parents: BTreeSet::new(),
            row_value_stores: BTreeSet::new(),
            move_poisons: BTreeMap::new(),
            store_ghost_keeps: BTreeMap::new(),
            ctor_ghost_keeps: BTreeMap::new(),
            arm_free_sites: BTreeMap::new(),
            arm_rebind_frees: BTreeMap::new(),
            arm_do_exit_frees: BTreeMap::new(),
            arm_root_exit_frees: Vec::new(),
        },
        holds: HoldsState {
            hold_edges: BTreeMap::new(),
            cyclic_stores: BTreeMap::new(),
            num_assigns: BTreeMap::new(),
            nil_severed: BTreeMap::new(),
            moved_severed: BTreeMap::new(),
        },
        reads: ReadSideState {
            tbl_value_stores: BTreeSet::new(),
            nested_store_bases: BTreeMap::new(),
            row_reads: BTreeMap::new(),
            row_links: BTreeMap::new(),
            user_store_sites: BTreeSet::new(),
            boundary_fed: BTreeSet::new(),
        },
        layout: LayoutFactsState {
            name_dense: BTreeMap::new(),
            fast_stores: BTreeMap::new(),
            reserve_plans: BTreeMap::new(),
            verdicts: vec![LayoutVerdict::Growing; n],
        },
        ctor_lines: ctx.ctor_lines.clone(),
        fn_rets: Vec::new(),
        fn_edge_frames: Vec::new(),
        fn_ret_shapes: BTreeMap::new(),
        fn_ret_edge_shapes: BTreeMap::new(),
        join_arm_shapes: BTreeMap::new(),
        join_tags: BTreeMap::new(),
        call_tags: BTreeMap::new(),
        fn_scope_keys: BTreeMap::new(),
        fn_body_sites: BTreeSet::new(),
        fn_params: BTreeMap::new(),
        fn_store_params: BTreeMap::new(),
        fn_param_sites: BTreeSet::new(),
        fn_moved_params: BTreeMap::new(),
        fn_ret_params: BTreeMap::new(),
        fn_ret_reach: BTreeMap::new(),
        fn_ret_reaches: Vec::new(),
        fn_walk: Vec::new(),
        fn_scope_entries: Vec::new(),
        fn_def_sites: BTreeMap::new(),
        fn_captures: BTreeMap::new(),
        fn_capture_depths: BTreeMap::new(),
        fn_body_depths: BTreeMap::new(),
        loop_scope_entries: Vec::new(),
    };

    let mut prev_end: Vec<Scope> = Vec::new();
    loop {
        a.walk.changed = false;
        a.walk.scopes = vec![boundary_root_scope()];
        a.fn_def_sites.clear();
        a.fn_captures.clear();
        a.fn_capture_depths.clear();
        a.walk_stmts(None, ctx.ast);
        // Stability sees the one stack the walk maintains: every face
        // rides its binding, so a settled scope state cannot hide an
        // oscillating rider — the old four-stack compare had to guard
        // against exactly that, and has nothing left to guard.
        let end = a.walk.scopes.clone();
        let stable = end == prev_end && !a.walk.changed;
        prev_end = end.clone();
        if stable {
            break;
        }
    }

    let adopt_lines: BTreeMap<String, usize> = {
        let mut m = BTreeMap::new();
        for scope in a.walk.scopes.iter() {
            for (name, bind) in scope {
                let mut best: Option<usize> = None;
                for s in bind.shape.aliases.iter() {
                    if let Some(&l) = a.lattice.adopt_witness.get(s) {
                        best = Some(best.map_or(l, |b: usize| b.min(l)));
                    }
                }
                if let Some(l) = best {
                    m.insert(name.clone(), l);
                }
            }
        }
        m
    };

    a.ledger.diagnostics.clear();
    let (static_elems, elems_diags) = a.compute_static_elems(n);

    let rec: Gate = Some(Recording { _priv: () });
    a.walk.scopes = vec![boundary_root_scope()];
    a.pin_derived_exprs.clear();
    a.pin_justified_names.clear();

    // The L4 interleave: one checker statement between every walk
    // statement, reading the walk's snapshots. A walk error breaks the
    // loop before the checker sees that statement; an elems refusal
    // (a missing-value diagnostic already minted) never runs the
    // checker at all.
    let mut chk = checker::Checker::new(checker::CheckCtx {
        // [index-base] the one CheckCtx mint — the surface's law feeds
        // the checker's mint bounds seam.
        index_base: a.surface.index_base(),
        adopt_lines: adopt_lines.clone(),
        sites: a.lattice.sites.clone(),
        elems: static_elems.clone(),
        fn_def_sites: a.fn_def_sites.clone(),
        fn_captures: a.fn_captures.clone(),
        fn_capture_depths: a.fn_capture_depths.clone(),
    });
    let mut checker_ran = elems_diags.is_empty();
    let mut last_post: Option<Vec<Scope>> = None;
    let mut walk_completed = true;
    for stmt in ctx.ast {
        if let Some(post) = &last_post {
            debug_assert_eq!(
                a.walk.scopes, *post,
                "the interleaving broke: the walk moved between the checker's snapshots"
            );
        }
        chk.snapshot_pre(&a.walk, &a.holds.moved_severed);
        if let Err(err) = a.walk_stmt(rec, stmt) {
            a.ledger
                .diagnostics
                .push(err.0.with_site(Some(stmt.loc().line as usize)));
            checker_ran = false;
            walk_completed = false;
            break;
        }
        chk.snapshot_post(&a.walk, &a.holds.moved_severed);
        last_post = Some(a.walk.scopes.clone());
        if checker_ran && let Err(msg) = chk.check_stmt(&mut a.lattice.unknowns, stmt) {
            a.ledger
                .diagnostics
                .push(msg.with_site(Some(stmt.loc().line as usize)));
            walk_completed = false;
            break;
        }
    }
    if walk_completed {
        #[cfg(debug_assertions)]
        if let Err(diff) =
            recorded_reproduces_fixpoint(&a.walk.scopes, &prev_end, &a.pin_justified_names)
        {
            panic!(
                "the recorded pass diverged from the fixpoint's converged end state \
                 beyond the chartered pin refinements: {diff}"
            );
        }
    }
    debug_assert!(
        a.lattice.row_ghost_next <= a.lattice.unknowns.next_id() + 1,
        "id-space exhausted: row ghosts crossed the unknown-node minter"
    );
    if checker_ran {
        chk.finish(&mut a.lattice.unknowns);
    }
    let chk_facts = chk.into_facts();

    if let Err(err) = a.decide_root_exit(rec) {
        a.ledger.diagnostics.push(err.0);
    }
    a.plan_stmt_temp_frees(ctx.ast);
    a.mint_fast_lane(ctx.ast);

    let mut facts = a
        .into_recorded(adopt_lines, static_elems, elems_diags, chk_facts)
        .into_facts();
    facts.fn_touched = ctx.fn_touched.clone();
    facts.check_row_reads();
    facts
}

#[cfg(debug_assertions)]
fn recorded_reproduces_fixpoint(
    recorded: &[Scope],
    fixpoint: &[Scope],
    pin_justified: &BTreeSet<String>,
) -> Result<(), String> {
    if recorded.len() != fixpoint.len() {
        return Err(format!(
            "the scope stack depths diverged: recorded {} vs fixpoint {}",
            recorded.len(),
            fixpoint.len()
        ));
    }
    for (depth, (rec_scope, fix_scope)) in recorded.iter().zip(fixpoint).enumerate() {
        for (name, rec) in rec_scope {
            let Some(fix) = fix_scope.get(name) else {
                return Err(format!(
                    "depth {depth}: '{name}' exists only in the recorded pass"
                ));
            };
            if rec.shape == fix.shape {
                continue;
            }
            let legal = rec.shape.layout == fix.shape.layout
                && rec.shape.aliases == fix.shape.aliases
                && rec.shape.lineage == fix.shape.lineage
                && ty_refines(&rec.shape.ty, &fix.shape.ty);
            if !legal {
                return Err(format!(
                    "depth {depth}: '{name}' is not a monotone refinement — \
                     recorded {:?} vs fixpoint {:?}",
                    rec.shape, fix.shape
                ));
            }
            if !pin_justified.contains(name) {
                return Err(format!(
                    "depth {depth}: '{name}' refined to {:?} with no walk pin \
                     accounting for it — recorded {:?} vs fixpoint {:?}",
                    rec.shape.ty, rec.shape, fix.shape,
                ));
            }
        }
        for name in fix_scope.keys() {
            if !rec_scope.contains_key(name) {
                return Err(format!(
                    "depth {depth}: '{name}' exists only in the fixpoint end state"
                ));
            }
        }
    }
    Ok(())
}

#[cfg(debug_assertions)]
fn ty_refines(rec: &Ty, fix: &Ty) -> bool {
    if rec == fix {
        return true;
    }
    match (rec, fix) {
        (_, Pending) => pinned_scalar(rec),
        (Tbl(rec_elem), Tbl(fix_elem)) => ty_refines(rec_elem, fix_elem),
        _ => false,
    }
}

struct Recorded {
    ledger: Ledger,
    lattice: LatticeState,
    own: OwnershipState,
    reads: ReadSideState,
    layout: LayoutFactsState,
    ctor_lines: Vec<usize>,
    fn_scope_keys: BTreeMap<NodeId, (NodeId, u8)>,
    fn_body_depths: BTreeMap<NodeId, usize>,
    join_tags: BTreeMap<NodeId, bool>,
    call_tags: BTreeMap<NodeId, Vec<bool>>,
    adopt_lines: BTreeMap<String, usize>,
    static_elems: Vec<crate::shape::Ty>,
    elems_diags: Vec<Diagnostic>,
    chk: checker::CheckFacts,
}

impl Analyzer {
    fn into_recorded(
        self,
        adopt_lines: BTreeMap<String, usize>,
        static_elems: Vec<crate::shape::Ty>,
        elems_diags: Vec<Diagnostic>,
        chk: checker::CheckFacts,
    ) -> Recorded {
        Recorded {
            ledger: self.ledger,
            lattice: self.lattice,
            own: self.own,
            reads: self.reads,
            layout: self.layout,
            ctor_lines: self.ctor_lines,
            fn_scope_keys: self.fn_scope_keys,
            fn_body_depths: self.fn_body_depths,
            join_tags: self.join_tags,
            call_tags: self.call_tags,
            adopt_lines,
            static_elems,
            elems_diags,
            chk,
        }
    }

    fn compute_static_elems(&mut self, n: usize) -> (Vec<crate::shape::Ty>, Vec<Diagnostic>) {
        let mut elems: Vec<crate::shape::Ty> = (0..n).map(crate::shape::Ty::Unknown).collect();

        let site_ids: Vec<usize> = self.lattice.sites.values().copied().collect();
        for id in site_ids {
            if self.lattice.needed[id] && self.lattice.site_elem[id] == Pending {
                if self.fn_body_sites.contains(&id) || self.fn_param_sites.contains(&id) {
                    elems[id] = crate::shape::Ty::Unknown(id);
                    continue;
                }
                if self.reads.boundary_fed.contains(&id) {
                    elems[id] = crate::shape::Ty::Unknown(id);
                    continue;
                }
                let line = self.ctor_lines[id];
                self.ledger.diagnostics.push(
                    Diagnostic::ty(format!(
                        "a table is read before it is ever given a value (table site #{id})"
                    ))
                    .with_site(Some(line)),
                );
                elems[id] = crate::shape::Ty::Unknown(id);
            } else if self.lattice.site_elem[id] == Pending {
                elems[id] = crate::shape::Ty::Unknown(id);
            } else {
                elems[id] = self.elem_type_of_tbl(id);
            }
        }

        for (&site, name) in &self.reads.nested_store_bases {
            if !self.reads.tbl_value_stores.contains(&site) {
                let line = self.ctor_lines[site];
                self.ledger.diagnostics.push(
                    Diagnostic::ty(format!(
                        "cannot index a row of '{name}' — no table is ever \
                         stored into '{name}', and stores do not create rows (table site #{site})"
                    ))
                    .with_site(Some(line)),
                );
            }
        }

        for (base, (value, line)) in &self.holds.cyclic_stores {
            self.ledger.diagnostics.push(
                Diagnostic::ty(format!(
                    "cyclic table store — '{value}' stored into '{base}' \
                     would create a table cycle (alm's element types are finite)"
                ))
                .with_site(Some(*line)),
            );
        }

        for id in 0..n {
            propagate_elem_down(&mut elems, &self.lattice.child_sites, id);
        }

        let elems_diags: Vec<Diagnostic> = std::mem::take(&mut self.ledger.diagnostics);
        (elems, elems_diags)
    }
}

impl Recorded {
    fn into_facts(mut self) -> ShapeFacts {
        let mut diagnostics = std::mem::take(&mut self.ledger.diagnostics);
        diagnostics.append(&mut self.elems_diags);
        diagnostics.append(&mut self.chk.diagnostics);

        let substitutions = self.lattice.unknowns.take_subs();

        let mut cell_children = self.lattice.child_sites.clone();
        for (parent, kids) in std::mem::take(&mut self.reads.row_links) {
            cell_children.entry(parent).or_default().extend(kids);
        }

        // [fast-lane] The second-writer contract's consumption marking:
        // a reserve plan's pre-header name whose reserve an ffi.new mint
        // over that name already satisfied skips its own reserve — the
        // mint's reserve is the one reserve.
        let mint_caps: BTreeSet<&str> = self
            .chk
            .ffi_mints
            .values()
            .filter(|m| !m.name.is_empty())
            .map(|m| m.name.as_str())
            .collect();
        for plan in self.layout.reserve_plans.values_mut() {
            plan.pre_satisfied = plan
                .pre_header
                .iter()
                .filter(|n| mint_caps.contains(n.as_str()))
                .cloned()
                .collect();
        }

        ShapeFacts {
            sites: self.lattice.sites,
            elems: self.static_elems,
            layouts: self.layout.verdicts,
            free_sites: self.own.free_sites,
            free_keeps: self.own.free_keeps,
            do_exit_frees: self.own.do_exit_frees,
            root_exit_frees: self.own.root_exit_frees,
            stmt_temp_frees: self.own.stmt_temp_frees,
            cond_temp_frees: self.own.cond_temp_frees,
            arm_temp_frees: self.own.arm_temp_frees,
            rebind_frees: self.own.rebind_grants,
            move_poisons: self.own.move_poisons,
            fast_stores: self.layout.fast_stores,
            reserve_plans: self.layout.reserve_plans,
            stored_ctor_parents: self.own.stored_ctor_parents,
            substitutions,
            row_reads: std::mem::take(&mut self.reads.row_reads),
            cell_children,
            fn_scope_keys: self.fn_scope_keys,
            join_tags: self.join_tags,
            call_tags: self.call_tags,
            store_ghost_keeps: self.own.store_ghost_keeps,
            ctor_ghost_keeps: self.own.ctor_ghost_keeps,
            arm_free_sites: self.own.arm_free_sites,
            arm_rebind_frees: self.own.arm_rebind_frees,
            arm_do_exit_frees: self.own.arm_do_exit_frees,
            arm_root_exit_frees: self.own.arm_root_exit_frees,
            fn_touched: BTreeMap::new(),
            fn_body_depths: self.fn_body_depths,
            ctor_lines: self.ctor_lines,
            adopt_lines: self.adopt_lines,
            boundary_elem: self.chk.boundary_elem,
            local_types: self.chk.local_types,
            fn_defs: self.chk.fn_defs,
            env_faces: self.chk.env_faces,
            env_face_depths: self.chk.env_face_depths,
            fn_capture_depths: self.chk.fn_capture_depths,
            closure_fields: self.chk.closure_fields,
            call_fns: self.chk.call_fns,
            ffi_verbs: self.chk.ffi_verbs,
            builtin_verbs: self.chk.builtin_verbs,
            ffi_mints: self.chk.ffi_mints,
            instances: self.chk.instances,
            diagnostics,
        }
    }
}

fn get_base_identifier(expr: &Expr) -> Option<&String> {
    // C: index-chain classifier — same law as stmt_base above
    match expr {
        Expr::Identifier { name, .. } => Some(name),
        Expr::Index { obj, .. } => get_base_identifier(obj),
        Expr::Integer { .. }
        | Expr::Float { .. }
        | Expr::Boolean { .. }
        | Expr::String { .. }
        | Expr::Nil { .. }
        | Expr::TableCtor { .. }
        | Expr::BinaryOp { .. }
        | Expr::UnaryOp { .. }
        | Expr::SysAllocCount { .. }
        | Expr::SysExecCount { .. }
        | Expr::FfiModule { .. }
        | Expr::AsyncModule { .. }
        | Expr::Field { .. }
        | Expr::Function { .. }
        | Expr::Call { .. } => None,
    }
}

pub(super) fn dotted_callee(callee: &Expr) -> Option<String> {
    let Expr::Field { obj, name, .. } = callee else {
        return None;
    };
    let base = match obj.as_ref() {
        Expr::Identifier { name: b, .. } => b.clone(),
        Expr::Field { .. } => dotted_callee(obj.as_ref())?,
        _ => return None,
    };
    Some(format!("{base}.{name}"))
}

pub(super) fn value_call_msg(name: &str) -> Diagnostic {
    Diagnostic::ty(format!(
        "'{name}' is not an expansion — a call through a value \
         needs a closure"
    ))
}

pub(super) fn calls_through_fn_var_msg() -> Diagnostic {
    Diagnostic::ty(
        "calls go through a macro's name — only macros \
     assigned directly to variables are callable",
    )
}
