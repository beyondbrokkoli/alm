use crate::analysis::AnalysisContext;
use crate::ast::{BinOp, CtorKey, Expr, NodeId, Stmt, UnOp};
use alm_rt::{signal, trace};
use std::collections::{BTreeMap, BTreeSet};

use super::core::{
    BOUNDARY_ROOT, BOUNDS_FAIL_THRESHOLD, LayoutVerdict, MOVED_ROOT, NULL_ROOT, RowLineage,
    SPARSE_THRESHOLD, TableShape, is_ghost, is_root,
};
// H11: the diagnostic type, one name for every analyzer child (the
// `use super::*` globs below the mod decls reach it)
use super::facts;
use super::facts::{FillPlan, ShapeFacts};
use super::helpers::{const_key_value, extract_guard, merge_table_scopes};
use super::ty::{Ty, arith_ty, contains_any, decided, join_ty, pinned_scalar, value_kind};
pub(super) use crate::diag::Diagnostic;
use Ty::{Any, Bool, Conflict, Coro, Ffi, FfiLib, Flt, Int, Pending, Str, Tbl};

mod checker;
mod checks;
mod constraints;
mod exits;
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

/// A walk rejection — minted typed (H11); the pushing boundary stamps
/// the site off the statement's own line.
struct ShapeError(pub Diagnostic);

fn boundary_root_scope() -> BTreeMap<String, TableShape> {
    let mut scope = BTreeMap::new();
    scope.insert(
        "arg".to_string(),
        TableShape {
            ty: Tbl(Box::new(Pending)),
            layout: LayoutVerdict::default(),
            aliases: BTreeSet::from([BOUNDARY_ROOT]),
            lineage: BTreeMap::new(),
        },
    );
    scope
}

struct Ledger {
    diagnostics: Vec<Diagnostic>,
    conflict_reported: BTreeSet<usize>,
}

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

struct WalkState {
    scopes: Vec<BTreeMap<String, TableShape>>,
    fn_scopes: Vec<BTreeMap<String, Option<NodeId>>>,
    changed: bool,
    conv_fires: BTreeSet<u8>,
    prov: Vec<BTreeMap<String, Option<Prov>>>,
    /// per-scope scalar unknown nodes — bare-declaration slots and
    /// scalar aliases of node-carrying RHSes (`local mode = arg[0]`
    /// rides the seed). The use-site pinning discipline (pins.rs) reads
    /// this map; it mirrors the checker's scope entries for the
    /// scalar-unknown case only.
    scalar_nodes: Vec<BTreeMap<String, usize>>,
}

#[derive(Clone, Copy, PartialEq)]
enum Prov {
    If(NodeId),
    Call(NodeId),
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
    /// the unknown-constraint store — the lattice home of the nominal
    /// type variables (boundary seed, bare-declaration slots, fn return
    /// nodes, per-call parameter instances) and their substitution pins.
    /// The walk anchors the minting; the checking half constrains through
    /// `bind`/`unify`; the assembled facts derive `substitutions` from
    /// here. The checking half owns no algebra of its own.
    unknowns: constraints::UnknownStore,
}

struct GhostMint {
    bases: BTreeSet<usize>,
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
    ret_path_frees: BTreeMap<NodeId, Vec<super::facts::DoExitFree>>,
    break_path_frees: BTreeMap<NodeId, Vec<super::facts::DoExitFree>>,
    ret_path_keep_frees: BTreeMap<NodeId, Vec<super::facts::DoExitFree>>,
    ret_path_keep_temps: BTreeMap<NodeId, Vec<usize>>,
    rebind_grants: BTreeMap<NodeId, BTreeMap<String, Vec<super::facts::Keep>>>,
    stored_ctor_parents: BTreeSet<usize>,
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
    num_assigns: BTreeMap<String, Vec<NumExpr>>,
    // nil-slot law: sites a straight-line `t = nil` severed from the
    // name. The header is freed and the aliases are gone, but the name's
    // element slot survives — a later rebind's adoption bridge joins
    // these sites' elems (both directions), so the mix is name-global
    // across the nil exactly as it is across a plain rebind.
    nil_severed: BTreeMap<String, BTreeSet<usize>>,
    // the move flavor of the same law: sites an affine move
    // (`local u = t`) severed from the name. The binding becomes the
    // MOVED marker, but the name's element slot survives it exactly as
    // it survives a nil — a later rebind's adoption bridges the history,
    // and the severed-sites view answers the pre-move type (the
    // checking half's name→type view reads this through its snapshot).
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
    name_dense: BTreeMap<(String, usize), bool>,
    fill_loops: BTreeMap<NodeId, super::facts::FillPlan>,
    verdicts: Vec<LayoutVerdict>,
}

fn collect_body_sites(stmts: &[Stmt], sites: &BTreeMap<NodeId, usize>, out: &mut BTreeSet<usize>) {
    fn walk_stmt(s: &Stmt, sites: &BTreeMap<NodeId, usize>, out: &mut BTreeSet<usize>) {
        match s {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
                exprs.iter().for_each(|e| walk_expr(e, sites, out))
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr, .. } => walk_expr(expr, sites, out),
            Stmt::Break { .. } => {}
            Stmt::IndexAssign {
                obj, key, value, ..
            } => {
                walk_expr(obj, sites, out);
                walk_expr(key, sites, out);
                walk_expr(value, sites, out);
            }
            Stmt::While {
                condition, body, ..
            } => {
                walk_expr(condition, sites, out);
                body.iter().for_each(|s| walk_stmt(s, sites, out));
            }
            Stmt::Do { body, .. } => body.iter().for_each(|s| walk_stmt(s, sites, out)),
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                walk_expr(condition, sites, out);
                then_body.iter().for_each(|s| walk_stmt(s, sites, out));
                else_body.iter().for_each(|s| walk_stmt(s, sites, out));
            }
            Stmt::Return { value, .. } => {
                if let Some(e) = value {
                    walk_expr(e, sites, out);
                }
            }
        }
    }
    fn walk_expr(e: &Expr, sites: &BTreeMap<NodeId, usize>, out: &mut BTreeSet<usize>) {
        if let Some(&id) = sites.get(&e.id()) {
            out.insert(id);
        }
        match e {
            Expr::TableCtor { entries, .. } => {
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        walk_expr(ke, sites, out);
                    }
                    walk_expr(v, sites, out);
                }
            }
            Expr::Index { obj, key, .. } => {
                walk_expr(obj, sites, out);
                walk_expr(key, sites, out);
            }
            Expr::BinaryOp { left, right, .. } => {
                walk_expr(left, sites, out);
                walk_expr(right, sites, out);
            }
            Expr::UnaryOp { expr, .. } => walk_expr(expr, sites, out),
            Expr::Call { callee, args, .. } => {
                walk_expr(callee, sites, out);
                args.iter().for_each(|a| walk_expr(a, sites, out));
            }
            Expr::Function { body, .. } => body.iter().for_each(|s| walk_stmt(s, sites, out)),
            _ => {}
        }
    }
    stmts.iter().for_each(|s| walk_stmt(s, sites, out));
}

fn collect_stored_bases(stmts: &[Stmt]) -> BTreeSet<String> {
    fn walk_stmt(s: &Stmt, out: &mut BTreeSet<String>) {
        match s {
            Stmt::IndexAssign { obj, .. } => {
                if let Some(base) = stmt_base(obj) {
                    out.insert(base);
                }
                walk_obj_value(s, out);
            }
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
                exprs.iter().for_each(|e| walk_expr(e, out))
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr, .. } => walk_expr(expr, out),
            Stmt::While {
                condition, body, ..
            } => {
                walk_expr(condition, out);
                body.iter().for_each(|s| walk_stmt(s, out));
            }
            Stmt::Do { body, .. } => body.iter().for_each(|s| walk_stmt(s, out)),
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                walk_expr(condition, out);
                then_body.iter().for_each(|s| walk_stmt(s, out));
                else_body.iter().for_each(|s| walk_stmt(s, out));
            }
            Stmt::Return { value, .. } => {
                if let Some(e) = value {
                    walk_expr(e, out);
                }
            }
            Stmt::Break { .. } => {}
        }
    }
    fn walk_obj_value(s: &Stmt, out: &mut BTreeSet<String>) {
        if let Stmt::IndexAssign {
            obj, key, value, ..
        } = s
        {
            walk_expr(obj, out);
            walk_expr(key, out);
            walk_expr(value, out);
        }
    }
    fn walk_expr(e: &Expr, out: &mut BTreeSet<String>) {
        match e {
            Expr::TableCtor { entries, .. } => {
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        walk_expr(ke, out);
                    }
                    walk_expr(v, out);
                }
            }
            Expr::Index { obj, key, .. } => {
                walk_expr(obj, out);
                walk_expr(key, out);
            }
            Expr::BinaryOp { left, right, .. } => {
                walk_expr(left, out);
                walk_expr(right, out);
            }
            Expr::UnaryOp { expr, .. } => walk_expr(expr, out),
            Expr::Call { callee, args, .. } => {
                walk_expr(callee, out);
                args.iter().for_each(|a| walk_expr(a, out));
            }
            Expr::Function { body, .. } => body.iter().for_each(|s| walk_stmt(s, out)),
            _ => {}
        }
    }
    fn stmt_base(e: &Expr) -> Option<String> {
        match e {
            Expr::Identifier { name: n, .. } => Some(n.clone()),
            Expr::Index { obj, .. } => stmt_base(obj),
            _ => None,
        }
    }
    let mut out = BTreeSet::new();
    stmts.iter().for_each(|s| walk_stmt(s, &mut out));
    out
}

struct Analyzer {
    walk: WalkState,
    ledger: Ledger,
    lattice: LatticeState,
    own: OwnershipState,
    holds: HoldsState,
    reads: ReadSideState,
    layout: LayoutFactsState,
    /// the differential lever (see `analyze_with`): false disarms the
    /// walk-side use-site pins so only the checker's own land.
    walk_pins: bool,
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
    /// the Hygiene Law's definition-side record: per fn literal, the
    /// defining-scope chain snapshot taken at its definition walk (see
    /// `walk_fn_def`). Read by the checking half's call resolution.
    fn_def_sites: BTreeMap<NodeId, BTreeMap<String, Option<NodeId>>>,
    /// W3a's capture sets (the invariance argument lives HERE, fold d
    /// B4 style): per fn literal, the enclosing-scope (below-top-level)
    /// non-fn names its body transitively reads. WHICH names a body
    /// captures is AST-structural (the chain snapshot plus the body's
    /// transitive free names, nested literals as holes), hence
    /// instantiation-INVARIANT — recorded once by the walk at the
    /// definition, consumed by the checking half (env faces, capture
    /// guard). The CELL TYPES are per-instantiation checker territory
    /// (`env_faces`).
    fn_captures: BTreeMap<NodeId, BTreeSet<String>>,
    loop_scope_entries: Vec<usize>,
}

/// `walk_pins` arms the walk's use-site pins. The one pipeline (H10) is
/// the only caller: the shipped path (main.rs's driver) always passes
/// `true`; `false` is the differential leg's lever (the pin-owed
/// register, census §3 cluster A row 3): the walk's use-site pins are
/// a documented SUBSET of the checker's own — with the lever off, the
/// checker's pins alone must land the identical constraint store,
/// hence the identical facts, hence the identical pipeline output. The
/// property harness asserts exactly that over the whole corpus and the
/// generated programs (`walk_pins_are_a_pure_subset_over_the_corpus`).
pub fn analyze_with(ctx: &AnalysisContext<'_>, walk_pins: bool) -> ShapeFacts {
    let n = ctx.sites.len();
    let mut a = Analyzer {
        walk_pins,
        walk: WalkState {
            scopes: vec![boundary_root_scope()],
            fn_scopes: vec![BTreeMap::new()],
            changed: false,
            conv_fires: BTreeSet::new(),
            prov: vec![BTreeMap::new()],
            scalar_nodes: vec![BTreeMap::new()],
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
            ret_path_frees: BTreeMap::new(),
            break_path_frees: BTreeMap::new(),
            ret_path_keep_frees: BTreeMap::new(),
            ret_path_keep_temps: BTreeMap::new(),
            rebind_grants: BTreeMap::new(),
            stored_ctor_parents: BTreeSet::new(),
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
            fill_loops: BTreeMap::new(),
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
        loop_scope_entries: Vec::new(),
    };

    let mut prev_end: Vec<BTreeMap<String, TableShape>> = Vec::new();
    let mut dbg_pass: u32 = 0;
    loop {
        dbg_pass += 1;
        crate::alm_dbgln!("[fixpoint] pass {dbg_pass}");
        a.walk.changed = false;
        a.walk.scopes = vec![boundary_root_scope()];
        a.walk.fn_scopes = vec![BTreeMap::new()];
        a.walk.prov = vec![BTreeMap::new()];
        a.walk.scalar_nodes = vec![BTreeMap::new()];
        a.fn_def_sites.clear();
        a.fn_captures.clear();
        a.walk_stmts(None, ctx.ast);
        let end = a.walk.scopes.clone();
        let stable = end == prev_end && !a.walk.changed;
        prev_end = end;
        if stable {
            break;
        }
    }

    for slot in std::mem::take(&mut a.walk.conv_fires) {
        trace::compiler_trace_signal(slot);
    }

    // ---- ONE walk, recorded once ----
    // The lattice is final now (the fixpoint converged), so the
    // acceptance inputs are computable BEFORE the recorded pass: the
    // adoption lines and the static-elem table (the same table
    // into_facts carries out — one definition of the elem truth, read
    // by both halves of the walk).
    // Computed from the fixpoint's final scope state, which the recorded
    // pass reproduces (that is what convergence means).
    let adopt_lines: BTreeMap<String, usize> = {
        let mut m = BTreeMap::new();
        for scope in a.walk.scopes.iter() {
            for (name, shape) in scope {
                let mut best: Option<usize> = None;
                for s in shape.aliases.iter() {
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

    // Fixpoint passes may error transiently (a scope that converges away
    // from the error); the recorded pass is the truth — drop the echoes
    // BEFORE the elem table drains the ledger into its own diagnostic
    // list, or the echoes would ride out inside elems_diags.
    a.ledger.diagnostics.clear();
    let (static_elems, elems_diags) = a.compute_static_elems(n);

    let rec: Gate = Some(Recording { _priv: () });
    a.walk.scopes = vec![boundary_root_scope()];
    a.walk.fn_scopes = vec![BTreeMap::new()];
    a.walk.prov = vec![BTreeMap::new()];
    a.walk.scalar_nodes = vec![BTreeMap::new()];

    // The recorded pass drives BOTH halves per top-level statement, in
    // program order: lattice machinery first, then the checker (its own
    // recursion covers nested bodies — each statement is checked exactly
    // once, loop fixpoint iterations never re-fire it). The checker only
    // ever ran on a clean analyzer diagnostic list; keep that contract.
    // The walk runs one statement AHEAD of the checker, so the checker
    // reads the walk's state through two snapshots per statement: before
    // the statement's walk (its queries) and after it (its fresh
    // declarations' view compare).
    let mut chk = checker::Checker::new(checker::CheckCtx {
        adopt_lines: adopt_lines.clone(),
        sites: a.lattice.sites.clone(),
        elems: static_elems.clone(),
        fn_def_sites: a.fn_def_sites.clone(),
        fn_captures: a.fn_captures.clone(),
    });
    let mut checker_ran = elems_diags.is_empty();
    // The interleaving pin (census §3 cluster A row 1): the checker's
    // pre-statement snapshot must read the walk's UNCHANGED post-state
    // of the previous statement — nothing walks between the two
    // snapshots, and the walk runs one statement ahead of the checker.
    // A driver that walked first would hand the checker a post-walk
    // snapshot where a pre-walk one is due, and this census fires.
    let mut last_post: Option<Vec<BTreeMap<String, TableShape>>> = None;
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
            signal!(rec.on(), trace::TRACE_GHOST_BAIL);
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
            signal!(trace::TRACE_GHOST_BAIL_CHECKER);
            if msg.is_desync() {
                signal!(trace::TRACE_ENG_DESYNC);
            }
            a.ledger
                .diagnostics
                .push(msg.with_site(Some(stmt.loc().line as usize)));
            // a top-level checker error stops the walk, but the closing
            // moves still run — the standalone pass did the same
            walk_completed = false;
            break;
        }
    }
    // The reproduction pin (census §3 cluster A row 2): the recorded
    // pass reproduces the fixpoint's final scope state — that is what
    // convergence means, and it is the whole soundness of computing
    // `adopt_lines`/`static_elems` from the fixpoint's end before the
    // recorded pass runs. Gated on a clean walk: a rejected program
    // stops mid-stream by design.
    if walk_completed {
        debug_assert_eq!(
            a.walk.scopes, prev_end,
            "the recorded pass diverged from the fixpoint's converged end state"
        );
    }
    // The id-space census (census §3 cluster C row 21): the four id
    // families — real site ids 0..n, static-elem ghosts counting DOWN
    // from ROW_GHOST_FLOOR, row ghosts counting UP from
    // ROW_GHOST_FLOOR+1, unknown nodes counting DOWN from usize::MAX.
    // The two ghost families are disjoint BY CONSTRUCTION (floor-
    // adjacent, growing apart); the one genuinely approaching pair is
    // row ghosts ↑ vs the unknown-node minter ↓ — the census is their
    // headroom check.
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

    let mut facts = a
        .into_recorded(adopt_lines, static_elems, elems_diags, chk_facts)
        .into_facts();
    // the fn-touched map rides the context (H7: the scan folded into
    // the one derivation pass — purely syntactic, nothing walk-side
    // feeds it, so the old post-walk call site bought nothing)
    facts.fn_touched = ctx.fn_touched.clone();
    // the row-read discipline is the analysis's final acceptance gate
    facts.check_row_reads();
    // H12/7a — THE SHADOW: the instance view must equal the pair view
    // on EVERY compile (assembly-side, over the self-contained facts —
    // H6's dividend; never in the lowerer, whose replacement this is).
    // Third of the census breed (desugar attribution, identity, this).
    assert_instance_shadow(&facts);
    facts
}

/// H12/7a's every-compile shadow: the instance-keyed view (minted
/// ALONGSIDE every pair-keyed insert by the checker) must equal the
/// pair-keyed view, every compile, clean or rejected — 7b consumes
/// the instance view, 7c kills the pair view, and this assert is the
/// dual-run oracle that keeps the two halves honest in between (the
/// H5 playbook, worked twice). The laws, each loud by name:
///
/// - OWNERSHIP: every bridge entry `(expr, site) → owner` names the
///   instance minted for `site`'s own expansion (a top-level
///   self-pair — `expr == site` — owns to ROOT; every nested pair
///   owns to the outermost expansion's instance, whatever the
///   lexical depth — the site law).
/// - AGREEMENT: for every pair present in a pair map, the owner's (or
///   child's) instance view carries the SAME truth — call_defs →
///   fn_node, call_rets → ret, index_key_lanes / access_elems /
///   creation_envs / closure_calls → the owner's shadow maps.
/// - REVERSE: no shadow entry without its pair (the instance view
///   invents nothing).
/// - TOTALITY: every pair key is bridged, every bridge key has its
///   pair, every instance is reachable from ROOT through the children
///   maps. Exact on CLEAN compiles only: a rejected program stops
///   mid-stream by design, and a post-mint reject (a parameter
///   unification refusing after the entry mint) leaves a minted but
///   unbRIDged instance — allowed exactly when diagnostics exist.
fn assert_instance_shadow(facts: &ShapeFacts) {
    let root = facts::InstanceId::ROOT;
    // R2's convention, held every compile: ROOT is nobody's call and
    // nobody's callee, the top level's bases are zero, and it owns no
    // params or body (7c rules the root's face when `local_types`
    // re-keys — until then the emptiness IS the convention).
    if let Some(root_rec) = facts.instances.get(&root) {
        assert!(
            root_rec.call.is_none()
                && root_rec.fn_node.is_none()
                && root_rec.ret.is_none()
                && root_rec.env_face.is_none(),
            "the shadow (7a): ROOT is nobody's call — the top-level convention"
        );
        assert_eq!(
            (root_rec.frame_base, root_rec.break_base),
            (0, 0),
            "the shadow (7a): the top level's bases are zero"
        );
        assert!(
            root_rec.params.is_empty() && root_rec.body.is_empty(),
            "the shadow (7a): ROOT owns no params or body"
        );
    }
    for ((expr, site), &owner) in &facts.instance_of {
        let owner_rec = facts.instances.get(&owner).unwrap_or_else(|| {
            panic!("the shadow (7a): the bridge names instance {owner:?} with no record")
        });
        // OWNERSHIP: the owner is `site`'s own instance (ROOT for a
        // top-level self-pair — an expr cannot sit inside its own
        // expansion, so `expr == site` names top level and nothing
        // else ever does).
        assert_eq!(
            owner_rec.call,
            if *expr == *site { None } else { Some(*site) },
            "the shadow (7a): pair ({expr:?}, {site:?}) bridged to the wrong owner"
        );
        // AGREEMENT, map by map, for the maps that carry this pair.
        if let Some(&fn_ptr) = facts.call_defs.get(&(*expr, *site)) {
            let kids = owner_rec.children.get(expr).unwrap_or_else(|| {
                panic!("the shadow (7a): call pair ({expr:?}, {site:?}) has no child instance")
            });
            assert!(
                !kids.is_empty(),
                "the shadow (7a): call pair ({expr:?}, {site:?}) has an empty children set"
            );
            for &kid in kids {
                let krec = facts.instances.get(&kid).unwrap_or_else(|| {
                    panic!("the shadow (7a): children names instance {kid:?} with no record")
                });
                assert_eq!(
                    krec.call,
                    Some(*expr),
                    "the shadow (7a): a child of ({expr:?}, {site:?}) mints a different call"
                );
                assert_eq!(
                    krec.fn_node,
                    Some(fn_ptr),
                    "the shadow (7a): the instance view of call_defs ({expr:?}, {site:?}) disagrees"
                );
                assert_eq!(
                    krec.ret.as_ref(),
                    facts.call_rets.get(&(*expr, *site)),
                    "the shadow (7a): the instance view of call_rets ({expr:?}, {site:?}) disagrees"
                );
            }
        }
        if let Some(&lane) = facts.index_key_lanes.get(&(*expr, *site)) {
            assert_eq!(
                owner_rec.index_key_lanes.get(expr),
                Some(&lane),
                "the shadow (7a): the instance view of index_key_lanes ({expr:?}, {site:?}) disagrees"
            );
        }
        if let Some(face) = facts.access_elems.get(&(*expr, *site)) {
            assert_eq!(
                owner_rec.access_elems.get(expr),
                Some(face),
                "the shadow (7a): the instance view of access_elems ({expr:?}, {site:?}) disagrees"
            );
        }
        if let Some(&lit) = facts.creation_envs.get(&(*expr, *site)) {
            assert_eq!(
                owner_rec.creation_envs.get(expr),
                Some(&lit),
                "the shadow (7a): the instance view of creation_envs ({expr:?}, {site:?}) disagrees"
            );
        }
        if facts.closure_calls.contains(&(*expr, *site)) {
            assert!(
                owner_rec.closure_calls.contains(expr),
                "the shadow (7a): the instance view of closure_calls ({expr:?}, {site:?}) disagrees"
            );
        }
    }
    // REVERSE + TOTALITY over the records: every shadow entry has its
    // pair (keyed by the record's own call expr — the site law), every
    // children value is a real instance.
    for (&inst, rec) in &facts.instances {
        let pair_of = |e: NodeId| match rec.call {
            None => (e, e),
            Some(call) => (e, call),
        };
        for (&e, &lane) in &rec.index_key_lanes {
            assert_eq!(
                facts.index_key_lanes.get(&pair_of(e)),
                Some(&lane),
                "the shadow (7a): instance {inst:?} carries a lane with no pair"
            );
        }
        for (&e, face) in &rec.access_elems {
            assert_eq!(
                facts.access_elems.get(&pair_of(e)),
                Some(face),
                "the shadow (7a): instance {inst:?} carries an elem face with no pair"
            );
        }
        for (&e, &lit) in &rec.creation_envs {
            assert_eq!(
                facts.creation_envs.get(&pair_of(e)),
                Some(&lit),
                "the shadow (7a): instance {inst:?} carries a creation site with no pair"
            );
        }
        for &e in &rec.closure_calls {
            assert!(
                facts.closure_calls.contains(&pair_of(e)),
                "the shadow (7a): instance {inst:?} carries a closure call with no pair"
            );
        }
        for (&e, kids) in &rec.children {
            assert!(
                facts.call_defs.contains_key(&pair_of(e)),
                "the shadow (7a): instance {inst:?} names child call {e:?} with no call_defs pair"
            );
            for &kid in kids {
                assert!(
                    facts.instances.contains_key(&kid),
                    "the shadow (7a): instance {inst:?} names child instance {kid:?} with no record"
                );
            }
        }
    }
    // TOTALITY, forward: every pair key in the six maps is bridged.
    for (expr, site) in facts.call_defs.keys() {
        assert!(
            facts.instance_of.contains_key(&(*expr, *site)),
            "the shadow (7a): call_defs pair ({expr:?}, {site:?}) has no bridge entry"
        );
    }
    for (expr, site) in facts.call_rets.keys() {
        assert!(
            facts.instance_of.contains_key(&(*expr, *site)),
            "the shadow (7a): call_rets pair ({expr:?}, {site:?}) has no bridge entry"
        );
    }
    for (expr, site) in facts.index_key_lanes.keys() {
        assert!(
            facts.instance_of.contains_key(&(*expr, *site)),
            "the shadow (7a): index_key_lanes pair ({expr:?}, {site:?}) has no bridge entry"
        );
    }
    for (expr, site) in facts.access_elems.keys() {
        assert!(
            facts.instance_of.contains_key(&(*expr, *site)),
            "the shadow (7a): access_elems pair ({expr:?}, {site:?}) has no bridge entry"
        );
    }
    for (expr, site) in facts.creation_envs.keys() {
        assert!(
            facts.instance_of.contains_key(&(*expr, *site)),
            "the shadow (7a): creation_envs pair ({expr:?}, {site:?}) has no bridge entry"
        );
    }
    for (expr, site) in &facts.closure_calls {
        assert!(
            facts.instance_of.contains_key(&(*expr, *site)),
            "the shadow (7a): closure_calls pair ({expr:?}, {site:?}) has no bridge entry"
        );
    }
    // TOTALITY, clean-compile leg: every instance is reachable from
    // ROOT through the children maps (a rejected program may stop
    // mid-stream past a mint — that is the diagnostics gate below).
    if facts.diagnostics.is_empty() {
        let mut reached = BTreeSet::from([root]);
        for rec in facts.instances.values() {
            reached.extend(rec.children.values().flatten().copied());
        }
        for &inst in facts.instances.keys() {
            assert!(
                reached.contains(&inst),
                "the shadow (7a): instance {inst:?} is unreachable from ROOT on a clean compile"
            );
        }
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
    join_tags: BTreeMap<NodeId, bool>,
    call_tags: BTreeMap<NodeId, Vec<bool>>,
    adopt_lines: BTreeMap<String, usize>,
    /// the single elem table, computed once post-fixpoint — the same
    /// values the checker checked against ride out in the facts
    static_elems: Vec<crate::shape::Ty>,
    /// the elem table's own diagnostics (pending/missing/conflict/
    /// nested-store/cyclic), appended after the walk's
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
            join_tags: self.join_tags,
            call_tags: self.call_tags,
            adopt_lines,
            static_elems,
            elems_diags,
            chk,
        }
    }

    /// The static-elem table, computed BEFORE the recorded pass so the
    /// checker checks against the exact table the assembled facts will
    /// carry. Diagnostics land in the ledger and are
    /// drained out here (the walk clears it anyway).
    fn compute_static_elems(&mut self, n: usize) -> (Vec<crate::shape::Ty>, Vec<Diagnostic>) {
        let mut elems: Vec<crate::shape::Ty> = (0..n).map(crate::shape::Ty::Unknown).collect();

        let site_ids: Vec<usize> = self.lattice.sites.values().copied().collect();
        for id in site_ids {
            if self.lattice.needed[id] && self.lattice.site_elem[id] == Pending {
                if self.fn_body_sites.contains(&id) || self.fn_param_sites.contains(&id) {
                    signal!(trace::TRACE_ANALYZE_PENDING);
                    elems[id] = crate::shape::Ty::Unknown(id);
                    continue;
                }
                if self.reads.boundary_fed.contains(&id) {
                    signal!(trace::TRACE_ANALYZE_PENDING);
                    elems[id] = crate::shape::Ty::Unknown(id);
                    continue;
                }
                signal!(trace::TRACE_ANALYZE_MISSING_VALUE);
                let line = self.ctor_lines[id];
                self.ledger.diagnostics.push(
                    Diagnostic::ty(format!(
                        "a table is read before it is ever given a value (table site #{id})"
                    ))
                    .with_site(Some(line)),
                );
                elems[id] = crate::shape::Ty::Unknown(id);
            } else if self.lattice.site_elem[id] == Pending {
                signal!(trace::TRACE_ANALYZE_PENDING);
                elems[id] = crate::shape::Ty::Unknown(id);
            } else {
                signal!(trace::TRACE_ANALYZE_RESOLVED);
                elems[id] = self.elem_type_of_tbl(id);
            }
        }

        for (&site, name) in &self.reads.nested_store_bases {
            if !self.reads.tbl_value_stores.contains(&site) {
                signal!(trace::TRACE_STMT_IDX_NULL_ROW);
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
            signal!(trace::TRACE_FAIL_CYCLIC_STORE);
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

        // the substitution fact is derived from the lattice's constraint
        // store — one home for every pin the checking half recorded
        let substitutions = self.lattice.unknowns.take_subs();

        let mut cell_children = self.lattice.child_sites.clone();
        for (parent, kids) in std::mem::take(&mut self.reads.row_links) {
            cell_children.entry(parent).or_default().extend(kids);
        }

        ShapeFacts {
            sites: self.lattice.sites,
            elems: self.static_elems,
            boundary_elem: self.chk.boundary_elem,
            layouts: self.layout.verdicts,
            free_sites: self.own.free_sites,
            free_keeps: self.own.free_keeps,
            do_exit_frees: self.own.do_exit_frees,
            root_exit_frees: self.own.root_exit_frees,
            stmt_temp_frees: self.own.stmt_temp_frees,
            cond_temp_frees: self.own.cond_temp_frees,
            arm_temp_frees: self.own.arm_temp_frees,
            ret_path_frees: self.own.ret_path_frees,
            break_path_frees: self.own.break_path_frees,
            ret_path_keep_frees: self.own.ret_path_keep_frees,
            ret_path_keep_temps: self.own.ret_path_keep_temps,
            rebind_frees: self.own.rebind_grants,
            move_poisons: self.own.move_poisons,
            name_dense: self.layout.name_dense,
            fill_loops: self.layout.fill_loops,
            stored_ctor_parents: self.own.stored_ctor_parents,
            substitutions,
            local_types: self.chk.local_types,
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
            fn_defs: self.chk.fn_defs,
            env_faces: self.chk.env_faces,
            creation_envs: self.chk.creation_envs,
            closure_calls: self.chk.closure_calls,
            closure_fields: self.chk.closure_fields,
            call_defs: self.chk.call_defs,
            call_rets: self.chk.call_rets,
            ffi_verbs: self.chk.ffi_verbs,
            index_key_lanes: self.chk.index_key_lanes,
            access_elems: self.chk.access_elems,
            instances: self.chk.instances,
            instance_of: self.chk.instance_of,
            ctor_lines: self.ctor_lines,
            adopt_lines: self.adopt_lines,
            diagnostics,
        }
    }
}

fn get_base_identifier(expr: &Expr) -> Option<&String> {
    match expr {
        Expr::Identifier { name, .. } => Some(name),
        Expr::Index { obj, .. } => get_base_identifier(obj),
        _ => None,
    }
}

/// W3a's value-call diagnostic: a callee name that is neither an
/// expansion nor a closure value (a plain scalar/table read in call
/// position). The old text claimed values are never callable; the
/// closure value is. Both halves would print this exact text —
/// whichever fires first (post-W3a the walk tolerates value calls, so
/// the checker owns the reject).
pub(super) fn value_call_msg(name: &str) -> Diagnostic {
    Diagnostic::ty(format!(
        "'{name}' is not an expansion — a call through a value \
         needs a closure"
    ))
}

/// Flatten a dotted callee chain (`A.b`, `A.B.c`, …) into its ONE
/// string key. None when the chain does not bottom out at a plain
/// identifier (that face is a module-surface call, not a name).
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

/// The ONE non-identifier-callee diagnostic, same discipline as
/// `not_a_function_msg`.
pub(super) fn calls_through_fn_var_msg() -> Diagnostic {
    Diagnostic::ty(
        "calls go through a macro's name — only macros \
     assigned directly to variables are callable",
    )
}
