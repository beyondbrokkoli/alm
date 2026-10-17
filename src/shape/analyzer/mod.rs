use crate::analysis::AnalysisContext;
use crate::ast::{BinOp, CtorKey, Expr, Stmt, UnOp};
use glm_rt::{signal, trace};
use std::collections::{BTreeMap, BTreeSet};

use super::core::{
    BOUNDARY_ROOT, BOUNDS_FAIL_THRESHOLD, LayoutVerdict, MOVED_ROOT, NULL_ROOT, RowLineage,
    SPARSE_THRESHOLD, TableShape, is_ghost, is_root,
};
use super::facts;
use super::facts::ShapeFacts;
use super::helpers::{const_key_value, extract_guard, merge_table_scopes};
use super::ty::{Ty, arith_ty, contains_any, join_ty, pinned_scalar, value_kind};
use Ty::{Any, Bool, Conflict, Coro, Ffi, FfiLib, Flt, Int, Pending, Str, Tbl};

mod checks;
mod exits;
mod functions;
mod infer;
mod lattice;
mod rebind;
mod rows;
mod walk;

use infer::*;
use lattice::*;
use rebind::*;
use rows::*;

struct ShapeError(String);

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
    diagnostics: Vec<String>,
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
    fn_scopes: Vec<BTreeMap<String, Option<*const Expr>>>,
    changed: bool,
    conv_fires: BTreeSet<u8>,
    prov: Vec<BTreeMap<String, Option<Prov>>>,
}

#[derive(Clone, Copy, PartialEq)]
enum Prov {
    If(*const Stmt),
    Call(*const Expr),
}

struct LatticeState {
    sites: BTreeMap<*const Expr, usize>,
    site_elem: Vec<Ty>,
    needed: Vec<bool>,
    child_sites: BTreeMap<usize, BTreeSet<usize>>,
    ghost_next: usize,
    row_ghosts: BTreeMap<*const Expr, usize>,
    row_ghost_next: usize,
    ghost_mints: BTreeMap<usize, GhostMint>,
    site_slots: BTreeMap<usize, BTreeMap<i64, usize>>,
    ghost_site: BTreeMap<usize, usize>,
    housed_ghosts: BTreeSet<usize>,
    claimed_ghosts: BTreeSet<usize>,
    adopt_witness: BTreeMap<usize, usize>,
}

struct GhostMint {
    bases: BTreeSet<usize>,
    key: Option<i64>,
}

struct OwnershipState {
    free_sites: BTreeSet<*const Stmt>,
    free_keeps: BTreeMap<*const Stmt, Vec<super::facts::Keep>>,
    do_exit_frees: BTreeMap<(*const Stmt, u8), Vec<super::facts::DoExitFree>>,
    root_exit_frees: Vec<super::facts::DoExitFree>,
    stmt_temp_frees: BTreeMap<*const Stmt, Vec<usize>>,
    cond_temp_frees: BTreeMap<*const Stmt, Vec<usize>>,
    arm_temp_frees: BTreeMap<*const Expr, Vec<usize>>,
    ret_path_frees: BTreeMap<*const Stmt, Vec<super::facts::DoExitFree>>,
    ret_path_keep_frees: BTreeMap<*const Stmt, Vec<super::facts::DoExitFree>>,
    ret_path_keep_temps: BTreeMap<*const Stmt, Vec<usize>>,
    rebind_grants: BTreeMap<*const Stmt, BTreeMap<String, Vec<super::facts::Keep>>>,
    stored_ctor_parents: BTreeSet<usize>,
    move_poisons: BTreeMap<*const Stmt, BTreeSet<String>>,
    store_ghost_keeps: BTreeMap<*const Stmt, Vec<usize>>,
    ctor_ghost_keeps: BTreeMap<*const Expr, Vec<(usize, usize)>>,
    arm_free_sites: BTreeMap<*const Stmt, Vec<super::facts::ArmFreeEntry>>,
    arm_rebind_frees: BTreeMap<*const Stmt, Vec<super::facts::ArmFreeEntry>>,
    arm_do_exit_frees: BTreeMap<(*const Stmt, u8), Vec<super::facts::ArmFreeEntry>>,
    arm_root_exit_frees: Vec<super::facts::ArmFreeEntry>,
}

struct HoldsState {
    hold_edges: BTreeMap<usize, BTreeSet<usize>>,
    cyclic_stores: BTreeMap<String, (String, usize)>,
    num_assigns: BTreeMap<String, Vec<NumExpr>>,
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
    verdicts: Vec<LayoutVerdict>,
}

fn collect_body_sites(
    stmts: &[Stmt],
    sites: &BTreeMap<*const Expr, usize>,
    out: &mut BTreeSet<usize>,
) {
    fn walk_stmt(s: &Stmt, sites: &BTreeMap<*const Expr, usize>, out: &mut BTreeSet<usize>) {
        match s {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs } => {
                exprs.iter().for_each(|e| walk_expr(e, sites, out))
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr } => walk_expr(expr, sites, out),
            Stmt::IndexAssign { obj, key, value } => {
                walk_expr(obj, sites, out);
                walk_expr(key, sites, out);
                walk_expr(value, sites, out);
            }
            Stmt::While { condition, body } => {
                walk_expr(condition, sites, out);
                body.iter().for_each(|s| walk_stmt(s, sites, out));
            }
            Stmt::Do { body } => body.iter().for_each(|s| walk_stmt(s, sites, out)),
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                walk_expr(condition, sites, out);
                then_body.iter().for_each(|s| walk_stmt(s, sites, out));
                else_body.iter().for_each(|s| walk_stmt(s, sites, out));
            }
            Stmt::Return { value } => {
                if let Some(e) = value {
                    walk_expr(e, sites, out);
                }
            }
        }
    }
    fn walk_expr(e: &Expr, sites: &BTreeMap<*const Expr, usize>, out: &mut BTreeSet<usize>) {
        if let Some(&id) = sites.get(&(e as *const Expr)) {
            out.insert(id);
        }
        match e {
            Expr::TableCtor(entries) => {
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        walk_expr(ke, sites, out);
                    }
                    walk_expr(v, sites, out);
                }
            }
            Expr::Index { obj, key } => {
                walk_expr(obj, sites, out);
                walk_expr(key, sites, out);
            }
            Expr::BinaryOp { left, right, .. } => {
                walk_expr(left, sites, out);
                walk_expr(right, sites, out);
            }
            Expr::UnaryOp { expr, .. } => walk_expr(expr, sites, out),
            Expr::Call { callee, args } => {
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
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs } => {
                exprs.iter().for_each(|e| walk_expr(e, out))
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr } => walk_expr(expr, out),
            Stmt::While { condition, body } => {
                walk_expr(condition, out);
                body.iter().for_each(|s| walk_stmt(s, out));
            }
            Stmt::Do { body } => body.iter().for_each(|s| walk_stmt(s, out)),
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                walk_expr(condition, out);
                then_body.iter().for_each(|s| walk_stmt(s, out));
                else_body.iter().for_each(|s| walk_stmt(s, out));
            }
            Stmt::Return { value } => {
                if let Some(e) = value {
                    walk_expr(e, out);
                }
            }
        }
    }
    fn walk_obj_value(s: &Stmt, out: &mut BTreeSet<String>) {
        if let Stmt::IndexAssign { obj, key, value } = s {
            walk_expr(obj, out);
            walk_expr(key, out);
            walk_expr(value, out);
        }
    }
    fn walk_expr(e: &Expr, out: &mut BTreeSet<String>) {
        match e {
            Expr::TableCtor(entries) => {
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        walk_expr(ke, out);
                    }
                    walk_expr(v, out);
                }
            }
            Expr::Index { obj, key } => {
                walk_expr(obj, out);
                walk_expr(key, out);
            }
            Expr::BinaryOp { left, right, .. } => {
                walk_expr(left, out);
                walk_expr(right, out);
            }
            Expr::UnaryOp { expr, .. } => walk_expr(expr, out),
            Expr::Call { callee, args } => {
                walk_expr(callee, out);
                args.iter().for_each(|a| walk_expr(a, out));
            }
            Expr::Function { body, .. } => body.iter().for_each(|s| walk_stmt(s, out)),
            _ => {}
        }
    }
    fn stmt_base(e: &Expr) -> Option<String> {
        match e {
            Expr::Identifier(n) => Some(n.clone()),
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
    stmt_lines: BTreeMap<*const Stmt, usize>,
    ctor_lines: Vec<usize>,
    fn_rets: Vec<Option<TableShape>>,
    fn_edge_frames: Vec<Vec<TableShape>>,
    fn_ret_shapes: BTreeMap<*const Expr, TableShape>,
    fn_ret_edge_shapes: BTreeMap<*const Expr, Vec<TableShape>>,
    join_arm_shapes: BTreeMap<(*const Stmt, String), (TableShape, TableShape)>,
    join_tags: BTreeMap<*const Stmt, bool>,
    call_tags: BTreeMap<*const Expr, Vec<bool>>,
    fn_scope_keys: BTreeMap<*const Expr, (*const Stmt, u8)>,
    fn_body_sites: BTreeSet<usize>,
    fn_params: BTreeMap<*const Expr, Vec<String>>,
    fn_store_params: BTreeMap<*const Expr, BTreeSet<String>>,
    fn_param_sites: BTreeSet<usize>,
    fn_moved_params: BTreeMap<*const Expr, BTreeSet<String>>,
    fn_ret_params: BTreeMap<*const Expr, BTreeSet<usize>>,
    fn_ret_reach: BTreeMap<*const Expr, BTreeSet<usize>>,
    fn_ret_reaches: Vec<BTreeSet<usize>>,
    fn_walk: Vec<(*const Expr, Vec<String>)>,
    fn_scope_entries: Vec<usize>,
}

pub fn analyze(ctx: &AnalysisContext<'_>) -> ShapeFacts {
    let n = ctx.sites.len();
    let mut a = Analyzer {
        walk: WalkState {
            scopes: vec![boundary_root_scope()],
            fn_scopes: vec![BTreeMap::new()],
            changed: false,
            conv_fires: BTreeSet::new(),
            prov: vec![BTreeMap::new()],
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
            verdicts: vec![LayoutVerdict::Growing; n],
        },
        stmt_lines: ctx.stmt_lines.clone(),
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
    };

    let mut prev_end: Vec<BTreeMap<String, TableShape>> = Vec::new();
    loop {
        a.walk.changed = false;
        a.walk.scopes = vec![boundary_root_scope()];
        a.walk.fn_scopes = vec![BTreeMap::new()];
        a.walk.prov = vec![BTreeMap::new()];
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

    let rec: Gate = Some(Recording { _priv: () });
    a.walk.scopes = vec![boundary_root_scope()];
    a.walk.fn_scopes = vec![BTreeMap::new()];
    a.walk.prov = vec![BTreeMap::new()];
    a.ledger.diagnostics.clear();
    a.walk_stmts(rec, ctx.ast);

    if let Err(err) = a.decide_root_exit(rec) {
        a.ledger.diagnostics.push(err.0);
    }
    a.plan_stmt_temp_frees(ctx.ast);

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

    let mut facts = a.into_recorded(adopt_lines).into_facts(n);
    facts.fn_touched = crate::analysis::scan_fn_touched(ctx.ast);
    facts
}

struct Recorded {
    recording: bool,
    ledger: Ledger,
    lattice: LatticeState,
    own: OwnershipState,
    holds: HoldsState,
    reads: ReadSideState,
    layout: LayoutFactsState,
    stmt_lines: BTreeMap<*const Stmt, usize>,
    ctor_lines: Vec<usize>,
    fn_scope_keys: BTreeMap<*const Expr, (*const Stmt, u8)>,
    fn_body_sites: BTreeSet<usize>,
    fn_param_sites: BTreeSet<usize>,
    join_tags: BTreeMap<*const Stmt, bool>,
    call_tags: BTreeMap<*const Expr, Vec<bool>>,
    adopt_lines: BTreeMap<String, usize>,
}

impl Analyzer {
    fn into_recorded(self, adopt_lines: BTreeMap<String, usize>) -> Recorded {
        Recorded {
            recording: true,
            ledger: self.ledger,
            lattice: self.lattice,
            own: self.own,
            holds: self.holds,
            reads: self.reads,
            layout: self.layout,
            stmt_lines: self.stmt_lines,
            ctor_lines: self.ctor_lines,
            fn_scope_keys: self.fn_scope_keys,
            fn_body_sites: self.fn_body_sites,
            fn_param_sites: self.fn_param_sites,
            join_tags: self.join_tags,
            call_tags: self.call_tags,
            adopt_lines,
        }
    }
}

impl Recorded {
    fn into_facts(mut self, n: usize) -> ShapeFacts {
        let mut elems: Vec<crate::ast::StaticType> =
            (0..n).map(crate::ast::StaticType::Unknown).collect();

        let site_ids: Vec<usize> = self.lattice.sites.values().copied().collect();
        for id in site_ids {
            if self.lattice.needed[id] && self.lattice.site_elem[id] == Pending {
                if self.fn_body_sites.contains(&id) || self.fn_param_sites.contains(&id) {
                    signal!(self.recording, trace::TRACE_ANALYZE_PENDING);
                    elems[id] = crate::ast::StaticType::Unknown(id);
                    continue;
                }
                if self.reads.boundary_fed.contains(&id) {
                    signal!(self.recording, trace::TRACE_ANALYZE_PENDING);
                    elems[id] = crate::ast::StaticType::Unknown(id);
                    continue;
                }
                signal!(self.recording, trace::TRACE_ANALYZE_MISSING_VALUE);
                let line = self.ctor_lines[id];
                self.ledger.diagnostics.push(format!(
                    "line {line}: Type Error: a table is read before it is ever given a value \
                     (table site #{id})"
                ));
                elems[id] = crate::ast::StaticType::Unknown(id);
            } else if self.lattice.site_elem[id] == Pending {
                signal!(self.recording, trace::TRACE_ANALYZE_PENDING);
                elems[id] = crate::ast::StaticType::Unknown(id);
            } else {
                signal!(self.recording, trace::TRACE_ANALYZE_RESOLVED);
                elems[id] = self.elem_type_of_tbl(id);
            }
        }

        for (&site, name) in &self.reads.nested_store_bases {
            if !self.reads.tbl_value_stores.contains(&site) {
                signal!(self.recording, trace::TRACE_STMT_IDX_NULL_ROW);
                let line = self.ctor_lines[site];
                self.ledger.diagnostics.push(format!(
                    "line {line}: Type Error: cannot index a row of '{name}' — no table is ever \
                     stored into '{name}', and stores do not create rows (table site #{site})"
                ));
            }
        }

        for (base, (value, line)) in &self.holds.cyclic_stores {
            signal!(self.recording, trace::TRACE_FAIL_CYCLIC_STORE);
            self.ledger.diagnostics.push(format!(
                "line {line}: Type Error: cyclic table store — '{value}' stored into '{base}' \
                 would create a table cycle (glm's element types are finite)"
            ));
        }

        for id in 0..n {
            propagate_elem_down(&mut elems, &self.lattice.child_sites, id);
        }

        let mut cell_children = self.lattice.child_sites.clone();
        for (parent, kids) in std::mem::take(&mut self.reads.row_links) {
            cell_children.entry(parent).or_default().extend(kids);
        }

        ShapeFacts {
            sites: self.lattice.sites,
            elems,
            boundary_elem: None,
            layouts: self.layout.verdicts,
            free_sites: self.own.free_sites,
            free_keeps: self.own.free_keeps,
            do_exit_frees: self.own.do_exit_frees,
            root_exit_frees: self.own.root_exit_frees,
            stmt_temp_frees: self.own.stmt_temp_frees,
            cond_temp_frees: self.own.cond_temp_frees,
            arm_temp_frees: self.own.arm_temp_frees,
            ret_path_frees: self.own.ret_path_frees,
            ret_path_keep_frees: self.own.ret_path_keep_frees,
            ret_path_keep_temps: self.own.ret_path_keep_temps,
            rebind_frees: self.own.rebind_grants,
            move_poisons: self.own.move_poisons,
            name_dense: self.layout.name_dense,
            stored_ctor_parents: self.own.stored_ctor_parents,
            substitutions: BTreeMap::new(),
            local_types: BTreeMap::new(),
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
            fn_defs: BTreeMap::new(),
            call_defs: BTreeMap::new(),
            stmt_lines: self.stmt_lines,
            ctor_lines: self.ctor_lines,
            adopt_lines: self.adopt_lines,
            diagnostics: self.ledger.diagnostics,
        }
    }
}

fn get_base_identifier(expr: &Expr) -> Option<&String> {
    match expr {
        Expr::Identifier(name) => Some(name),
        Expr::Index { obj, .. } => get_base_identifier(obj),
        _ => None,
    }
}
