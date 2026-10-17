//! The checking half of the analyzer's recorded pass. ONE walk is the
//! truth: the recorded pass drives the lattice machinery and this checker
//! per top-level statement, in program order, against the same final elem
//! table (`static_elems`) the assembled facts will carry.
//!
//! The checker owns NO scope stack of its own. A top-level name's type is
//! a PURE VIEW over lattice state — the walk's own binding (its sites'
//! elems, joined, resolved through the constraint store), the walk's scalar
//! node map, the walk's fn binding (the value node the store anchors), the
//! boundary seed. What the checker still holds is exactly its sequential
//! ACCEPTANCE state: `top` (writebacks — rebind adoptions and unifications,
//! the nil-kept entry, scalars whose derivation the walk cannot see, e.g.
//! arithmetic on unresolved operands), per-block `frames` while its
//! recursion is inside a nested body (names the walk's post-statement
//! state has already popped), and the inlined call frames (parameters and
//! locals of a body under check — a checker-only world). The walk runs one
//! statement AHEAD of the checker, so the driver hands the checker two
//! snapshots per statement: the state BEFORE the statement's walk (what
//! queries read) and the state AFTER it (what a fresh declaration compares
//! against to decide whether an entry must be held at all).
//!
//! The substitution algebra lives in the lattice's `UnknownStore`: the
//! nominal unknowns (use-driven scalar pinning, the boundary seed,
//! monomorphic call signatures) are minted by the walk where it can anchor
//! them and constrained through lattice ops (`bind`/`unify` beside
//! `decide`). Everything the checker records for the lowerer lives in its
//! OWN stores, and `analyze` merges them at assembly time — one pass, one
//! fact set.

use super::super::core::{BOUNDARY_ROOT, MOVED_ROOT, TableShape};
use super::super::facts::{FfiVerb, FnDef, KeyLane};
use super::super::{is_ghost, is_root, join_ty};
use super::WalkState;
use super::constraints::UnknownStore;
use crate::ast::{BinOp, CtorKey, Expr, Stmt, UnOp};
use crate::shape::ty::Ty;
use glm_rt::{signal, trace};
use std::collections::{BTreeMap, BTreeSet};

fn snap_of(walk: &WalkState, severed: &BTreeMap<String, BTreeSet<usize>>) -> WalkSnap {
    WalkSnap {
        binds: walk.scopes[0].clone(),
        scalars: walk.scalar_nodes[0].clone(),
        fns: walk.fn_scopes[0].clone(),
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

/// One checker-held scope frame — pushed only where the checker's
/// recursion enters a world the walk's post-statement state cannot see:
/// block bodies (arms, do, while — the walk already merged/popped them)
/// and inlined call bodies (parameters and locals under check).
struct Frame {
    types: BTreeMap<String, Ty>,
    fns: BTreeMap<String, Option<*const Expr>>,
}

/// The walk's top-level state at one moment, cloned by the driver: `pre`
/// (before the statement's walk — what queries read; the walk is one
/// statement ahead, so this is the state the checker's sequential view
/// must resolve against) and `post` (after it — what a fresh declaration
/// is compared against, since every later query reads snapshots that
/// already include the declaration). `severed` carries the move-slot
/// law's sites (names an affine move poisoned at top level): the walk's
/// own binding for such a name is the MOVED marker, so this map is the
/// only walk-side carrier of the surviving type slot.
#[derive(Clone)]
pub(super) struct WalkSnap {
    binds: BTreeMap<String, TableShape>,
    scalars: BTreeMap<String, usize>,
    fns: BTreeMap<String, Option<*const Expr>>,
    severed: BTreeMap<String, BTreeSet<usize>>,
}

/// The analyzer's final state the checker checks against — the same
/// single elem table the assembled facts carry (cloned in, so the driver
/// can interleave `&mut Analyzer` walks between checker statements).
pub(super) struct CheckCtx {
    pub stmt_lines: BTreeMap<*const Stmt, usize>,
    pub adopt_lines: BTreeMap<String, usize>,
    pub sites: BTreeMap<*const Expr, usize>,
    pub elems: Vec<Ty>,
}

/// Everything the checker records for the lowerer, handed to `analyze` at
/// assembly time. The substitutions are NOT here — they live in the
/// lattice's `UnknownStore` and ride out of it at assembly.
pub(super) struct CheckFacts {
    pub local_types: BTreeMap<(*const Stmt, String), Ty>,
    pub fn_defs: BTreeMap<*const Expr, FnDef>,
    pub call_defs: BTreeMap<*const Expr, *const Expr>,
    pub ffi_verbs: BTreeMap<*const Expr, FfiVerb>,
    pub index_key_lanes: BTreeMap<*const Expr, KeyLane>,
    pub access_elems: BTreeMap<*const Expr, Ty>,
    pub boundary_elem: Option<Ty>,
    pub diagnostics: Vec<String>,
}

pub(super) struct Checker {
    /// block and inlined-call frames — the checker's recursion worlds the
    /// walk's post-statement state cannot answer
    frames: Vec<Frame>,
    /// the top-level sequential acceptance delta: exactly the entries the
    /// lattice view cannot reproduce (rebind writebacks, the nil-kept
    /// entry, scalars derived from unresolved operands). Every other
    /// top-level name resolves through the view.
    top: BTreeMap<String, Ty>,
    /// names declared by the current top-level statement (presence for
    /// same-statement redeclaration checks)
    cur_decls: BTreeSet<String>,
    /// the walk state BEFORE the current statement's walk (queries)
    snap: WalkSnap,
    /// the walk state AFTER the current statement's walk (decl compares)
    decl_snap: WalkSnap,
    ctx: CheckCtx,
    return_ctxs: Vec<ReturnCtx>,
    inline_stack: Vec<*const Expr>,
    seed_read: bool,
    len_deferrals: Vec<(Ty, Option<usize>)>,
    cur_stmt: Option<*const Stmt>,
    loop_depth: usize,
    fn_defs: BTreeMap<*const Expr, FnDef>,
    call_defs: BTreeMap<*const Expr, *const Expr>,
    ffi_verbs: BTreeMap<*const Expr, FfiVerb>,
    index_key_lanes: BTreeMap<*const Expr, KeyLane>,
    access_elems: BTreeMap<*const Expr, Ty>,
    local_types: BTreeMap<(*const Stmt, String), Ty>,
    boundary_elem: Option<Ty>,
    diagnostics: Vec<String>,
}

impl Checker {
    pub(super) fn new(ctx: CheckCtx) -> Self {
        Self {
            frames: Vec::new(),
            top: BTreeMap::new(),
            cur_decls: BTreeSet::new(),
            snap: WalkSnap {
                binds: BTreeMap::new(),
                scalars: BTreeMap::new(),
                fns: BTreeMap::new(),
                severed: BTreeMap::new(),
            },
            decl_snap: WalkSnap {
                binds: BTreeMap::new(),
                scalars: BTreeMap::new(),
                fns: BTreeMap::new(),
                severed: BTreeMap::new(),
            },
            ctx,
            return_ctxs: vec![ReturnCtx::Boundary],
            inline_stack: Vec::new(),
            seed_read: false,
            len_deferrals: Vec::new(),
            cur_stmt: None,
            loop_depth: 0,
            fn_defs: BTreeMap::new(),
            call_defs: BTreeMap::new(),
            ffi_verbs: BTreeMap::new(),
            index_key_lanes: BTreeMap::new(),
            access_elems: BTreeMap::new(),
            local_types: BTreeMap::new(),
            boundary_elem: None,
            diagnostics: Vec::new(),
        }
    }

    /// The walk's top-level state, cloned by the driver around each
    /// statement's walk: `pre` before it (what queries read — the walk is
    /// one statement ahead) and `post` after it (what fresh declarations
    /// compare against). `severed` is the move-slot law's site map.
    pub(super) fn snapshot_pre(
        &mut self,
        walk: &WalkState,
        severed: &BTreeMap<String, BTreeSet<usize>>,
    ) {
        self.snap = snap_of(walk, severed);
    }
    pub(super) fn snapshot_post(
        &mut self,
        walk: &WalkState,
        severed: &BTreeMap<String, BTreeSet<usize>>,
    ) {
        self.decl_snap = snap_of(walk, severed);
    }

    /// The checker's view of a constructor's element type: the analyzer's
    /// one elem table (`static_elems`), resolved through the constraint
    /// pins the lattice's unknown store carries.
    fn elem_of(&self, lat: &mut UnknownStore, ctor: &Expr) -> Ty {
        let id = self.ctx.sites[&(ctor as *const Expr)];
        lat.resolve(&self.ctx.elems[id].clone())
    }

    fn declare_fn_binding(&mut self, name: &str, ptr: Option<*const Expr>) {
        // top level: the walk maintains the identical binding — the view
        // reads it; only checker frames (blocks, inlined bodies) carry
        // their own
        if let Some(frame) = self.frames.last_mut() {
            frame.fns.insert(name.to_string(), ptr);
        }
    }

    fn assign_fn_binding(&mut self, name: &str, ptr: Option<*const Expr>) {
        let Some(depth) = self.frames.iter().rposition(|f| f.fns.contains_key(name)) else {
            return; // top level: the walk's own fn binding is the truth
        };
        self.frames[depth].fns.insert(name.to_string(), ptr);
    }

    fn bind_function(&mut self, lat: &mut UnknownStore, name: &str, expr: &Expr) -> Ty {
        let Expr::Function { params, body } = expr else {
            unreachable!("bind_function on a non-function");
        };
        // both nodes are lattice anchors now: the return node by the walk
        // (`walk_fn_def`), the binding's own value by the definition —
        // the name→type view derives a fn binding's type from it without
        // the checker holding an entry
        let ret = Ty::Unknown(lat.ensure_fn_ret(expr as *const Expr));
        self.fn_defs.insert(
            expr as *const Expr,
            FnDef {
                params: params.clone(),
                body: body.as_slice(),
                ret: ret.clone(),
                signature: None,
            },
        );
        self.declare_fn_binding(name, Some(expr as *const Expr));
        Ty::Unknown(lat.ensure_fn_value(expr as *const Expr))
    }

    fn push_return_ctx(&mut self, expected: Ty) {
        self.return_ctxs.push(ReturnCtx::Internal(expected));
    }

    /// The checker's closing moves, in the order the standalone pass ran
    /// them: pin the boundary elem, resolve every recorded store through
    /// the final constraints, replay the deferred '#' checks.
    pub(super) fn finish(&mut self, lat: &mut UnknownStore) {
        self.finalize_boundary_elem(lat);
        self.resolve_recorded_facts(lat);
        self.replay_len_deferrals(lat);
    }

    /// Hands the recorded stores to `analyze` for the assembled facts.
    pub(super) fn into_facts(self) -> CheckFacts {
        let Self {
            local_types,
            fn_defs,
            call_defs,
            ffi_verbs,
            index_key_lanes,
            access_elems,
            boundary_elem,
            diagnostics,
            ..
        } = self;
        CheckFacts {
            local_types,
            fn_defs,
            call_defs,
            ffi_verbs,
            index_key_lanes,
            access_elems,
            boundary_elem,
            diagnostics,
        }
    }

    fn replay_len_deferrals(&mut self, lat: &mut UnknownStore) {
        for (ty, line) in std::mem::take(&mut self.len_deferrals) {
            match lat.resolve(&ty) {
                Ty::Tbl(_) | Ty::Str | Ty::Unknown(_) => {}
                Ty::Any => {
                    signal!(trace::TRACE_CHK_ANY_LEN);
                }
                other => {
                    let msg = format!(
                        "Type Error: '#' requires a Table, String, or Any operand, got {}",
                        type_name(&other)
                    );
                    self.diagnostics.push(match line {
                        Some(l) => format!("line {l}: {msg}"),
                        None => msg,
                    });
                }
            }
        }
    }

    fn finalize_boundary_elem(&mut self, lat: &mut UnknownStore) {
        let id = lat.boundary_seed();
        let elem = match lat.resolve(&Ty::Unknown(id)) {
            Ty::Unknown(head) => {
                if !self.seed_read {
                    return;
                }
                signal!(trace::TRACE_BOUNDARY_ELEM_ANY);
                lat.bind(head, Ty::Any).ok();
                self.boundary_elem = Some(Ty::Any);
                self.resolve_fn_defs_through_subs(lat);
                return;
            }
            Ty::Tbl(_) => {
                self.diagnostics.push(
                    "Type Error: the boundary 'arg' table's cells hold scalars — \
                     a table element cannot be inferred from 'arg[i]' usage"
                        .to_string(),
                );
                return;
            }
            Ty::Any => {
                signal!(trace::TRACE_BOUNDARY_ELEM_ANY);
                self.boundary_elem = Some(Ty::Any);
                self.resolve_fn_defs_through_subs(lat);
                return;
            }
            concrete => concrete,
        };
        signal!(trace::TRACE_BOUNDARY_ELEM_PINNED);
        self.boundary_elem = Some(elem);
        self.resolve_fn_defs_through_subs(lat);
    }

    fn resolve_fn_defs_through_subs(&mut self, lat: &mut UnknownStore) {
        for def in self.fn_defs.values_mut() {
            def.ret = lat.resolve(&def.ret);
            if let Some(sig) = &mut def.signature {
                for ty in sig.iter_mut() {
                    *ty = lat.resolve(ty);
                }
            }
        }
    }

    /// The closing resolution pass: the checker holds no scope entries,
    /// so what remains is resolving the recorded facts through
    /// the final constraints — every bare declaration's local type (the
    /// identity nodes are the lattice's, anchored by the walk's LocalDecl
    /// arm) and every access-elem face (constraints bound later — the
    /// boundary elem's seed-read pin, inlined-body unifications — must
    /// flow into them; the lowerer consumes the FINAL truth, not the
    /// mid-check snapshot).
    fn resolve_recorded_facts(&mut self, lat: &mut UnknownStore) {
        for ((stmt, name), id) in lat.bare_nodes() {
            let resolved = lat.resolve(&Ty::Unknown(*id));
            self.local_types.insert((*stmt, name.clone()), resolved);
        }
        let resolved: Vec<(*const Expr, Ty)> = self
            .access_elems
            .iter()
            .map(|(&k, v)| (k, lat.resolve(v)))
            .collect();
        for (k, v) in resolved {
            self.access_elems.insert(k, v);
        }
    }

    fn begin_scope(&mut self) {
        self.frames.push(Frame {
            types: BTreeMap::new(),
            fns: BTreeMap::new(),
        });
    }
    fn end_scope(&mut self) {
        self.frames.pop();
    }

    /// Declares `name` at the checker's current depth. Inside a frame
    /// (block or inlined body) the entry is held in full — a checker
    /// world the walk's state cannot answer. At the top level the entry
    /// is held ONLY when the lattice view cannot reproduce it (e.g. a
    /// scalar derived from unresolved operands, whose walk binding stays
    /// Pending); everything else resolves through the view.
    fn declare_var(&mut self, lat: &UnknownStore, name: String, ty: Ty) -> Result<(), String> {
        if let Some(frame) = self.frames.last_mut() {
            if frame.types.contains_key(&name) {
                return Err(format!(
                    "Scope Error: variable '{}' already declared in this scope",
                    name
                ));
            }
            frame.types.insert(name, ty);
            return Ok(());
        }
        // presence: the walk's pre-statement binding set (the boundary
        // `arg` rides it) plus this statement's own declarations
        let boundary_seed = name == "arg";
        if !boundary_seed
            && (self.snap.binds.contains_key(&name)
                || self.top.contains_key(&name)
                || self.cur_decls.contains(&name))
        {
            return Err(format!(
                "Scope Error: variable '{}' already declared in this scope",
                name
            ));
        }
        self.cur_decls.insert(name.clone());
        let (view, _) = self.view_type(lat, &name, &self.decl_snap);
        if view != Some(ty.clone()) {
            self.top.insert(name, ty);
        }
        Ok(())
    }

    /// The name→type query. Frames (innermost out) shadow; the top-level
    /// sequential delta shadows the view; everything else is the pure
    /// view over the walk's pre-statement state.
    fn var_type(&mut self, lat: &mut UnknownStore, name: &str) -> Result<Ty, String> {
        for frame in self.frames.iter().rev() {
            if let Some(ty) = frame.types.get(name) {
                return Ok(lat.resolve(ty));
            }
        }
        if let Some(ty) = self.top.get(name) {
            return Ok(lat.resolve(ty));
        }
        let (view, seed_read) = self.view_type(lat, name, &self.snap);
        if seed_read {
            self.seed_read = true;
        }
        view.ok_or_else(|| format!("Scope Error: reference to undeclared variable '{}'", name))
    }

    /// The pure name→type view over lattice state — computed, not held.
    /// Sources, in shadow order: the fn binding (the value rides the
    /// store's per-definition anchor; frame maps shadow the walk's
    /// top-level map at holding depth), the walk's scalar-node map
    /// (bare slots, boundary cells, scalar/elem aliases of shared
    /// unknowns — the node is the VALUE when the binding is
    /// scalar-shaped, the ELEM when the binding is a table), and the
    /// walk's binding itself (the boundary seed for `arg`; a table's
    /// elem is the static-elem view joined over its real sites, with
    /// the walk's live elem as the fallback a ghost-only binding (a
    /// row read) carries). Returns the type and whether this read
    /// witnessed the seed.
    fn view_type(&self, lat: &UnknownStore, name: &str, snap: &WalkSnap) -> (Option<Ty>, bool) {
        let fn_binding = self
            .frames
            .iter()
            .rev()
            .find_map(|f| f.fns.get(name).copied())
            .or_else(|| snap.fns.get(name).copied());
        if let Some(Some(ptr)) = fn_binding
            && let Some(id) = lat.fn_value_node(ptr)
        {
            return (Some(lat.resolve(&Ty::Unknown(id))), false);
        }
        let Some(bind) = snap.binds.get(name) else {
            return (None, false);
        };
        if name == "arg" && bind.aliases.contains(&BOUNDARY_ROOT) {
            let id = lat.boundary_seed();
            let resolved = lat.resolve(&Ty::Unknown(id));
            // the seed-read witness: the seed still rides an unknown
            // (a pinned seed already decided the elem's kind)
            let seed_read = matches!(resolved, Ty::Unknown(_));
            return (Some(Ty::Tbl(Box::new(resolved))), seed_read);
        }
        // the move-slot law: an affine move left the MOVED marker, but
        // the name's type slot survives it — the severed sites' elems
        // (the same static-elem join every other table view answers
        // with) are the pre-move type. Reads through the moved name
        // reject elsewhere (the nil/moved poison laws); this view feeds
        // `t = nil` acceptance and rebind adoption against the history.
        if bind.aliases.contains(&MOVED_ROOT)
            && let Some(sites) = snap.severed.get(name)
            && !sites.is_empty()
        {
            let mut elem = Ty::Pending;
            for &s in sites {
                if !is_root(&s) && !is_ghost(&s) {
                    let site_view = lat.resolve(&self.ctx.elems[s]);
                    elem = join_ty(&elem, &site_view);
                }
            }
            return (Some(Ty::Tbl(Box::new(elem))), false);
        }
        if let Some(&id) = snap.scalars.get(name) {
            return (
                Some(match &bind.ty {
                    Ty::Tbl(_) => Ty::Tbl(Box::new(lat.resolve(&Ty::Unknown(id)))),
                    _ => lat.resolve(&Ty::Unknown(id)),
                }),
                false,
            );
        }
        match &bind.ty {
            Ty::Tbl(live_elem) => {
                let mut elem = Ty::Pending;
                for &s in bind.aliases.iter() {
                    if !is_root(&s) && !is_ghost(&s) {
                        let site_view = lat.resolve(&self.ctx.elems[s]);
                        elem = join_ty(&elem, &site_view);
                    }
                }
                if matches!(elem, Ty::Pending) {
                    elem = live_elem.as_ref().clone();
                }
                (Some(Ty::Tbl(Box::new(elem))), false)
            }
            other => (Some(other.clone()), false),
        }
    }

    /// Writes a rebind's resolved type at the depth that holds the name:
    /// a frame entry, or (top level) the sequential delta.
    fn write_back(&mut self, name: &str, ty: Ty) {
        if let Some(frame) = self
            .frames
            .iter_mut()
            .rev()
            .find(|f| f.types.contains_key(name))
        {
            frame.types.insert(name.to_string(), ty);
        } else {
            self.top.insert(name.to_string(), ty);
        }
    }

    /// The nil law keeps the released name's type slot: inside a frame
    /// the entry simply stays; at top level the pre-nil view is held in
    /// the delta so later rebinds adopt against the surviving history.
    fn hold_entry(&mut self, name: &str, ty: Ty) {
        if let Some(frame) = self
            .frames
            .iter_mut()
            .rev()
            .find(|f| f.types.contains_key(name))
        {
            frame.types.insert(name.to_string(), ty);
        } else if !self.top.contains_key(name) {
            self.top.insert(name.to_string(), ty);
        }
    }

    pub(super) fn check_stmt(&mut self, lat: &mut UnknownStore, stmt: &Stmt) -> Result<(), String> {
        self.cur_stmt = Some(stmt as *const Stmt);
        // the presence window for top-level declarations (frames cover
        // every nested call)
        if self.frames.is_empty() {
            self.cur_decls.clear();
        }
        match stmt {
            Stmt::LocalDecl { names, exprs } => {
                let mut expr_types = Vec::with_capacity(exprs.len());
                for (name, expr) in names.iter().zip(exprs.iter()) {
                    if let Expr::Function { .. } = expr {
                        expr_types.push(self.bind_function(lat, name, expr));
                    } else {
                        self.declare_fn_binding(name, None);
                        expr_types.push(self.check_expr(lat, expr)?);
                    }
                }
                for name in &names[exprs.len()..] {
                    self.declare_fn_binding(name, None);
                }
                for (name, ty) in names.iter().zip(expr_types) {
                    self.declare_var(lat, name.clone(), ty)?;
                }
                for name in &names[exprs.len()..] {
                    // the identity node is the lattice's (anchored by the
                    // walk's LocalDecl arm — one node per declaration,
                    // minted during the fixpoint, read here)
                    let id = lat.ensure_bare_node(stmt, name);
                    self.declare_var(lat, name.clone(), Ty::Unknown(id))?;
                }
            }
            Stmt::Assignment { name, expr } => {
                if let Expr::Function { .. } = expr {
                    let ty = self.bind_function(lat, name, expr);
                    if let Some(frame) = self
                        .frames
                        .iter_mut()
                        .rev()
                        .find(|f| f.types.contains_key(name))
                    {
                        // a block-local name: the frame holds both halves
                        frame.types.insert(name.clone(), ty);
                    } else if !self.frames.is_empty() {
                        // a top-level fn name rebound inside a block: the
                        // type write escapes at holding depth (as every
                        // assignment's does) and the walk's fn binding
                        // escapes with it — the fn rebind TAKES, one
                        // discipline for both halves
                        self.top.insert(name.clone(), ty);
                    } else {
                        // top level: the walk's fn binding answers from
                        // here on (the view) — drop any stale hold
                        self.top.remove(name);
                    }
                    return Ok(());
                }
                self.assign_fn_binding(name, None);
                let expected = self.var_type(lat, name)?;
                if matches!(expr, Expr::Nil) {
                    if !matches!(expected, Ty::Tbl(_) | Ty::Unknown(_)) {
                        return Err(format!(
                            "Type Error: 'nil' releases tables — '{}' is of type {}",
                            name,
                            type_name(&expected)
                        ));
                    }
                    // the nil law: the name's type slot survives — hold
                    // the entry so later rebinds adopt against the
                    // surviving history
                    self.hold_entry(name, expected);
                    return Ok(());
                }
                let actual = self.check_expr(lat, expr)?;
                if expected != actual {
                    // every cleanly-joinable elem mix was already adopted
                    // by the lattice (the rebind's site exchange, the
                    // nil/move-severed bridges) before the checker ran —
                    // a mismatch reaching here is a genuine conflict
                    lat.unify(&expected, &actual)?;
                    let resolved = lat.resolve(&actual);
                    self.write_back(name, resolved);
                }
            }
            Stmt::IndexAssign { obj, key, value } => {
                let (elem, _obj_desc) = self.check_index_base(lat, obj)?;
                let _key_ty = self.check_index_key(lat, key)?;

                let val_ty = self.check_expr(lat, value)?;

                if matches!(lat.resolve(&elem), Ty::Any) {
                    match lat.resolve(&val_ty) {
                        Ty::Int | Ty::Flt | Ty::Bool | Ty::Str | Ty::Any | Ty::Unknown(_) => {
                            return Ok(());
                        }
                        Ty::Tbl(_) => {
                            return Err(
                                "Type Error: an Any table's cells hold scalars — a table value \
                                 cannot enter a dynamic cell"
                                    .to_string(),
                            );
                        }
                        Ty::Ffi | Ty::FfiLib | Ty::Coro => {
                            return Err("Type Error: an Any table's cells hold scalars — the ffi \
                                 surface cannot enter a dynamic cell"
                                .to_string());
                        }
                        // flow state never rides a resolved checker type —
                        // the elems table materializes it before this half
                        // ever reads it
                        Ty::Pending | Ty::Conflict => {
                            unreachable!("flow state never rides a resolved checker type")
                        }
                    }
                }

                if matches!(elem, Ty::Tbl(_)) && matches!(val_ty, Ty::Tbl(_)) {
                    let expected_inner = match &elem {
                        Ty::Tbl(inner) => inner.as_ref(),
                        _ => unreachable!(),
                    };
                    let actual_inner = match &val_ty {
                        Ty::Tbl(inner) => inner.as_ref(),
                        _ => unreachable!(),
                    };
                    lat.unify(expected_inner, actual_inner)?;
                } else {
                    lat.unify(&elem, &val_ty)?;
                }
            }
            Stmt::While { condition, body } => {
                self.check_condition(lat, condition, "while")?;
                self.begin_scope();
                self.loop_depth += 1;
                self.check_block(lat, body);
                self.loop_depth -= 1;
                self.end_scope();
            }
            Stmt::Break => {
                if self.loop_depth == 0 {
                    return Err("Type Error: 'break' outside of loop".to_string());
                }
            }
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                self.check_condition(lat, condition, "if")?;
                self.begin_scope();
                self.check_block(lat, then_body);
                self.end_scope();
                self.begin_scope();
                self.check_block(lat, else_body);
                self.end_scope();
            }
            Stmt::Do { body } => {
                self.begin_scope();
                self.check_block(lat, body);
                self.end_scope();
            }
            Stmt::Print { exprs } => {
                for e in exprs {
                    let ty = self.check_expr(lat, e)?;
                    if matches!(ty, Ty::Tbl(_)) {
                        return Err("Type Error: cannot print a table — print its cells instead"
                            .to_string());
                    }
                }
            }
            Stmt::Expr { expr } => {
                if !self.check_ffi_verb(lat, expr)? {
                    let _ = self.check_expr(lat, expr)?;
                }
            }
            Stmt::Return { value } => match self.return_ctxs.last().cloned() {
                Some(ReturnCtx::Boundary) => match value {
                    None | Some(Expr::Nil) => {}
                    Some(expr) => match self.check_expr(lat, expr)? {
                        Ty::Tbl(_) => {}
                        other => {
                            return Err(format!(
                                "Type Error: 'return' hands a value to the host — \
                                     return a table (or nil for null), got {}",
                                type_name(&other)
                            ));
                        }
                    },
                },
                Some(ReturnCtx::Internal(expected)) => {
                    let expr = match value {
                        Some(expr) if !matches!(expr, Expr::Nil) => expr,
                        _ => {
                            return Err("Type Error: an internal 'return' carries a value — \
                                     the bare and nil forms belong to the script's host \
                                     boundary"
                                .to_string());
                        }
                    };
                    let actual = self.check_expr(lat, expr)?;
                    lat.unify(&expected, &actual)?;
                    let resolved = lat.resolve(&actual);
                    if let Some(ReturnCtx::Internal(ty)) = self.return_ctxs.last_mut() {
                        *ty = resolved;
                    }
                }
                None => unreachable!("new pushes the root return context"),
            },
        }
        Ok(())
    }

    fn check_index_base(
        &mut self,
        lat: &mut UnknownStore,
        obj: &Expr,
    ) -> Result<(Ty, String), String> {
        let ty = self.check_expr(lat, obj)?;
        match ty {
            Ty::Tbl(elem) => {
                let desc = type_name(&Ty::Tbl(elem.clone()));
                // the elem face fact: this one resolved view is what every
                // lowering of this access consumes — the lowerer's own
                // type-walk re-derivation was the elem seam (two views of
                // one cell kind disagreeing on adoption-bridged names)
                signal!(trace::TRACE_CHK_ELEM_FACE);
                self.access_elems
                    .insert(obj as *const Expr, (*elem).clone());
                Ok((*elem, desc))
            }
            _ => Err(format!(
                "Type Error: cannot index {} — only tables support '[]'",
                type_name(&ty)
            )),
        }
    }

    /// Validates the key in index position and returns its resolved type
    /// (Integer or String — a bare Unknown key is pinned to Integer here).
    /// NOTE: a statically-negative literal key (`t[-1]`, `{[k - 2] = v}`)
    /// is NOT an error — the negative no-op is pinned language contract
    /// (soundness_edge_gauntlet S6, ctor_expr_keys): the store drops, the
    /// read answers the element zero.
    fn check_index_key(&mut self, lat: &mut UnknownStore, key: &Expr) -> Result<Ty, String> {
        let key_ty = self.check_expr(lat, key)?;
        let key_ty = lat.resolve(&key_ty);
        let key_ty = if let Ty::Unknown(id) = key_ty {
            lat.bind(id, Ty::Int)?;
            Ty::Int
        } else {
            key_ty
        };
        if key_ty != Ty::Int && key_ty != Ty::Str {
            let note = self.any_provenance_note(lat, &key_ty, key);
            return Err(format!(
                "Type Error: table index must be an Integer or a String, got {}{}",
                type_name(&key_ty),
                note.unwrap_or_default()
            ));
        }
        if key_ty == Ty::Str {
            signal!(trace::TRACE_CHK_STRKEY);
        }
        // the lane decision: recorded so the lowerer selects the
        // addressing lane from this fact rather than re-deriving it from
        // its own type walk of the key expression
        signal!(trace::TRACE_CHK_KEY_LANE);
        self.index_key_lanes.insert(
            key as *const Expr,
            if key_ty == Ty::Str {
                KeyLane::Str
            } else {
                KeyLane::Int
            },
        );
        Ok(key_ty)
    }

    /// Records the checker's verdict for one dotted call site — the fact
    /// the lowerer lowers straight from (member, arity, and operand types
    /// were all decided HERE; re-deriving them downstream was the desync
    /// surface this replaces).
    fn record_verb(&mut self, call: &Expr, verb: FfiVerb) {
        signal!(trace::TRACE_CHK_FFI_VERB);
        self.ffi_verbs.insert(call as *const Expr, verb);
    }

    fn check_ffi_call(
        &mut self,
        lat: &mut UnknownStore,
        call: &Expr,
        obj: &Expr,
        name: &str,
        args: &[Expr],
    ) -> Result<Ty, String> {
        let base = match obj {
            Expr::Identifier(n) => n.clone(),
            _ => {
                return Err(
                    "Type Error: the ffi surface's '.' base must be a name — a bound \
                     module or library handle"
                        .to_string(),
                );
            }
        };
        let raw = self.check_expr(lat, obj)?;
        let bt = lat.resolve(&raw);
        match bt {
            Ty::Ffi => match name {
                "load" => {
                    if args.len() != 1 {
                        return Err("Type Error: ffi.load takes exactly one path".to_string());
                    }
                    let t = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&t);
                    let t = if let Ty::Unknown(id) = t {
                        lat.bind(id, Ty::Str)?;
                        Ty::Str
                    } else {
                        t
                    };
                    match t {
                        Ty::Str => {
                            self.record_verb(call, FfiVerb::Load);
                            Ok(Ty::FfiLib)
                        }
                        other => Err(format!(
                            "Type Error: ffi.load's path is a String, got {}",
                            type_name(&other)
                        )),
                    }
                }
                "cdef" => Err(
                    "Type Error: ffi.cdef is a statement verb — call it on its own line; its \
                     nothing cannot bind"
                        .to_string(),
                ),
                "arg_kind" => {
                    if args.len() != 1 {
                        return Err(
                            "Type Error: ffi.arg_kind takes exactly one library".to_string()
                        );
                    }
                    let raw = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&raw);
                    match t {
                        Ty::FfiLib => {
                            self.record_verb(call, FfiVerb::ArgKind);
                            Ok(Ty::Int)
                        }
                        other => Err(format!(
                            "Type Error: ffi.arg_kind takes a library handle, got {}",
                            type_name(&other)
                        )),
                    }
                }
                _ => Err(format!(
                    "Type Error: unknown ffi member '{name}' — load, cdef, arg_kind"
                )),
            },
            Ty::Coro => {
                match name {
                    "create" => {
                        if args.len() != 1 {
                            return Err("Type Error: coroutine.create takes exactly one library"
                                .to_string());
                        }
                        let raw = self.check_expr(lat, &args[0])?;
                        let t = lat.resolve(&raw);
                        match t {
                            Ty::FfiLib => {
                                self.record_verb(call, FfiVerb::CoroCreate);
                                Ok(Ty::Int)
                            }
                            other => Err(format!(
                                "Type Error: coroutine.create takes a library handle, got {}",
                                type_name(&other),
                            )),
                        }
                    }
                    "resume" => {
                        if args.len() != 2 {
                            return Err(
                                "Type Error: coroutine.resume takes a coroutine handle and one \
                             table — the spawn inputs (its first three cells ride the \
                             worker's boundary)"
                                    .to_string(),
                            );
                        }
                        let raw = self.check_expr(lat, &args[0])?;
                        let t = lat.resolve(&raw);
                        let t = if let Ty::Unknown(id) = t {
                            lat.bind(id, Ty::Int)?;
                            Ty::Int
                        } else {
                            t
                        };
                        match t {
                            Ty::Int => {}
                            other => {
                                return Err(format!(
                                    "Type Error: coroutine.resume's first argument is a \
                                 coroutine handle, got {}",
                                    type_name(&other)
                                ));
                            }
                        }
                        let raw = self.check_expr(lat, &args[1])?;
                        let t = lat.resolve(&raw);
                        match t {
                            Ty::Tbl(_) => {
                                self.record_verb(call, FfiVerb::CoroResume);
                                Ok(Ty::Int)
                            }
                            other => Err(format!(
                                "Type Error: coroutine.resume's second argument is the input \
                                 table, got {}",
                                type_name(&other),
                            )),
                        }
                    }
                    "yield" => {
                        if args.len() != 1 {
                            return Err(
                                "Type Error: coroutine.yield takes exactly one integer".to_string()
                            );
                        }
                        let raw = self.check_expr(lat, &args[0])?;
                        let t = lat.resolve(&raw);
                        let t = if let Ty::Unknown(id) = t {
                            lat.bind(id, Ty::Int)?;
                            Ty::Int
                        } else {
                            t
                        };
                        match t {
                            Ty::Int => {
                                self.record_verb(call, FfiVerb::CoroYield);
                                Ok(Ty::Int)
                            }
                            other => Err(format!(
                                "Type Error: coroutine.yield streams one integer, got {}",
                                type_name(&other),
                            )),
                        }
                    }
                    "status" => {
                        if args.len() != 1 {
                            return Err("Type Error: coroutine.status takes exactly one coroutine"
                                .to_string());
                        }
                        let raw = self.check_expr(lat, &args[0])?;
                        let t = lat.resolve(&raw);
                        let t = if let Ty::Unknown(id) = t {
                            lat.bind(id, Ty::Int)?;
                            Ty::Int
                        } else {
                            t
                        };
                        match t {
                            Ty::Int => {
                                self.record_verb(call, FfiVerb::CoroStatus);
                                Ok(Ty::Str)
                            }
                            other => Err(format!(
                                "Type Error: coroutine.status takes a coroutine handle, got {}",
                                type_name(&other),
                            )),
                        }
                    }
                    "close" => {
                        if args.len() != 1 {
                            return Err("Type Error: coroutine.close takes exactly one coroutine"
                                .to_string());
                        }
                        let raw = self.check_expr(lat, &args[0])?;
                        let t = lat.resolve(&raw);
                        let t = if let Ty::Unknown(id) = t {
                            lat.bind(id, Ty::Int)?;
                            Ty::Int
                        } else {
                            t
                        };
                        match t {
                            Ty::Int => {
                                self.record_verb(call, FfiVerb::CoroClose);
                                Ok(Ty::Int)
                            }
                            other => Err(format!(
                                "Type Error: coroutine.close takes a coroutine handle, got {}",
                                type_name(&other),
                            )),
                        }
                    }
                    _ => Err(format!(
                        "Type Error: unknown coroutine member '{name}' — create, resume, yield, \
                     status, close"
                    )),
                }
            }
            Ty::FfiLib => Err(format!(
                "Type Error: {base}.{name} is the drive verb — a statement on its own line; \
                 the module's result stays in the module's world, nothing comes back to bind"
            )),
            _ => Err(format!(
                "Type Error: '{base}' is not a module surface — '.' is the ffi/coroutine \
                 surface's, tables use '[]'"
            )),
        }
    }

    fn check_ffi_verb(&mut self, lat: &mut UnknownStore, expr: &Expr) -> Result<bool, String> {
        let Expr::Call { callee, args } = expr else {
            return Ok(false);
        };
        let Expr::Field { obj, name } = callee.as_ref() else {
            return Ok(false);
        };
        let Expr::Identifier(base) = obj.as_ref() else {
            return Ok(false);
        };
        let raw = self.check_expr(lat, obj)?;
        let bt = lat.resolve(&raw);
        match (&bt, name.as_str()) {
            (Ty::Ffi, "cdef") => {
                if args.len() != 1 {
                    return Err(
                        "Type Error: ffi.cdef takes exactly one declaration string".to_string()
                    );
                }
                let raw = self.check_expr(lat, &args[0])?;
                let t = lat.resolve(&raw);
                match t {
                    Ty::Str => {
                        self.record_verb(expr, FfiVerb::Cdef);
                        Ok(true)
                    }
                    other => Err(format!(
                        "Type Error: ffi.cdef's declaration is a String, got {}",
                        type_name(&other)
                    )),
                }
            }
            (Ty::FfiLib, _) => {
                if args.len() != 1 {
                    return Err(format!(
                        "Type Error: the drive call .{name} takes exactly one table — the \
                         boundary the module reads"
                    ));
                }
                let raw = self.check_expr(lat, &args[0])?;
                let t = lat.resolve(&raw);
                match t {
                    Ty::Tbl(_) => {
                        self.record_verb(
                            expr,
                            FfiVerb::Drive {
                                base: base.clone(),
                                sym: name.clone(),
                            },
                        );
                        Ok(true)
                    }
                    other => Err(format!(
                        "Type Error: the drive call .{name} takes one table, got {}",
                        type_name(&other)
                    )),
                }
            }
            _ => Ok(false),
        }
    }

    fn check_condition(
        &mut self,
        lat: &mut UnknownStore,
        condition: &Expr,
        kw: &str,
    ) -> Result<(), String> {
        let ty = self.check_expr(lat, condition)?;
        let ty = self.pin_bool(lat, &ty)?;
        if ty != Ty::Bool {
            let note = self.any_provenance_note(lat, &ty, condition);
            return Err(format!(
                "Type Error: '{}' condition must be a Boolean, got {}{}",
                kw,
                type_name(&ty),
                note.unwrap_or_default()
            ));
        }
        Ok(())
    }

    fn check_expr(&mut self, lat: &mut UnknownStore, expr: &Expr) -> Result<Ty, String> {
        match expr {
            Expr::Integer(_) => Ok(Ty::Int),
            Expr::Float(_) => Ok(Ty::Flt),
            Expr::Boolean(_) => Ok(Ty::Bool),
            Expr::String(_) => Ok(Ty::Str),
            Expr::Nil => {
                signal!(trace::TRACE_CHK_NIL_EXPR);
                Err(
                    "Type Error: 'nil' is only valid as the right-hand side of 't = nil' — \
                     it releases a table's memory, it is not a value"
                        .to_string(),
                )
            }
            Expr::TableCtor(entries) => {
                let elem = self.elem_of(lat, expr);
                // The parser rejects what it can see statically (named keys
                // and literal-string expr keys vs positional slots, either
                // order); the checker is the full discipline's home: every
                // entry is an ARRAY cell (an integer key — positional or
                // dynamic) or a RECORD cell (a string key — named or
                // dynamic), and a constructor never mixes the two.
                let mut has_int_key = false;
                let mut has_str_key = false;
                for (key, e) in entries {
                    match key {
                        CtorKey::Const(_) => has_int_key = true,
                        CtorKey::Str(_) => has_str_key = true,
                        CtorKey::Expr(ke) => {
                            if self.check_index_key(lat, ke)? == Ty::Str {
                                has_str_key = true;
                            } else {
                                has_int_key = true;
                            }
                        }
                    }
                    if has_int_key && has_str_key {
                        return Err(
                            "Type Error: mixed array and record constructor elements — a \
                             constructor is an array or a record, never both"
                                .to_string(),
                        );
                    }
                    let ty = self.check_expr(lat, e)?;
                    if matches!(elem, Ty::Tbl(_)) && matches!(ty, Ty::Tbl(_)) {
                        let expected_inner = match &elem {
                            Ty::Tbl(inner) => inner.as_ref(),
                            _ => unreachable!(),
                        };
                        let actual_inner = match &ty {
                            Ty::Tbl(inner) => inner.as_ref(),
                            _ => unreachable!(),
                        };
                        if expected_inner != actual_inner {
                            lat.unify(expected_inner, actual_inner)?;
                        }
                    } else if ty != elem {
                        if matches!(elem, Ty::Any) {
                            if matches!(ty, Ty::Tbl(_)) {
                                return Err(format!(
                                    "Type Error: an Any table's cells hold scalars — a table \
                                     value cannot enter a dynamic cell ({} after Any)",
                                    type_name(&ty)
                                ));
                            }
                            if matches!(ty, Ty::Unknown(_)) {
                                lat.unify(&elem, &ty)?;
                            }
                            continue;
                        }
                        lat.unify(&elem, &ty)?;
                        let resolved = lat.resolve(&ty);
                        if resolved != lat.resolve(&elem) {
                            return Err(format!(
                                "Type Error: mixed table constructor elements — {} after {}",
                                type_name(&ty),
                                type_name(&elem)
                            ));
                        }
                    }
                }
                Ok(Ty::Tbl(Box::new(elem)))
            }
            Expr::Index { obj, key } => {
                let (elem, _) = self.check_index_base(lat, obj)?;
                let _key_ty = self.check_index_key(lat, key)?;
                Ok(elem)
            }
            Expr::Identifier(name) => self.var_type(lat, name),
            Expr::BinaryOp { op, left, right } => {
                let l = self.check_expr(lat, left)?;
                let r = self.check_expr(lat, right)?;
                match op {
                    BinOp::And | BinOp::Or => {
                        let l = self.pin_bool(lat, &l)?;
                        let r = self.pin_bool(lat, &r)?;
                        if l == Ty::Bool && r == Ty::Bool {
                            Ok(Ty::Bool)
                        } else {
                            Err(format!(
                                "Type Error: '{}' requires Boolean operands on both sides",
                                match op {
                                    BinOp::And => "and",
                                    _ => "or",
                                }
                            ))
                        }
                    }
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::IntDiv | BinOp::Mod => {
                        self.numeric_operand(lat, &l, &r, op, left, right)
                    }
                    BinOp::Div => {
                        self.infer_numeric_pair(lat, &l, &r)?;
                        let l = lat.resolve(&l);
                        let r = lat.resolve(&r);
                        if !matches!((&l, &r), (Ty::Int | Ty::Flt, Ty::Int | Ty::Flt,)) {
                            let note = self
                                .any_provenance_note(lat, &l, left)
                                .or_else(|| self.any_provenance_note(lat, &r, right));
                            return Err(format!(
                                "Type Error: '/' requires numeric operands{}",
                                note.unwrap_or_default()
                            ));
                        }
                        Ok(Ty::Flt)
                    }
                    BinOp::LessThan | BinOp::GreaterThan | BinOp::LessEq | BinOp::GreaterEq => {
                        self.numeric_operand(lat, &l, &r, op, left, right)?;
                        Ok(Ty::Bool)
                    }
                    BinOp::Equal | BinOp::NotEqual => {
                        self.pin_scalar_pair(lat, &l, &r)?;
                        let l = lat.resolve(&l);
                        let r = lat.resolve(&r);
                        if l == Ty::Str && r == Ty::Str {
                            signal!(trace::TRACE_CHK_STR_EQ);
                            return Ok(Ty::Bool);
                        }
                        if l == Ty::Str || r == Ty::Str {
                            return Err(format!(
                                "Type Error: '{}' compares String with {}",
                                match op {
                                    BinOp::Equal => "==",
                                    _ => "~=",
                                },
                                type_name(if l == Ty::Str { &r } else { &l })
                            ));
                        }
                        let l_unk = matches!(l, Ty::Unknown(_));
                        let r_unk = matches!(r, Ty::Unknown(_));
                        if (l_unk && matches!(r, Ty::Tbl(_)) || r_unk && matches!(l, Ty::Tbl(_)))
                            && (self.is_boundary_chained(lat, &l)
                                || self.is_boundary_chained(lat, &r))
                        {
                            return Err(
                                "Type Error: '==' compares a boundary cell with a table — \
                                 boundary cells hold scalars"
                                    .to_string(),
                            );
                        }
                        if !types_compatible(&l, &r) {
                            return Err(format!(
                                "Type Error: '{}' compares {} with {}",
                                match op {
                                    BinOp::Equal => "==",
                                    _ => "~=",
                                },
                                type_name(&l),
                                type_name(&r)
                            ));
                        }
                        Ok(Ty::Bool)
                    }
                }
            }
            Expr::UnaryOp { op, expr } => {
                let t = self.check_expr(lat, expr)?;
                match op {
                    UnOp::Neg => {
                        let t = lat.resolve(&t);
                        let t = if let Ty::Unknown(id) = t {
                            lat.bind(id, Ty::Int)?;
                            Ty::Int
                        } else {
                            t
                        };
                        match t {
                            Ty::Int | Ty::Flt => Ok(t),
                            _ => {
                                Err("Type Error: unary '-' requires a numeric operand".to_string())
                            }
                        }
                    }
                    UnOp::Not => {
                        let t = self.pin_bool(lat, &t)?;
                        match t {
                            Ty::Bool => Ok(Ty::Bool),
                            _ => Err("Type Error: 'not' requires a Boolean operand".to_string()),
                        }
                    }
                    UnOp::Len => match lat.resolve(&t) {
                        Ty::Tbl(_) | Ty::Str => Ok(Ty::Int),
                        Ty::Any => {
                            signal!(trace::TRACE_CHK_ANY_LEN);
                            Ok(Ty::Int)
                        }
                        unknown @ Ty::Unknown(_) => {
                            let line = self
                                .cur_stmt
                                .and_then(|s| self.ctx.stmt_lines.get(&s).copied());
                            self.len_deferrals.push((unknown, line));
                            Ok(Ty::Int)
                        }
                        _ => Err(format!(
                            "Type Error: '#' requires a Table, String, or Any operand, got {}",
                            type_name(&t)
                        )),
                    },
                }
            }
            Expr::SysAllocCount | Expr::SysExecCount => Ok(Ty::Int),
            Expr::FfiModule => Ok(Ty::Ffi),
            Expr::CoroModule => Ok(Ty::Coro),
            Expr::Field { obj, .. } => {
                // non-callee dot access is a record read; the ffi verbs
                // dispatch in the Call arm before check_expr sees them
                let ty = self.check_expr(lat, obj)?;
                let ty = lat.resolve(&ty);
                match ty {
                    Ty::Tbl(elem) => {
                        // the dispatch: a Table receiver desugars the dot
                        // to a string-keyed index (negative interned key)
                        signal!(trace::TRACE_PARSE_STRKEY_DOT);
                        // a record read answers the table's elem — the
                        // same elem face fact the bracket accesses record
                        signal!(trace::TRACE_CHK_ELEM_FACE);
                        self.access_elems
                            .insert(obj.as_ref() as *const Expr, (*elem).clone());
                        Ok(*elem)
                    }
                    other => Err(format!(
                        "Type Error: dot access needs a record or the ffi surface, got {}",
                        type_name(&other)
                    )),
                }
            }
            Expr::Function { .. } => Err(
                "Type Error: a function value binds directly to a variable — \
                 'local f = function(a, b) ... end'"
                    .to_string(),
            ),
            Expr::Call { callee, args } => {
                if let Expr::Field { obj, name } = callee.as_ref() {
                    return self.check_ffi_call(lat, expr, obj, name, args);
                }
                let name = match callee.as_ref() {
                    Expr::Identifier(n) => n.clone(),
                    _ => {
                        return Err("Type Error: calls go through a function variable — only \
                             anonymous functions assigned directly to variables are callable"
                            .to_string());
                    }
                };
                // the fn binding: checker frames first (inlined bodies
                // hold their own), then the walk's top-level fn map
                let fn_ptr = self
                    .frames
                    .iter()
                    .rev()
                    .find_map(|f| f.fns.get(&name).copied())
                    .or_else(|| self.snap.fns.get(&name).copied())
                    .flatten()
                    .ok_or_else(|| {
                        format!(
                            "Type Error: '{name}' is not a function — only anonymous \
                             functions assigned directly to variables are callable"
                        )
                    })?;
                if self.inline_stack.contains(&fn_ptr) {
                    return Err(format!(
                        "Type Error: '{name}' is recursive — inline closures expand at \
                         their call sites, so a call chain may not reach back into itself"
                    ));
                }
                let def = self.fn_defs.get(&fn_ptr).cloned().ok_or_else(|| {
                    format!(
                        "Type Error: '{name}' holds no function body — \
                             the checker and the analyzer disagree"
                    )
                })?;
                if args.len() != def.params.len() {
                    return Err(format!(
                        "Type Error: '{name}' takes {} argument(s), got {}",
                        def.params.len(),
                        args.len()
                    ));
                }
                let mut arg_tys = Vec::with_capacity(args.len());
                for a in args {
                    arg_tys.push(self.check_expr(lat, a)?);
                }

                match &def.signature {
                    None => {
                        if let Some(d) = self.fn_defs.get_mut(&fn_ptr) {
                            d.signature = Some(arg_tys.clone());
                        }
                    }
                    Some(fixed) => {
                        for (i, (f, a)) in fixed.iter().zip(arg_tys.iter()).enumerate() {
                            if lat.unify(f, a).is_err() {
                                let want = type_name(&lat.resolve(f));
                                let got = type_name(&lat.resolve(a));
                                return Err(format!(
                                    "Type Error: argument {} of '{name}' is {got} where \
                                     the first call fixed {want} — calls are monomorphic",
                                    i + 1
                                ));
                            }
                        }
                    }
                }

                let body = unsafe { def.body() };

                self.inline_stack.push(fn_ptr);
                self.begin_scope();
                for (p, aty) in def.params.iter().zip(arg_tys) {
                    let pty = lat.fresh();
                    self.declare_var(lat, p.clone(), pty.clone())?;
                    lat.unify(&pty, &aty)?;
                }
                self.push_return_ctx(def.ret.clone());
                let saved_loop_depth = std::mem::replace(&mut self.loop_depth, 0);
                self.check_block(lat, body);
                self.loop_depth = saved_loop_depth;
                let ret = match self.return_ctxs.pop() {
                    Some(ReturnCtx::Internal(ty)) => lat.resolve(&ty),
                    _ => unreachable!("push_return_ctx just pushed an Internal context"),
                };
                self.end_scope();
                self.inline_stack.pop();

                if let Some(d) = self.fn_defs.get_mut(&fn_ptr) {
                    d.ret = ret.clone();
                }
                self.call_defs.insert(expr as *const Expr, fn_ptr);
                Ok(ret)
            }
        }
    }

    /// Walks until the first error, records it with its line, keeps going
    /// no further. The driver calls this per top-level statement;
    /// recursion covers the nested bodies.
    pub(super) fn check_block(&mut self, lat: &mut UnknownStore, stmts: &[Stmt]) {
        for stmt in stmts {
            if let Err(msg) = self.check_stmt(lat, stmt) {
                signal!(trace::TRACE_GHOST_BAIL_CHECKER);
                if msg.contains("disagree") {
                    signal!(trace::TRACE_ENG_DESYNC);
                }
                let line = self.ctx.stmt_lines.get(&(stmt as *const Stmt)).copied();
                self.diagnostics.push(match line {
                    Some(l) => format!("line {l}: {msg}"),
                    None => msg,
                });
                return;
            }
        }
    }

    fn numeric_operand(
        &mut self,
        lat: &mut UnknownStore,
        l: &Ty,
        r: &Ty,
        op: &BinOp,
        l_expr: &Expr,
        r_expr: &Expr,
    ) -> Result<Ty, String> {
        let (l, r) = self.infer_numeric_pair(lat, l, r)?;
        match (&l, &r) {
            (Ty::Int, Ty::Int) => Ok(Ty::Int),
            (Ty::Flt, Ty::Flt) => Ok(Ty::Flt),
            (Ty::Int, Ty::Flt) | (Ty::Flt, Ty::Int) => Err(format!(
                "Type Error: '{}' does not support mixed Integer and Float operands",
                bin_op_name(op)
            )),
            _ => {
                let note = self
                    .any_provenance_note(lat, &l, l_expr)
                    .or_else(|| self.any_provenance_note(lat, &r, r_expr));
                Err(format!(
                    "Type Error: '{}' requires numeric operands{}",
                    bin_op_name(op),
                    note.unwrap_or_default()
                ))
            }
        }
    }

    fn is_boundary_chained(&self, lat: &UnknownStore, ty: &Ty) -> bool {
        let seed = lat.boundary_seed();
        matches!(
            (
                lat.resolve(ty),
                lat.resolve(&Ty::Unknown(seed)),
            ),
            (Ty::Unknown(a), Ty::Unknown(b)) if a == b
        )
    }

    fn pin_bool(&mut self, lat: &mut UnknownStore, ty: &Ty) -> Result<Ty, String> {
        let resolved = lat.resolve(ty);
        if let Ty::Unknown(id) = resolved {
            lat.bind(id, Ty::Bool)?;
            return Ok(Ty::Bool);
        }
        Ok(resolved)
    }

    fn infer_numeric_pair(
        &mut self,
        lat: &mut UnknownStore,
        l: &Ty,
        r: &Ty,
    ) -> Result<(Ty, Ty), String> {
        let lr = lat.resolve(l);
        let rr = lat.resolve(r);
        let num = |t: &Ty| matches!(t, Ty::Int | Ty::Flt);
        let unknown_id = |t: &Ty| match t {
            Ty::Unknown(id) => *id,
            _ => unreachable!("the pin guards only reach unknowns"),
        };
        let unknown = |t: &Ty| matches!(t, Ty::Unknown(_));
        match (&lr, &rr) {
            (a, b) if num(a) && num(b) => Ok((lr.clone(), rr.clone())),
            (a, b) if num(a) && unknown(b) => {
                lat.bind(unknown_id(b), a.clone())?;
                Ok((a.clone(), a.clone()))
            }
            (a, b) if num(b) && unknown(a) => {
                lat.bind(unknown_id(a), b.clone())?;
                Ok((b.clone(), b.clone()))
            }
            (a, b) if unknown(a) && unknown(b) => {
                lat.bind(unknown_id(a), Ty::Int)?;
                lat.bind(unknown_id(b), Ty::Int)?;
                Ok((Ty::Int, Ty::Int))
            }
            _ => Ok((lr, rr)),
        }
    }

    fn pin_scalar_pair(&mut self, lat: &mut UnknownStore, l: &Ty, r: &Ty) -> Result<(), String> {
        let lr = lat.resolve(l);
        let rr = lat.resolve(r);
        let scalar = |t: &Ty| matches!(t, Ty::Int | Ty::Flt | Ty::Bool | Ty::Str);
        match (&lr, &rr) {
            (a, Ty::Unknown(id)) if scalar(a) => {
                lat.bind(*id, a.clone())?;
            }
            (Ty::Unknown(id), b) if scalar(b) => {
                lat.bind(*id, b.clone())?;
            }
            _ => {}
        }
        Ok(())
    }

    fn any_provenance_note(&self, lat: &UnknownStore, ty: &Ty, expr: &Expr) -> Option<String> {
        if !matches!(lat.resolve(ty), Ty::Any) {
            return None;
        }
        let name = match expr {
            Expr::Identifier(n) => n,
            Expr::Index { obj, .. } => match obj.as_ref() {
                Expr::Identifier(n) => n,
                _ => return None,
            },
            _ => return None,
        };
        let line = self.ctx.adopt_lines.get(name)?;
        signal!(trace::TRACE_CHK_ANY_PROVENANCE);
        Some(format!(
            " — '{name}' went dynamic at line {line} (the scalar-kind mix on its cells; \
             adoption is name-global)"
        ))
    }
}

fn types_compatible(l: &Ty, r: &Ty) -> bool {
    match (l, r) {
        (a, b) if a == b => true,
        (Ty::Unknown(_), Ty::Unknown(_)) => true,
        (Ty::Unknown(_), _) | (_, Ty::Unknown(_)) => true,
        (Ty::Tbl(e1), Ty::Tbl(e2)) => types_compatible(e1, e2),
        _ => false,
    }
}

pub(super) fn type_name(ty: &Ty) -> String {
    match ty {
        Ty::Int => "Integer".to_string(),
        Ty::Flt => "Float".to_string(),
        Ty::Bool => "Boolean".to_string(),
        Ty::Str => "String".to_string(),
        Ty::Tbl(elem) => match **elem {
            Ty::Int => "IntTable".to_string(),
            Ty::Flt => "FloatTable".to_string(),
            Ty::Bool => "BoolTable".to_string(),
            Ty::Str => "StringTable".to_string(),
            Ty::Unknown(_) => "Table<?>".to_string(),
            Ty::Any => "AnyTable".to_string(),
            _ => format!("Table of {}", type_name(elem)),
        },
        Ty::Unknown(_) => "?".to_string(),
        Ty::Ffi => "Ffi".to_string(),
        Ty::FfiLib => "FfiLib".to_string(),
        Ty::Coro => "Coro".to_string(),
        Ty::Any => "Any".to_string(),
        // totality only — flow state never rides a resolved checker type
        Ty::Pending => "Pending".to_string(),
        Ty::Conflict => "Conflict".to_string(),
    }
}

fn bin_op_name(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::IntDiv => "//",
        BinOp::Mod => "%",
        BinOp::LessThan => "<",
        BinOp::GreaterThan => ">",
        BinOp::LessEq => "<=",
        BinOp::GreaterEq => ">=",
        BinOp::Equal => "==",
        BinOp::NotEqual => "~=",
        BinOp::And => "and",
        BinOp::Or => "or",
    }
}
