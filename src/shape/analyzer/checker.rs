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
use super::{calls_through_fn_var_msg, dotted_callee, value_call_msg};
use crate::ast::{BinOp, CtorKey, Expr, Stmt, UnOp};
use crate::shape::ty::Ty;
use alm_rt::{signal, trace};
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
    /// the Hygiene Law's definition-side record: per fn literal, the
    /// defining-scope chain snapshot the walk took at its definition
    /// (names below top level, None = a non-fn shadow). The call arm
    /// resolves an expansion's free names through it — never through
    /// the caller's frames.
    pub fn_def_sites: BTreeMap<*const Expr, BTreeMap<String, Option<*const Expr>>>,
    /// W3a's walk-side capture sets (the invariance argument at
    /// `fn_captures` in facts.rs) — the checker reads them at creation
    /// sites (the env face) and at call arms (the capture guard).
    pub fn_captures: BTreeMap<*const Expr, BTreeSet<String>>,
}

/// Everything the checker records for the lowerer, handed to `analyze` at
/// assembly time. The substitutions are NOT here — they live in the
/// lattice's `UnknownStore` and ride out of it at assembly.
pub(super) struct CheckFacts {
    pub local_types: BTreeMap<(*const Stmt, Option<*const Expr>, String), Ty>,
    pub fn_defs: BTreeMap<*const Expr, FnDef>,
    pub call_defs: BTreeMap<(*const Expr, *const Expr), *const Expr>,
    pub call_rets: BTreeMap<(*const Expr, *const Expr), Ty>,
    pub env_faces: BTreeMap<*const Expr, BTreeMap<String, Ty>>,
    pub creation_envs: BTreeMap<(*const Expr, *const Expr), *const Expr>,
    pub closure_calls: BTreeSet<(*const Expr, *const Expr)>,
    pub closure_fields: BTreeMap<(usize, String), *const Expr>,
    pub ffi_verbs: BTreeMap<*const Expr, FfiVerb>,
    pub index_key_lanes: BTreeMap<(*const Expr, *const Expr), KeyLane>,
    pub access_elems: BTreeMap<(*const Expr, *const Expr), Ty>,
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
    /// the OUTERMOST call expr of every inline expansion currently being
    /// checked (bottom = outermost site). The pair `(call expr,
    /// first-of-this-stack or the call itself)` is the per-instantiation
    /// fact key both halves share — see the KEYING DISCIPLINE note at
    /// `call_defs` in facts.rs.
    expansion_sites: Vec<*const Expr>,
    /// the checker frame depth each expansion began at: frames BELOW the
    /// innermost boundary belong to the caller — the Hygiene Law keeps
    /// them out of fn resolution.
    expansion_frame_bases: Vec<usize>,
    /// the params of the fn each expansion is inlining — a parameter
    /// shadows every fn name (fn values are never arguments).
    expansion_params: Vec<Vec<String>>,
    seed_read: bool,
    len_deferrals: Vec<(Ty, Option<usize>)>,
    cur_stmt: Option<*const Stmt>,
    loop_depth: usize,
    fn_defs: BTreeMap<*const Expr, FnDef>,
    call_defs: BTreeMap<(*const Expr, *const Expr), *const Expr>,
    call_rets: BTreeMap<(*const Expr, *const Expr), Ty>,
    /// W3a: the per-fn env faces (creation sites record, later sites
    /// unify — monomorphism of the enclosing signature pins the kinds;
    /// the keying discipline at `env_faces` in facts.rs).
    env_faces: BTreeMap<*const Expr, BTreeMap<String, Ty>>,
    /// W3a: the creation sites themselves — `(fn-name identifier,
    /// expansion site) → fn literal` (the lowerer mints here).
    creation_envs: BTreeMap<(*const Expr, *const Expr), *const Expr>,
    /// W3a: which resolved calls dispatch through a closure value (the
    /// lowerer's env-cell read rides this — a D4 dot-ns call lowers
    /// with no read).
    closure_calls: BTreeSet<(*const Expr, *const Expr)>,
    /// W3a: R3's record-face rule — `(ctor site, field name) → fn
    /// literal` (a record's closure cells dispatch by field, the elem
    /// stays the non-closure join).
    closure_fields: BTreeMap<(usize, String), *const Expr>,
    /// W3a: per ACTIVE expansion, Some(env face) at call-throughs (the
    /// closure's captures resolve through it), None at direct
    /// expansions (the defining scope's frames ARE live — P2's
    /// discipline). Parallel to `inline_stack`.
    expansion_envs: Vec<Option<BTreeMap<String, Ty>>>,
    /// W3a: per ACTIVE call-through expansion, the sequential writes
    /// to captured scalars — later statements in the same body read
    /// the override, never the mint-time face (write-through, L3).
    env_overrides: Vec<BTreeMap<String, Ty>>,
    /// W3a's straight-line law for creations: an env mint inside a
    /// conditional arm or loop body has no one register to free at
    /// root exit (the tag-physics of arm frees is walk-planned; envs
    /// are compiler-minted) — creations live in straight-line scope.
    /// The census factories create at the ctor-return; the bound is
    /// documented in the archived W3a closure record (V1 rows).
    cond_depth: usize,
    ffi_verbs: BTreeMap<*const Expr, FfiVerb>,
    index_key_lanes: BTreeMap<(*const Expr, *const Expr), KeyLane>,
    access_elems: BTreeMap<(*const Expr, *const Expr), Ty>,
    local_types: BTreeMap<(*const Stmt, Option<*const Expr>, String), Ty>,
    /// the bare declarations the CHECKER declared, keyed
    /// `(stmt, expansion site, name)` — the B3 (fold d) ruling: the
    /// identity node is PER-EXPANSION (a fresh mint at each site's
    /// declare; None = the checker's top level, itself a single
    /// site). The walk anchors no competing node (H8, 2026-10-26:
    /// the lattice's definition-view `bare_nodes` map is retired —
    /// its ids had no readers left). Finish resolves each node
    /// through the final store into `local_types` under the same key.
    bare_sites: BTreeMap<(*const Stmt, Option<*const Expr>, String), usize>,
    boundary_elem: Option<Ty>,
    diagnostics: Vec<String>,
    /// R15 (owner ruling 2026-10-26): true only while checking the
    /// DIRECT call expression of a `Stmt::Expr` — the procedure form,
    /// the one position where a valueless expansion may sit. The Call
    /// arm takes (and clears) it before checking arguments, so nested
    /// calls stay value positions.
    stmt_position_call: bool,
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
            expansion_sites: Vec::new(),
            expansion_frame_bases: Vec::new(),
            expansion_params: Vec::new(),
            seed_read: false,
            len_deferrals: Vec::new(),
            cur_stmt: None,
            loop_depth: 0,
            fn_defs: BTreeMap::new(),
            call_defs: BTreeMap::new(),
            call_rets: BTreeMap::new(),
            env_faces: BTreeMap::new(),
            creation_envs: BTreeMap::new(),
            closure_calls: BTreeSet::new(),
            closure_fields: BTreeMap::new(),
            expansion_envs: Vec::new(),
            env_overrides: Vec::new(),
            cond_depth: 0,
            ffi_verbs: BTreeMap::new(),
            index_key_lanes: BTreeMap::new(),
            access_elems: BTreeMap::new(),
            local_types: BTreeMap::new(),
            bare_sites: BTreeMap::new(),
            boundary_elem: None,
            diagnostics: Vec::new(),
            stmt_position_call: false,
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

    /// THE HYGIENE LAW's name resolution, one definition for every
    /// consumer: the current expansion's own frames (its params,
    /// locals, same-body blocks), then the defining-scope chain
    /// recorded at the literal's definition (None = a non-fn binding
    /// shadows), then the top-level map — read late, at the current
    /// statement's textual position. Frames below the innermost
    /// expansion boundary are the caller's and never participate.
    /// Returns the innermost HIT (Some(ptr) = an expansion binding,
    /// Some(None) = a shadowing non-fn binding, None = no binding).
    fn resolve_fn_binding(&self, name: &str) -> Option<Option<*const Expr>> {
        let base = self.expansion_frame_bases.last().copied().unwrap_or(0);
        self.frames[base..]
            .iter()
            .rev()
            .find_map(|f| f.fns.get(name).copied())
            .or_else(|| {
                self.inline_stack
                    .last()
                    .and_then(|&cur| self.ctx.fn_def_sites.get(&cur)?.get(name).copied())
            })
            .or_else(|| self.snap.fns.get(name).copied())
    }

    /// Whether a name read as a VALUE names an expansion (the Expansion
    /// Law's reject set: no runtime representation, not a value).
    fn resolves_to_fn(&self, name: &str) -> bool {
        self.resolve_fn_binding(name).flatten().is_some()
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
        // the Lexical Law's collection half (R3): the walk registers a
        // nested fn rebind the moment it walks THIS definition, so the
        // fn maps can point at a literal whose body the checker has not
        // registered (it registers bodies at inline time only). Collect
        // the nested literals now — a read of the rebound name must
        // compile whether or not the container is ever called.
        self.collect_nested_fn_defs(lat, body);
        self.declare_fn_binding(name, Some(expr as *const Expr));
        Ty::Unknown(lat.ensure_fn_value(expr as *const Expr))
    }

    /// Registers every fn literal bound inside `body` — lexically, at
    /// collection time, recursion into nested bodies included. Purely
    /// additive: an already-registered literal (bound by an inline
    /// check, signature already pinned by a call) keeps its entry.
    fn collect_nested_fn_defs(&mut self, lat: &mut UnknownStore, body: &[Stmt]) {
        for stmt in body {
            match stmt {
                Stmt::Assignment { expr, .. } => {
                    if let Expr::Function { params, body } = expr {
                        self.register_collected_fn(lat, expr, params, body);
                    }
                }
                Stmt::LocalDecl { exprs, .. } => {
                    for expr in exprs {
                        if let Expr::Function { params, body } = expr {
                            self.register_collected_fn(lat, expr, params, body);
                        }
                    }
                }
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    self.collect_nested_fn_defs(lat, then_body);
                    self.collect_nested_fn_defs(lat, else_body);
                }
                Stmt::While { body, .. } | Stmt::Do { body } => {
                    self.collect_nested_fn_defs(lat, body);
                }
                _ => {}
            }
        }
    }

    fn register_collected_fn(
        &mut self,
        lat: &mut UnknownStore,
        expr: &Expr,
        params: &[String],
        body: &[Stmt],
    ) {
        let ptr = expr as *const Expr;
        if self.fn_defs.contains_key(&ptr) {
            return;
        }
        let ret = Ty::Unknown(lat.ensure_fn_ret(ptr));
        self.fn_defs.insert(
            ptr,
            FnDef {
                params: params.to_vec(),
                body: body as *const [Stmt],
                ret,
                signature: None,
            },
        );
        self.collect_nested_fn_defs(lat, body);
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
            call_rets,
            env_faces,
            creation_envs,
            closure_calls,
            closure_fields,
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
            call_rets,
            env_faces,
            creation_envs,
            closure_calls,
            closure_fields,
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
        for ret in self.call_rets.values_mut() {
            *ret = lat.resolve(ret);
        }
        // W3a: the env faces ride the same Store Window discipline —
        // recorded early (still-Unknown cells are rewound by later
        // bindings), resolved once here to the one final truth.
        for face in self.env_faces.values_mut() {
            for ty in face.values_mut() {
                *ty = lat.resolve(ty);
            }
        }
    }

    /// The closing resolution pass: the checker holds no scope entries,
    /// so what remains is resolving the recorded facts through
    /// the final constraints — every bare declaration's local type
    /// (the checker's per-expansion identity nodes, B3's fresh mints)
    /// and every access-elem face (constraints bound later — the
    /// boundary elem's seed-read pin, inlined-body unifications — must
    /// flow into them; the lowerer consumes the FINAL truth, not the
    /// mid-check snapshot). THE STORE WINDOW LAW (facts.rs, at
    /// `call_defs`' keying note) is why this rewind is sound: the
    /// store is monotone and every consumer reads this one final
    /// truth, so a fact recorded still-Unknown can only be CLOSED by
    /// a later binding, never contradicted.
    fn resolve_recorded_facts(&mut self, lat: &mut UnknownStore) {
        for ((stmt, site, name), id) in std::mem::take(&mut self.bare_sites) {
            let resolved = lat.resolve(&Ty::Unknown(id));
            self.local_types.insert((stmt, site, name), resolved);
        }
        let resolved: Vec<((*const Expr, *const Expr), Ty)> = self
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

    /// W3a: the innermost ACTIVE call-through's env face — the
    /// closure's capture cells. Applies only while the innermost
    /// expansion IS that call-through (a deeper direct expansion owns
    /// its own chain; the Hygiene Law keeps the env out of it).
    fn active_env(&self) -> Option<&BTreeMap<String, Ty>> {
        self.expansion_envs.last()?.as_ref()
    }

    /// W3a: the same env's sequential overrides (captured scalars
    /// rebound inside this body — write-through, L3).
    fn active_env_override(&self, name: &str) -> Option<Ty> {
        if self.expansion_envs.last()?.is_some() {
            self.env_overrides.last()?.get(name).cloned()
        } else {
            None
        }
    }

    fn active_env_face(&self, name: &str) -> Option<Ty> {
        if let Some(face) = self.active_env() {
            face.get(name).cloned()
        } else {
            None
        }
    }

    /// W3a: the frame-scan bound — frames below the innermost
    /// call-through boundary are the caller's world and never
    /// participate in name resolution inside the closure (the Hygiene
    /// Law's value-name half). Zero when no call-through is active:
    /// today's unbounded discipline, bit for bit.
    fn call_through_base(&self) -> usize {
        self.expansion_envs
            .iter()
            .rposition(|e| e.is_some())
            .map(|i| self.expansion_frame_bases[i])
            .unwrap_or(0)
    }

    fn frames_resolve(&self, name: &str) -> Option<Ty> {
        let base = self.call_through_base();
        self.frames[base..]
            .iter()
            .rev()
            .find_map(|f| f.types.get(name).cloned())
    }

    /// The name→type query. Frames (innermost out, bounded by the
    /// innermost call-through) shadow; the active env's cells answer
    /// captured names (override first — write-through); the top-level
    /// sequential delta shadows the view; everything else is the pure
    /// view over the walk's pre-statement state.
    fn var_type(&mut self, lat: &mut UnknownStore, name: &str) -> Result<Ty, String> {
        if let Some(ty) = self.frames_resolve(name) {
            return Ok(lat.resolve(&ty));
        }
        if let Some(ty) = self.active_env_override(name) {
            return Ok(ty);
        }
        if let Some(ty) = self.active_env_face(name) {
            return Ok(ty);
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

    /// The quiet twin of `var_type` for call-dispatch attempts: a name
    /// that resolves to no callable (undeclared, or a plain value)
    /// answers None instead of its scope error — the caller owns the
    /// diagnostic.
    fn var_type_callable(&mut self, lat: &mut UnknownStore, name: &str) -> Option<Ty> {
        if let Some(ty) = self.frames_resolve(name) {
            return Some(lat.resolve(&ty));
        }
        if let Some(ty) = self.active_env_override(name) {
            return Some(ty);
        }
        if let Some(ty) = self.active_env_face(name) {
            return Some(ty);
        }
        if let Some(ty) = self.top.get(name) {
            return Some(lat.resolve(ty));
        }
        let (view, seed_read) = self.view_type(lat, name, &self.snap);
        if seed_read {
            self.seed_read = true;
        }
        view.map(|t| lat.resolve(&t))
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
                        let ty = self.check_expr(lat, expr)?;
                        Self::reject_face_extraction(expr, &ty)?;
                        expr_types.push(ty);
                    }
                }
                for name in &names[exprs.len()..] {
                    self.declare_fn_binding(name, None);
                }
                for (name, ty) in names.iter().zip(expr_types) {
                    self.declare_var(lat, name.clone(), ty)?;
                }
                for name in &names[exprs.len()..] {
                    // B3 (fold d), the owner ruling 2026-10-26: the bare
                    // declaration's identity node is PER-EXPANSION — a
                    // fresh mint at each site's declare (None = the
                    // checker's top level, itself a single site). Each
                    // expansion lowers its own IR local, so per-expansion
                    // is the truth the lowerer already lives; two sites of
                    // one body may close the same bare local differently
                    // (fn_bare_local_divergent pins the flip). The walk's
                    // definition-view anchoring stays in the lattice's own
                    // map, untouched. Reads through a bare name still
                    // reject via the nil-poison law per expansion — the
                    // node only closes via assignment unification.
                    let site = self.expansion_sites.first().copied();
                    let node = lat.fresh();
                    let id = match node {
                        Ty::Unknown(id) => id,
                        _ => unreachable!("fresh mints an Unknown node"),
                    };
                    self.bare_sites
                        .insert((stmt as *const Stmt, site, name.clone()), id);
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
                // W3a's write-through witness: whether this assignment
                // writes a CAPTURED name of the active call-through (the
                // env owns the cell; the override keeps this body's later
                // statements on the new truth — L3).
                let env_hit = self.active_env().is_some_and(|f| f.contains_key(name))
                    || self
                        .env_overrides
                        .last()
                        .is_some_and(|o| o.contains_key(name));
                if env_hit && !matches!(expected, Ty::Unknown(_)) {
                    // a captured TABLE binding is the env's own — the
                    // move already happened at the mint; a rebind inside
                    // the body has no affine home (census verdict: mutate
                    // cells, or rebind in the defining scope)
                    if matches!(expected, Ty::Tbl(_)) {
                        return Err(format!(
                            "Type Error: '{name}' is a captured table — it cannot be \
                             rebound inside its closure (mutate its cells, or rebind in \
                             the defining scope)"
                        ));
                    }
                }
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
                Self::reject_face_extraction(expr, &actual)?;
                if expected != actual {
                    // every cleanly-joinable elem mix was already adopted
                    // by the lattice (the rebind's site exchange, the
                    // nil/move-severed bridges) before the checker ran —
                    // a mismatch reaching here is a genuine conflict
                    lat.unify(&expected, &actual)?;
                    let resolved = lat.resolve(&actual);
                    self.write_back(name, resolved);
                }
                // W3a: the env cell adopts the rebind either way —
                // later statements in this body read the override (L3)
                if env_hit && let Some(o) = self.env_overrides.last_mut() {
                    o.insert(name.to_string(), lat.resolve(&actual));
                }
            }
            Stmt::IndexAssign { obj, key, value } => {
                let (elem, _obj_desc) = self.check_index_base(lat, obj)?;
                let _key_ty = self.check_index_key(lat, key)?;

                let val_ty = self.check_expr(lat, value)?;

                // W3a (the Escape Law's narrowed reject set): a closure
                // value enters a record's LITERAL fields only — computed
                // cells carry scalars and tables, never faces.
                if matches!(lat.resolve(&val_ty), Ty::Closure(_)) {
                    return Err(
                        "Type Error: a closure value enters only a record's literal \
                         fields — computed cells carry scalars and tables"
                            .to_string(),
                    );
                }

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
                        // unreachable in practice: the closure reject above
                        // fired — the arm keeps the match total
                        Ty::Closure(_) => {
                            return Err(
                                "Type Error: a closure value enters only a record's literal \
                                 fields — computed cells carry scalars and tables"
                                    .to_string(),
                            );
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
                self.cond_depth += 1;
                self.check_block(lat, body);
                self.cond_depth -= 1;
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
                self.cond_depth += 1;
                self.check_block(lat, then_body);
                self.cond_depth -= 1;
                self.end_scope();
                self.begin_scope();
                self.cond_depth += 1;
                self.check_block(lat, else_body);
                self.cond_depth -= 1;
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
                    if matches!(ty, Ty::Closure(_)) {
                        return Err(
                            "Type Error: cannot print a closure — call it, alias it, or \
                             store it in a record field"
                                .to_string(),
                        );
                    }
                }
            }
            Stmt::Expr { expr } => {
                // R15: the whole-statement call is the procedure form —
                // the one position a valueless expansion may occupy.
                if matches!(expr, Expr::Call { .. }) {
                    self.stmt_position_call = true;
                }
                if !self.check_ffi_verb(lat, expr)? {
                    let _ = self.check_expr(lat, expr)?;
                }
                self.stmt_position_call = false;
            }
            Stmt::Return { value } => match self.return_ctxs.last().cloned() {
                Some(ReturnCtx::Boundary) => match value {
                    None | Some(Expr::Nil) => {}
                    Some(expr) => match self.check_expr(lat, expr)? {
                        Ty::Tbl(_) => {
                            // W3a, W3-R5 (the Data Transfer Contract): the
                            // boundary return marshals flat cells to the
                            // host — a closure field would smuggle this
                            // module's heap state across.
                            if self.carries_closure(expr) {
                                return Err(
                                    "Type Error: a closure cannot cross a module boundary — \
                                     the boundary 'return' marshals flat cells only"
                                        .to_string(),
                                );
                            }
                        }
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

    /// The per-instantiation half of the access/key fact keys: the
    /// OUTERMOST expansion the current expression is being checked
    /// inside — the expression itself when it sits at no expansion
    /// (top level degenerates to `(expr, expr)`, mirroring the
    /// call-site convention). Derived exactly as the Call arm derives
    /// its pair keys; the lowerer mirrors this from its own stack.
    fn fact_site(&self, expr: *const Expr) -> *const Expr {
        self.expansion_sites.first().copied().unwrap_or(expr)
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
                let site = self.fact_site(obj as *const Expr);
                self.access_elems
                    .insert((obj as *const Expr, site), (*elem).clone());
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
        let lane = if key_ty == Ty::Str {
            KeyLane::Str
        } else {
            KeyLane::Int
        };
        let site = self.fact_site(key as *const Expr);
        self.index_key_lanes
            .insert((key as *const Expr, site), lane);
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
                                if self.carries_closure(&args[1]) {
                                    return Err("Type Error: a closure cannot cross a module \
                                         boundary — the spawn table marshals flat cells only"
                                        .to_string());
                                }
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
                        // W3a, W3-R5: the drive call marshals the boundary
                        // table into the target process's heap — a closure
                        // field cannot ride it.
                        if self.carries_closure(&args[0]) {
                            return Err("Type Error: a closure cannot cross a module boundary — \
                                 the drive table marshals flat cells only"
                                .to_string());
                        }
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

    /// W3a's THE ESCAPE LAW, creation half: the env face of the fn
    /// literal being read as a value — each capture's resolved type at
    /// THIS program point (frames → active env → top, per `var_type`;
    /// captures are below-top by construction, so a top fall-through
    /// is an undeclared name and rejects naturally). Recorded at the
    /// first creation site; later sites unify — the enclosing
    /// expansion's monomorphic signature pins the kinds, so two sites
    /// of one literal agree or reject as divergent (the Dispatch Law).
    fn create_closure(
        &mut self,
        lat: &mut UnknownStore,
        expr: &Expr,
        name: &str,
        ptr: *const Expr,
    ) -> Result<Ty, String> {
        if self.inline_stack.contains(&ptr) {
            return Err(format!(
                "Type Error: '{name}' cannot escape its own expansion — \
                 a closure cannot capture itself"
            ));
        }
        if self.cond_depth > 0 {
            return Err(format!(
                "Type Error: '{name}' cannot be created inside a conditional arm \
                 or loop body — creations are straight-line (V1)"
            ));
        }
        let caps = self.ctx.fn_captures.get(&ptr).cloned().unwrap_or_default();
        let mut face: BTreeMap<String, Ty> = BTreeMap::new();
        for cap in &caps {
            let ty = self.var_type(lat, cap)?;
            face.insert(cap.clone(), lat.resolve(&ty));
        }
        match self.env_faces.get(&ptr) {
            None => {
                self.env_faces.insert(ptr, face);
            }
            Some(prev) => {
                for (n, t) in &face {
                    match prev.get(n) {
                        Some(p) => {
                            lat.unify(p, t)?;
                        }
                        None => {
                            return Err(format!(
                                "Type Error: '{name}' has no capture '{n}' at an earlier \
                                 creation site — the checker and the analyzer disagree"
                            ));
                        }
                    }
                }
            }
        }
        let site = self.fact_site(expr as *const Expr);
        self.creation_envs.insert((expr as *const Expr, site), ptr);
        Ok(Ty::Closure(ptr))
    }

    /// W3a's Extraction Law: a closure face rides its record's FIELD —
    /// the field read answers the bare env pointer, and the env's ONE
    /// owner is its mint (freed at root exit). A binding that receives
    /// the read would carry an untracked second free at its own scope
    /// exit, so a face read feeds only the escape positions — a call
    /// argument, a return, a literal record field — never a name.
    fn reject_face_extraction(expr: &Expr, ty: &Ty) -> Result<(), String> {
        if matches!(expr, Expr::Field { .. }) && matches!(ty, Ty::Closure(_)) {
            return Err(
                "Type Error: the face rides the field — a closure field cannot be \
                 extracted into a name; call it through the record"
                    .to_string(),
            );
        }
        Ok(())
    }

    /// W3a, R3's record-face read half: does the obj's ctor pin this
    /// field to a closure singleton? V1 bound: the receiver must be a
    /// walk-visible (top-level) name — table identity IS the alias
    /// sites, and only the walk's binding view carries them.
    fn closure_field_fn(&self, obj: &Expr, field: &str) -> Option<*const Expr> {
        let Expr::Identifier(n) = obj else {
            return None;
        };
        let bind = self.snap.binds.get(n)?;
        for s in bind.aliases.iter() {
            if !is_root(s)
                && !is_ghost(s)
                && let Some(ptr) = self.closure_fields.get(&(*s, field.to_string()))
            {
                return Some(*ptr);
            }
        }
        None
    }

    /// W3a, W3-R5 (the Data Transfer Contract): does this table-valued
    /// expr carry a closure field? Such a table may not cross a module
    /// boundary — the env pointer is this module's heap state.
    fn carries_closure(&self, expr: &Expr) -> bool {
        if let Expr::Identifier(n) = expr
            && let Some(bind) = self.snap.binds.get(n)
        {
            return bind.aliases.iter().any(|s| {
                !is_root(s) && !is_ghost(s) && self.closure_fields.keys().any(|(site, _)| site == s)
            });
        }
        false
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
                    // W3a, R3 (the record-face rule): a closure-valued
                    // field pins the ctor's per-field singleton and
                    // NEVER joins the elem — the face rides the field.
                    // Array cells and computed keys carry no closure.
                    if let Ty::Closure(ptr) = ty {
                        match key {
                            CtorKey::Str(field) => {
                                let Some(&site) = self.ctx.sites.get(&(expr as *const Expr)) else {
                                    return Err(
                                        "Type Error: a closure field's constructor carries no \
                                         site — the checker and the analyzer disagree"
                                            .to_string(),
                                    );
                                };
                                self.closure_fields.insert((site, field.clone()), ptr);
                                continue;
                            }
                            _ => {
                                return Err("Type Error: a closure value enters only a record's \
                                     literal fields — array cells and computed keys carry \
                                     scalars and tables"
                                    .to_string());
                            }
                        }
                    }
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
            Expr::Identifier(name) => {
                // THE ESCAPE LAW (W3a, amending law #1): a fn name read
                // as a VALUE is a CREATION — the value is an owned env
                // store naming the expansion. The blanket reject
                // narrows to the consumer-side laws: print, arithmetic,
                // computed-key stores, and the boundary crossing. Call
                // arms resolve callees through the fn maps directly and
                // never reach here.
                if self.resolves_to_fn(name) {
                    let ptr = self
                        .resolve_fn_binding(name)
                        .flatten()
                        .expect("resolves_to_fn");
                    return self.create_closure(lat, expr, name, ptr);
                }
                self.var_type(lat, name)
            }
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
            Expr::Field { obj, name } => {
                // non-callee dot access is a record read; the ffi verbs
                // dispatch in the Call arm before check_expr sees them
                let ty = self.check_expr(lat, obj)?;
                let ty = lat.resolve(&ty);
                match ty {
                    Ty::Tbl(elem) => {
                        // W3a, R3: the closure face rides the FIELD — a
                        // ctor that pinned this field to a closure
                        // singleton answers the singleton here (the
                        // elem stays the non-closure join)
                        if let Some(ptr) = self.closure_field_fn(obj, name) {
                            let site = self.fact_site(obj.as_ref() as *const Expr);
                            self.access_elems
                                .insert((obj.as_ref() as *const Expr, site), Ty::Closure(ptr));
                            return Ok(Ty::Closure(ptr));
                        }
                        // the dispatch: a Table receiver desugars the dot
                        // to a string-keyed index (negative interned key)
                        signal!(trace::TRACE_PARSE_STRKEY_DOT);
                        // a record read answers the table's elem — the
                        // same elem face fact the bracket accesses record
                        signal!(trace::TRACE_CHK_ELEM_FACE);
                        let site = self.fact_site(obj.as_ref() as *const Expr);
                        self.access_elems
                            .insert((obj.as_ref() as *const Expr, site), (*elem).clone());
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
                let name = match callee.as_ref() {
                    Expr::Identifier(n) => n.clone(),
                    Expr::Field { obj, name } => {
                        // D4 call precedence: a dotted callee chain
                        // ("A.b", "A.B.c") that resolves through the fn
                        // maps is an expansion call — the expansion map
                        // wins; module surfaces are the fallback.
                        if let Some(dotted) = dotted_callee(callee.as_ref())
                            && self.resolve_fn_binding(&dotted).is_some()
                        {
                            dotted
                        } else if let Some(ptr) = self.closure_field_fn(obj, name) {
                            // W3a: a record field whose face pins a
                            // closure singleton — the call dispatches
                            // through the field (static, monomorphic).
                            // Record the obj-read face so the lowerer's
                            // cell read lands on the Ptr lane, and the
                            // dispatch kind so a D4 dot-ns call never
                            // reads a cell.
                            let site = self.fact_site(obj.as_ref() as *const Expr);
                            self.access_elems
                                .insert((obj.as_ref() as *const Expr, site), Ty::Closure(ptr));
                            let call_site = self
                                .expansion_sites
                                .first()
                                .copied()
                                .unwrap_or(expr as *const Expr);
                            self.closure_calls.insert((expr as *const Expr, call_site));
                            return self.expand_call(lat, expr, obj, name, ptr, true, args);
                        } else {
                            return self.check_ffi_call(lat, expr, obj, name, args);
                        }
                    }
                    _ => {
                        return Err(calls_through_fn_var_msg());
                    }
                };
                // THE HYGIENE LAW (see `resolve_fn_binding`): caller
                // frames never participate; a parameter shadows every fn
                // name (fn values are never arguments); top-level names
                // are read late, at this call site's textual position.
                let param_shadows = self
                    .expansion_params
                    .last()
                    .is_some_and(|ps| ps.iter().any(|p| p == &name));
                let fn_ptr = if param_shadows {
                    None
                } else {
                    self.resolve_fn_binding(&name).flatten()
                };
                // W3a's DISPATCH: a name the fn maps do not answer may
                // still hold a closure VALUE (a param, an alias, a
                // field-read binding) — its register is the env, and
                // the id rides the type.
                let (fn_ptr, call_through) = match fn_ptr {
                    Some(ptr) => (ptr, false),
                    None => match self.var_type_callable(lat, &name) {
                        Some(Ty::Closure(ptr)) => (ptr, true),
                        _ => {
                            return Err(value_call_msg(&name));
                        }
                    },
                };
                self.expand_call(
                    lat,
                    expr,
                    callee.as_ref(),
                    &name,
                    fn_ptr,
                    call_through,
                    args,
                )
            }
        }
    }

    /// The one inline-expansion path, shared by direct calls and W3a's
    /// call-through dispatch. `call_through` marks a dispatch off a
    /// closure VALUE: the captures resolve through the env (pushed as
    /// the expansion's face), and no live-world guard applies.
    #[allow(clippy::too_many_arguments)]
    fn expand_call(
        &mut self,
        lat: &mut UnknownStore,
        expr: &Expr,
        callee: &Expr,
        name: &str,
        fn_ptr: *const Expr,
        call_through: bool,
        args: &[Expr],
    ) -> Result<Ty, String> {
        if self.inline_stack.contains(&fn_ptr) {
            return Err(format!(
                "Type Error: '{name}' is recursive — inline closures expand at \
                 their call sites, so a call chain may not reach back into itself"
            ));
        }
        if !call_through {
            // W3a's capture guard (the direct-call half): a fn with a
            // non-empty capture set inlines directly only while its
            // captures are LIVE — resolvable in the current frames or
            // an active env. Outside the defining world the call must
            // go through the value.
            if let Some(caps) = self.ctx.fn_captures.get(&fn_ptr)
                && !caps.is_empty()
            {
                for cap in caps {
                    if self.frames_resolve(cap).is_none()
                        && self.active_env_override(cap).is_none()
                        && self.active_env_face(cap).is_none()
                    {
                        return Err(format!(
                            "Type Error: '{name}' is a closure — call it through its value"
                        ));
                    }
                }
            }
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
        let stmt_position = std::mem::take(&mut self.stmt_position_call);
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
                    // W3a, W3-R2 (the Dispatch Law): a
                    // closure-typed PARAMETER pins
                    // per-INSTANTIATION, not per-definition —
                    // two expansions of one body may each feed a
                    // different closure id. The per-instantiation
                    // truth rides the inner dispatch's own
                    // `(call, site)` keys; only the non-closure
                    // kinds carry the per-definition pin.
                    let both_closures = matches!(lat.resolve(f), Ty::Closure(_))
                        && matches!(lat.resolve(a), Ty::Closure(_));
                    if both_closures || lat.unify(f, a).is_ok() {
                        continue;
                    }
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

        let body = unsafe { def.body() };

        // R15 (owner ruling 2026-10-26): an expansion with NO
        // valued return produces no value — consuming its result
        // rejects; the statement position is the procedure form
        // and stays legal. A body with ANY valued return is not
        // valueless: its fall-off path answers the R13 typed zero
        // by the Store Window Law.
        if !stmt_position && !body_has_valued_return(body) {
            return Err(format!(
                "Type Error: '{name}' is an expansion with no return — \
                 it produces no value"
            ));
        }

        // the per-instantiation fact key: the OUTERMOST expansion
        // this call is checked inside (the call itself at no
        // expansion). One call expr may be checked once per site;
        // the pair key keeps every site's resolution its own.
        let call_ptr = expr as *const Expr;
        let site = self.expansion_sites.first().copied().unwrap_or(call_ptr);

        // W3a: the call-through's env face — recorded at the creation
        // site (program order guarantees it precedes every dispatch
        // off the value), resolved through the current store.
        let env_face = if call_through {
            match self.env_faces.get(&fn_ptr) {
                Some(face) => face
                    .iter()
                    .map(|(n, t)| (n.clone(), lat.resolve(t)))
                    .collect(),
                None => {
                    return Err(format!(
                        "Type Error: '{name}' dispatches with no recorded env — \
                         the checker and the analyzer disagree"
                    ));
                }
            }
        } else {
            BTreeMap::new()
        };

        self.inline_stack.push(fn_ptr);
        self.expansion_sites.push(call_ptr);
        self.expansion_frame_bases.push(self.frames.len());
        self.expansion_params.push(def.params.clone());
        self.expansion_envs
            .push(if call_through { Some(env_face) } else { None });
        self.env_overrides.push(BTreeMap::new());
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
        self.expansion_sites.pop();
        self.expansion_frame_bases.pop();
        self.expansion_params.pop();
        self.expansion_envs.pop();
        self.env_overrides.pop();

        // the resolved return type is per-instantiation; the
        // def's own `ret` stays the shared lattice anchor the
        // next expansion seeds its return context from (the
        // monomorphic law is per-definition)
        self.call_rets.insert((call_ptr, site), ret.clone());
        self.call_defs.insert((call_ptr, site), fn_ptr);
        let _ = callee;
        Ok(ret)
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

/// R15: does any statement of this body return a value? Statements
/// only — a nested function literal's returns belong to its own
/// definition, and expression positions cannot hold statements. The
/// parser's desugared shapes (for → Do/While/If) are covered by the
/// recursion, so a `return` inside any loop still counts.
fn body_has_valued_return(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Return { value: Some(_) } => true,
        Stmt::Do { body } | Stmt::While { body, .. } => body_has_valued_return(body),
        Stmt::If {
            then_body,
            else_body,
            ..
        } => body_has_valued_return(then_body) || body_has_valued_return(else_body),
        _ => false,
    })
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
        Ty::Closure(_) => "Closure".to_string(),
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
