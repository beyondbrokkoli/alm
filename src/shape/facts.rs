use super::core::LayoutVerdict;
use crate::ast::{Expr, NodeId, Stmt};
use crate::diag::Diagnostic;
use crate::shape::Ty;
use alm_rt::{signal, trace};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, PartialEq, Debug)]
pub enum Keep {
    Name(String),
    #[allow(dead_code)]
    Ghost(usize),
}

#[derive(Clone)]
pub struct DoExitFree {
    #[allow(dead_code)]
    pub site: usize,
    pub carrier: String,
    pub keeps: Vec<Keep>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TagSrc {
    If(NodeId),
    Call(NodeId),
}

#[derive(Clone)]
pub struct ArmFreeEntry {
    pub carrier: String,
    pub tag: TagSrc,
    pub nothing_on: bool,
    pub keeps: Vec<Keep>,
}

/// The fn literal's body, OWNED (H6): identity rides the node's id,
/// not its address, so the facts are self-contained — the AST may move
/// or die after analysis and the recorded bodies stay valid. A copy of
/// a node IS the node (the id copies with it); construction is the
/// only way to mint a new one, and the derivation pass's identity
/// census (analysis.rs) keeps duplicate ids out of any tree it reads.
#[derive(Clone)]
pub struct FnDef {
    pub params: Vec<String>,
    pub body: Vec<Stmt>,
    pub ret: Ty,
    pub signature: Option<Vec<Ty>>,
}

/// The checker's resolved decision for one dotted ffi/coroutine call
/// site. The checker validates member, arity, and operand types exactly
/// once and records the verdict here; the lowerer consumes it instead of
/// re-deriving the same decision from its own walk (every re-derivation
/// was a fresh desync surface). Operands stay positional: the verb names
/// the face, the call's own `args` slice carries the operands — the two
/// walks read the identical AST node, so the positions cannot drift.
#[derive(Clone)]
pub enum FfiVerb {
    Load,
    ArgKind,
    Cdef,
    CoroCreate,
    CoroResume,
    CoroYield,
    CoroStatus,
    CoroClose,
    /// The drive call: `lib.sym(tbl)` — base and symbol named because
    /// neither is an operand position.
    Drive {
        base: String,
        sym: String,
    },
}

/// The addressing lane of one index key, decided by the checker at the
/// key choke point (`check_index_key`); the lowerer consumes it instead
/// of re-deriving the lane from its own walk of the key expression.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KeyLane {
    Int,
    Str,
}

impl FnDef {
    pub fn body(&self) -> &[Stmt] {
        &self.body
    }
}

/// One materialized expansion instance (H12/7a): the checker's
/// `expand_call` mints one id per EXPANSION EVENT, at entry — not per
/// resolved pair. Analysis-world, deliberately type-distinct from
/// `NodeId` (the fold's tooth: an instance id can never be confused
/// with a node id). The mint is PRIVATE to the checker (one writer,
/// one atomic counter twin to `NodeId::mint` — "one construction
/// mints one instance"); `ROOT` is the one non-minted id, the
/// checker's top level (ruling R2 — 7c re-keys `local_types`' site
/// onto it so the `Option` dies).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstanceId(pub u32);

impl InstanceId {
    /// The checker's top level, minted at `Checker` construction
    /// (never drawn from the counter — the mint starts at 1). Top-level
    /// self-pairs `(expr, expr)` are the root instance's dynamic
    /// extent, exactly as an expansion's pairs are its own.
    pub const ROOT: InstanceId = InstanceId(0);
}

/// The instance record (H12/7a): everything one expansion event knows,
/// recorded at the checker's expansion entry and filled beside the
/// pair-keyed inserts. `body` copies `FnDef`'s OWNED-body shape (H6's
/// dividend: identity rides the node id, the facts are self-contained).
/// The shadow maps (`children`, `creation_envs`, `closure_calls`,
/// `index_key_lanes`, `access_elems`) are the instance-keyed view of
/// the six pair-keyed maps, built ALONGSIDE them (never consumed in
/// 7a); the assembly-side assert in `analyze_with`'s finish holds the
/// two views equal every compile. 7b consumes; 7c kills the pair view.
///
/// KEYING DISCIPLINE (the site law): the instance that owns a pair
/// `(expr, site)` is the OUTERMOST expansion's instance — the one
/// minted for `site`'s own expansion — at ANY nesting depth inside it
/// (`fact_site` = `expansion_sites.first()`). A nested instance's five
/// shadow maps are therefore EMPTY by law: facts checked inside it key
/// against the outermost site, and only the outermost instance's
/// record carries them.
///
/// R4's note: `children` is SET-valued because one call expr may mint
/// MANY instances under one owner (the same body expanded twice inside
/// one extent — g called twice from f's body); the pair stays
/// truth-keyed (one entry — monomorphism forces the events to agree),
/// instances are event-minted. The assert verifies every event's view
/// equals the pair truth.
#[derive(Clone, Debug)]
pub struct InstanceInfo {
    /// the call expr whose expansion minted this instance; None = ROOT
    /// (the top level is nobody's call).
    pub call: Option<NodeId>,
    /// the callee fn literal this expansion inlines; None = ROOT.
    pub fn_node: Option<NodeId>,
    pub params: Vec<String>,
    /// the inlined body, OWNED (H6 shape); empty for ROOT in 7a (7c
    /// rules the root's face when `local_types` re-keys).
    pub body: Vec<Stmt>,
    /// the checker's frame depth at entry (`frames.len()` — the
    /// Hygiene Law's caller-frame boundary; checker-world fact).
    pub frame_base: usize,
    /// the ABSOLUTE loop depth at entry: the caller's absolute base
    /// plus this body-relative depth (ruling R1 — the arithmetic twin
    /// of the lowerer's `break_ctxs.len()` push, same AST, same
    /// count).
    pub break_base: usize,
    /// R3: the call-through env face at entry (Some only for closure
    /// dispatches — the same face `expansion_envs` pushes);
    /// `env_overrides` stays checker-local sequential state.
    pub env_face: Option<BTreeMap<String, Ty>>,
    /// the expansion's resolved return, filled beside `call_rets`'
    /// pair insert; None until that insert lands (a post-mint reject
    /// can leave a minted instance unbRIDged — allowed only on
    /// rejected compiles, see the shadow's totality gate).
    pub ret: Option<Ty>,
    /// R4: the call exprs that minted child instances during this
    /// instance's DYNAMIC EXTENT (any depth — the site law above),
    /// each mapping to every instance it minted here. 7b's D4
    /// precedence asks membership of this map.
    pub children: BTreeMap<NodeId, BTreeSet<InstanceId>>,
    /// the instance view of `creation_envs` (creation sites minted in
    /// this extent — value: the fn literal the value names).
    pub creation_envs: BTreeMap<NodeId, NodeId>,
    /// the instance view of `closure_calls` (calls dispatching through
    /// a closure value in this extent).
    pub closure_calls: BTreeSet<NodeId>,
    /// the instance view of `index_key_lanes`.
    pub index_key_lanes: BTreeMap<NodeId, KeyLane>,
    /// the instance view of `access_elems`.
    pub access_elems: BTreeMap<NodeId, Ty>,
}

/// The one fill-loop acceptance predicate's recorded decision (H9):
/// which tables a `guard < bound` loop fills at the guard key, split by
/// store depth — `fills` are direct bases (`t[i] = …`), `nested_fills`
/// are row bases (`t[x][i] = …`). The walk's `detect_fill_loop` decides
/// acceptance once (no break, guard born nonneg and only ascending,
/// stable bound) and records the plan; the lowerer consumes it instead
/// of re-deriving the decision from its own walk.
#[derive(Clone)]
pub struct FillPlan {
    pub fills: BTreeSet<String>,
    pub nested_fills: BTreeSet<String>,
}

#[derive(Clone)]
pub struct ShapeFacts {
    pub sites: BTreeMap<NodeId, usize>,
    pub elems: Vec<Ty>,
    pub boundary_elem: Option<Ty>,
    #[allow(dead_code)]
    pub layouts: Vec<LayoutVerdict>,
    /// INVARIANCE ARGUMENT (fold d, B4) — the walk's structure family
    /// (`free_sites` through `move_poisons` below): every one of these
    /// maps records WHICH control edges and structural sites exist
    /// (scope exits, keeps, temp sites, tag edges, poisons) — facts
    /// about the AST's shape, not about types. They are recorded ONCE
    /// by the walk at the definition and consumed per expansion by the
    /// lowerer, which is sound because structure is
    /// instantiation-INVARIANT: a body inlined at many call sites has
    /// the same statements, the same scope tree, and the same exit
    /// edges at every site. Nothing kind-flavored may join this family
    /// without gaining the `(expr/stmt, expansion site)` key.
    pub free_sites: BTreeSet<NodeId>,
    pub free_keeps: BTreeMap<NodeId, Vec<Keep>>,
    pub do_exit_frees: BTreeMap<(NodeId, u8), Vec<DoExitFree>>,
    pub root_exit_frees: Vec<DoExitFree>,
    pub stmt_temp_frees: BTreeMap<NodeId, Vec<usize>>,
    pub cond_temp_frees: BTreeMap<NodeId, Vec<usize>>,
    pub arm_temp_frees: BTreeMap<NodeId, Vec<usize>>,
    pub ret_path_frees: BTreeMap<NodeId, Vec<DoExitFree>>,
    pub break_path_frees: BTreeMap<NodeId, Vec<DoExitFree>>,
    pub ret_path_keep_frees: BTreeMap<NodeId, Vec<DoExitFree>>,
    pub ret_path_keep_temps: BTreeMap<NodeId, Vec<usize>>,
    pub rebind_frees: BTreeMap<NodeId, BTreeMap<String, Vec<Keep>>>,
    pub join_tags: BTreeMap<NodeId, bool>,
    pub call_tags: BTreeMap<NodeId, Vec<bool>>,
    pub store_ghost_keeps: BTreeMap<NodeId, Vec<usize>>,
    pub ctor_ghost_keeps: BTreeMap<NodeId, Vec<(usize, usize)>>,
    pub arm_free_sites: BTreeMap<NodeId, Vec<ArmFreeEntry>>,
    pub arm_rebind_frees: BTreeMap<NodeId, Vec<ArmFreeEntry>>,
    pub arm_do_exit_frees: BTreeMap<(NodeId, u8), Vec<ArmFreeEntry>>,
    pub arm_root_exit_frees: Vec<ArmFreeEntry>,
    /// (`move_poisons`: the names a statement moved FROM — the lowerer's
    /// null_moves_of zeroes each source register AT the keyed statement,
    /// so a moved binding can never be read or freed twice; the map is
    /// structure (which names died where), the zeroing is
    /// per-instantiation codegen at the site.)
    pub move_poisons: BTreeMap<NodeId, BTreeSet<String>>,
    pub name_dense: BTreeMap<(String, usize), bool>,
    /// KEYING DISCIPLINE (H9): keyed by the While stmt node. The plan
    /// is recorded ONCE per loop node in the walk's recorded pass —
    /// structure is instantiation-invariant (the family argument at
    /// `free_sites` above), so a loop inside a fn body inlined at many
    /// call sites lowers the SAME plan at every expansion. Everything
    /// per-instantiation (the lowerer's scope depth, `has_var`, the
    /// depth-matched dense verdict) stays consumption-side — this map
    /// carries only the acceptance decision and its fill bases.
    pub fill_loops: BTreeMap<NodeId, FillPlan>,
    pub stored_ctor_parents: BTreeSet<usize>,
    pub substitutions: BTreeMap<usize, Ty>,
    /// KEYING DISCIPLINE (B3, fold d): keyed by the triple
    /// `(decl stmt, expansion site, name)` — the resolved type of ONE
    /// expansion's bare declaration (`local x` with no value). The
    /// site is the OUTERMOST expansion the declaration was checked
    /// inside (None = the checker's top level, itself a single
    /// site), derived exactly as the call-key sites are. Two
    /// expansions of one body may close the same bare local
    /// differently — each expansion lowers its own IR local, and this
    /// key keeps each lowering on its own resolved truth.
    pub local_types: BTreeMap<(NodeId, Option<NodeId>, String), Ty>,
    pub row_reads: BTreeMap<usize, (String, usize)>,
    pub cell_children: BTreeMap<usize, BTreeSet<usize>>,
    pub fn_scope_keys: BTreeMap<NodeId, (NodeId, u8)>,
    pub fn_touched: BTreeMap<NodeId, BTreeSet<String>>,
    pub fn_defs: BTreeMap<NodeId, FnDef>,
    /// KEYING DISCIPLINE (W3a): per fn literal, the RESOLVED env face —
    /// capture name → cell type — recorded at the FIRST creation site
    /// and unified (never contradicted) at later sites: the enclosing
    /// expansion's monomorphic signature pins the capture kinds, so
    /// every creation site of one fn literal in one program agrees.
    /// `resolve_fn_defs_through_subs` re-resolves these through the
    /// final store (the Store Window Law rides here as everywhere).
    pub env_faces: BTreeMap<NodeId, BTreeMap<String, Ty>>,
    /// KEYING DISCIPLINE: same `(expr, expansion site)` pairs as
    /// `call_defs` — the creation sites themselves: an fn name read as
    /// a VALUE (escape position) mints the env here. Map value is the
    /// fn literal the value names. One identifier expr may be checked
    /// once per expansion site; the pair key keeps each lowering on
    /// its own mint.
    pub creation_envs: BTreeMap<(NodeId, NodeId), NodeId>,
    /// KEYING DISCIPLINE (W3a): same `(call expr, expansion site)`
    /// pairs as `call_defs` — WHICH resolved calls dispatch through a
    /// closure VALUE (a record field's singleton) rather than the
    /// expansion maps. The lowerer must not re-derive the dispatch
    /// kind: a dotted callee may be either a D4 dot-ns expansion call
    /// or a closure-field dispatch, and the two lower differently
    /// (env cell read vs. no read at all).
    pub closure_calls: BTreeSet<(NodeId, NodeId)>,
    /// KEYING DISCIPLINE (W3a, R3's record-face rule): (ctor SITE,
    /// field name) → the fn literal the field carries. The closure
    /// face rides the FIELD, never the elem — a record's array elem
    /// stays the non-closure join, and the field's dispatch id is
    /// pinned per constructor, so `t.f(...)` resolves the singleton
    /// statically. Sites flow to readers through the existing alias
    /// machinery (that is what table identity IS in the checker's
    /// world).
    pub closure_fields: BTreeMap<(usize, String), NodeId>,
    /// KEYING DISCIPLINE (the R1 law): keyed by the pair
    /// `(call expr, expansion site)` where the expansion site is the
    /// OUTERMOST call whose inline expansion the call expr is being
    /// checked/lowered inside — the call expr itself when it sits at no
    /// expansion. One AST node lowers once PER EXPANSION SITE; the pair
    /// key restores that one-write-one-read discipline for a body
    /// inlined at many call sites. Both halves derive the site from
    /// their own recursion (no counters, no clocks): the checker checks
    /// and the lowerer lowers the identical AST in the identical order.
    /// Union consumers (fn_touched scans) must range over all sites of
    /// a call expr, never assume a single entry.
    ///
    /// THE STORE WINDOW LAW (fold d stated it; R13 closed it
    /// 2026-10-26): finish re-resolves every pair-keyed fact through
    /// the FINAL substitution store (`resolve_fn_defs_through_subs`,
    /// `resolve_recorded_facts`), so a fact recorded still-Unknown IS
    /// rewindable by a later binding — the mechanism is real (R13's
    /// probe matrix: a valueless definition's ret anchor, recorded
    /// Unknown at insertion, rewritten by a later assignment before
    /// finish resolves the recorded rets) — but every path through
    /// the window converges on the ONE final truth, so it cannot
    /// answer silently wrong. Four probes
    /// (2026-10-26) close it: (1) the store is MONOTONE with a
    /// single final truth — `unify` rejects a divergent second
    /// binding (the monomorphic argument/return laws, the elem unify
    /// at every store), so a later binding can only CLOSE a recorded
    /// Unknown, never contradict it. (2) Every consumer reads the
    /// final truth — the finish passes rewrite the recorded faces and
    /// the ctor's allocation derives from the same final elem, so
    /// check-time acceptance, access face, and allocation are one
    /// truth; a pre-binding runtime read answers the final elem's
    /// zero. (3) A still-Unknown operand cannot ride into a fact: a
    /// bare declaration's node rejects at the lifetime law before any
    /// face could record it, a still-Unknown argument unifies against
    /// the monomorphic signature at the call, lane facts pin Unknown
    /// keys to Int AT the choke point, and the boundary seed resolves
    /// to the module-global truth uniformly (one face for every
    /// expansion). (4) The one fact class that WAS recorded
    /// still-Unknown by design — a valueless definition's ret, R13's
    /// witness shape — is now gated at the door (R15, owner ruling
    /// 2026-10-26): consuming the result of an expansion with no
    /// valued return rejects at the call
    /// (`fn_valueless_call_rejected`); only the statement-position
    /// procedure call remains, and nothing consumes its ret. A body
    /// with ANY valued return still rides the law: its fall-off path
    /// materializes the bound face's typed zero (the null through the
    /// Str face, i64 0 through Int), never a miscoerced register. The
    /// window opens; the truth that walks through it is still the one
    /// final truth. Resolving at insertion would close the mechanism
    /// itself, but no divergence exists to close — this note is the
    /// law, not a debt.
    pub call_defs: BTreeMap<(NodeId, NodeId), NodeId>,
    /// KEYING DISCIPLINE: same `(call expr, expansion site)` pairs as
    /// `call_defs` — the RESOLVED return type of that one expansion.
    /// `FnDef.ret` stays the per-definition lattice anchor (the
    /// monomorphic law is per-definition); the resolved truth a call
    /// site's lowering consumes is per-instantiation, recorded here.
    pub call_rets: BTreeMap<(NodeId, NodeId), Ty>,
    /// INVARIANCE ARGUMENT (fold d, B4) — why `ffi_verbs` needs NO
    /// expansion-site key, unlike its checker-recorded neighbors: a
    /// verb is (member name, base-type family); the member name is
    /// fixed text in the AST node itself, and acceptance fixes the
    /// family per expansion — if two expansions of one body both
    /// accept the same dotted call, both resolved the SAME base-type
    /// family, hence the same verb. A base that changed families
    /// between sites would have been REJECTED in one expansion, and
    /// acceptance is per-program. One expr, one verb, every site.
    pub ffi_verbs: BTreeMap<NodeId, FfiVerb>,
    /// KEYING DISCIPLINE: same `(expr, expansion site)` pairs as
    /// `call_defs` — the addressing lane of THIS one expansion's key.
    /// The key expr may sit inside a body inlined at many call sites;
    /// each expansion's lane is its own truth (a late-bound callee can
    /// return an Integer at one site and a String at another).
    pub index_key_lanes: BTreeMap<(NodeId, NodeId), KeyLane>,
    /// KEYING DISCIPLINE: same `(expr, expansion site)` pairs as
    /// `call_defs` — the element face of one table access base, per
    /// expansion: recorded at the access choke points
    /// (`check_index_base` for bracket reads/writes, the Field
    /// receiver arm for dot reads) and consumed straight by the
    /// lowerer's Index/IndexAssign/Field faces, so the ctor's
    /// allocation and every access face come from one decision. A
    /// base reached in two expansions of one body may carry two faces
    /// (a late-bound callee's return elem differs per site); the pair
    /// key keeps each expansion's lowering on its own face.
    pub access_elems: BTreeMap<(NodeId, NodeId), Ty>,
    /// H12/7a — the materialized expansion instances, minted at the
    /// checker's `expand_call` ENTRY (one id per expansion EVENT) with
    /// the instance-keyed shadow maps built ALONGSIDE the pair-keyed
    /// maps above (the KEYING DISCIPLINE at `InstanceInfo`); consumed
    /// by nobody yet. The assembly-side shadow assert
    /// (`analyze_with`'s finish) holds the instance view equal to the
    /// pair view every compile; 7b consumes, 7c kills the pair view.
    pub instances: BTreeMap<InstanceId, InstanceInfo>,
    /// H12/7a — the bridge: every pair key `(expr, site)` → the
    /// OWNING instance (the outermost expansion's instance; ROOT for
    /// top-level self-pairs — uniform over all six pair-keyed maps;
    /// a call pair's own instances hang off the owner's children
    /// set). Rides every pair-keyed insert; dies with the pair maps
    /// in 7c (or at 7b, if the consumption fold makes it redundant).
    pub instance_of: BTreeMap<(NodeId, NodeId), InstanceId>,
    pub ctor_lines: Vec<usize>,
    #[allow(dead_code)]
    pub adopt_lines: BTreeMap<String, usize>,
    pub diagnostics: Vec<Diagnostic>,
}

impl ShapeFacts {
    pub fn elem_of(&self, ctor: &Expr) -> Ty {
        let id = self.sites[&ctor.id()];
        let elem = self.elems[id].clone();
        self.resolve_elem_type(elem)
    }

    fn resolve_elem_type(&self, ty: Ty) -> Ty {
        match &ty {
            Ty::Unknown(id) => match self.substitutions.get(id) {
                Some(resolved) => self.resolve_elem_type(resolved.clone()),
                None => ty,
            },
            Ty::Tbl(inner) => {
                let resolved = self.resolve_elem_type((**inner).clone());
                Ty::Tbl(Box::new(resolved))
            }
            _ => ty,
        }
    }

    pub fn is_dense_at_depth(&self, name: &str, depth: usize) -> bool {
        self.name_dense
            .get(&(name.to_string(), depth))
            .copied()
            .unwrap_or(false)
    }

    pub fn check_row_reads(&mut self) {
        let reads: Vec<(usize, String, usize)> = self
            .row_reads
            .iter()
            .map(|(&base, (name, depth))| (base, name.clone(), *depth))
            .collect();
        let mut reported: BTreeSet<usize> = BTreeSet::new();
        for (base, name, depth) in reads {
            let mut level: BTreeSet<usize> =
                self.cell_children.get(&base).cloned().unwrap_or_default();
            for _pierce in 2..=depth {
                let mut next: BTreeSet<usize> = BTreeSet::new();
                for row in level {
                    if reported.insert(row)
                        && matches!(
                            self.resolve_elem_type(self.elems[row].clone()),
                            Ty::Unknown(_)
                        )
                    {
                        signal!(trace::TRACE_ANALYZE_MISSING_VALUE);
                        let line = self.ctor_lines[row];
                        self.diagnostics.push(
                            Diagnostic::ty(format!(
                                "a row of '{name}' is read before it is \
                                 ever given a value (table site #{row})"
                            ))
                            .with_site(Some(line)),
                        );
                    }
                    if let Some(kids) = self.cell_children.get(&row) {
                        next.extend(kids.iter().copied());
                    }
                }
                level = next;
            }
        }
    }

    pub fn is_free(&self, stmt: &Stmt) -> bool {
        self.free_sites.contains(&stmt.id())
    }
}
