use super::core::LayoutVerdict;
use crate::ast::{Expr, Stmt};
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
    If(*const Stmt),
    Call(*const Expr),
}

#[derive(Clone)]
pub struct ArmFreeEntry {
    pub carrier: String,
    pub tag: TagSrc,
    pub nothing_on: bool,
    pub keeps: Vec<Keep>,
}

#[derive(Clone)]
pub struct FnDef {
    pub params: Vec<String>,
    pub body: *const [Stmt],
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
    pub unsafe fn body(&self) -> &[Stmt] {
        unsafe { &*self.body }
    }
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
    pub sites: BTreeMap<*const Expr, usize>,
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
    pub free_sites: BTreeSet<*const Stmt>,
    pub free_keeps: BTreeMap<*const Stmt, Vec<Keep>>,
    pub do_exit_frees: BTreeMap<(*const Stmt, u8), Vec<DoExitFree>>,
    pub root_exit_frees: Vec<DoExitFree>,
    pub stmt_temp_frees: BTreeMap<*const Stmt, Vec<usize>>,
    pub cond_temp_frees: BTreeMap<*const Stmt, Vec<usize>>,
    pub arm_temp_frees: BTreeMap<*const Expr, Vec<usize>>,
    pub ret_path_frees: BTreeMap<*const Stmt, Vec<DoExitFree>>,
    pub break_path_frees: BTreeMap<*const Stmt, Vec<DoExitFree>>,
    pub ret_path_keep_frees: BTreeMap<*const Stmt, Vec<DoExitFree>>,
    pub ret_path_keep_temps: BTreeMap<*const Stmt, Vec<usize>>,
    pub rebind_frees: BTreeMap<*const Stmt, BTreeMap<String, Vec<Keep>>>,
    pub join_tags: BTreeMap<*const Stmt, bool>,
    pub call_tags: BTreeMap<*const Expr, Vec<bool>>,
    pub store_ghost_keeps: BTreeMap<*const Stmt, Vec<usize>>,
    pub ctor_ghost_keeps: BTreeMap<*const Expr, Vec<(usize, usize)>>,
    pub arm_free_sites: BTreeMap<*const Stmt, Vec<ArmFreeEntry>>,
    pub arm_rebind_frees: BTreeMap<*const Stmt, Vec<ArmFreeEntry>>,
    pub arm_do_exit_frees: BTreeMap<(*const Stmt, u8), Vec<ArmFreeEntry>>,
    pub arm_root_exit_frees: Vec<ArmFreeEntry>,
    /// (`move_poisons`: the names a statement moved FROM — the lowerer's
    /// null_moves_of zeroes each source register AT the keyed statement,
    /// so a moved binding can never be read or freed twice; the map is
    /// structure (which names died where), the zeroing is
    /// per-instantiation codegen at the site.)
    pub move_poisons: BTreeMap<*const Stmt, BTreeSet<String>>,
    pub name_dense: BTreeMap<(String, usize), bool>,
    /// KEYING DISCIPLINE (H9): keyed by the While stmt node. The plan
    /// is recorded ONCE per loop node in the walk's recorded pass —
    /// structure is instantiation-invariant (the family argument at
    /// `free_sites` above), so a loop inside a fn body inlined at many
    /// call sites lowers the SAME plan at every expansion. Everything
    /// per-instantiation (the lowerer's scope depth, `has_var`, the
    /// depth-matched dense verdict) stays consumption-side — this map
    /// carries only the acceptance decision and its fill bases.
    pub fill_loops: BTreeMap<*const Stmt, FillPlan>,
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
    pub local_types: BTreeMap<(*const Stmt, Option<*const Expr>, String), Ty>,
    pub row_reads: BTreeMap<usize, (String, usize)>,
    pub cell_children: BTreeMap<usize, BTreeSet<usize>>,
    pub fn_scope_keys: BTreeMap<*const Expr, (*const Stmt, u8)>,
    pub fn_touched: BTreeMap<*const Expr, BTreeSet<String>>,
    pub fn_defs: BTreeMap<*const Expr, FnDef>,
    /// KEYING DISCIPLINE (W3a): per fn literal, the RESOLVED env face —
    /// capture name → cell type — recorded at the FIRST creation site
    /// and unified (never contradicted) at later sites: the enclosing
    /// expansion's monomorphic signature pins the capture kinds, so
    /// every creation site of one fn literal in one program agrees.
    /// `resolve_fn_defs_through_subs` re-resolves these through the
    /// final store (the Store Window Law rides here as everywhere).
    pub env_faces: BTreeMap<*const Expr, BTreeMap<String, Ty>>,
    /// KEYING DISCIPLINE: same `(expr, expansion site)` pairs as
    /// `call_defs` — the creation sites themselves: an fn name read as
    /// a VALUE (escape position) mints the env here. Map value is the
    /// fn literal the value names. One identifier expr may be checked
    /// once per expansion site; the pair key keeps each lowering on
    /// its own mint.
    pub creation_envs: BTreeMap<(*const Expr, *const Expr), *const Expr>,
    /// KEYING DISCIPLINE (W3a): same `(call expr, expansion site)`
    /// pairs as `call_defs` — WHICH resolved calls dispatch through a
    /// closure VALUE (a record field's singleton) rather than the
    /// expansion maps. The lowerer must not re-derive the dispatch
    /// kind: a dotted callee may be either a D4 dot-ns expansion call
    /// or a closure-field dispatch, and the two lower differently
    /// (env cell read vs. no read at all).
    pub closure_calls: BTreeSet<(*const Expr, *const Expr)>,
    /// KEYING DISCIPLINE (W3a, R3's record-face rule): (ctor SITE,
    /// field name) → the fn literal the field carries. The closure
    /// face rides the FIELD, never the elem — a record's array elem
    /// stays the non-closure join, and the field's dispatch id is
    /// pinned per constructor, so `t.f(...)` resolves the singleton
    /// statically. Sites flow to readers through the existing alias
    /// machinery (that is what table identity IS in the checker's
    /// world).
    pub closure_fields: BTreeMap<(usize, String), *const Expr>,
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
    pub call_defs: BTreeMap<(*const Expr, *const Expr), *const Expr>,
    /// KEYING DISCIPLINE: same `(call expr, expansion site)` pairs as
    /// `call_defs` — the RESOLVED return type of that one expansion.
    /// `FnDef.ret` stays the per-definition lattice anchor (the
    /// monomorphic law is per-definition); the resolved truth a call
    /// site's lowering consumes is per-instantiation, recorded here.
    pub call_rets: BTreeMap<(*const Expr, *const Expr), Ty>,
    /// INVARIANCE ARGUMENT (fold d, B4) — why `ffi_verbs` needs NO
    /// expansion-site key, unlike its checker-recorded neighbors: a
    /// verb is (member name, base-type family); the member name is
    /// fixed text in the AST node itself, and acceptance fixes the
    /// family per expansion — if two expansions of one body both
    /// accept the same dotted call, both resolved the SAME base-type
    /// family, hence the same verb. A base that changed families
    /// between sites would have been REJECTED in one expansion, and
    /// acceptance is per-program. One expr, one verb, every site.
    pub ffi_verbs: BTreeMap<*const Expr, FfiVerb>,
    /// KEYING DISCIPLINE: same `(expr, expansion site)` pairs as
    /// `call_defs` — the addressing lane of THIS one expansion's key.
    /// The key expr may sit inside a body inlined at many call sites;
    /// each expansion's lane is its own truth (a late-bound callee can
    /// return an Integer at one site and a String at another).
    pub index_key_lanes: BTreeMap<(*const Expr, *const Expr), KeyLane>,
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
    pub access_elems: BTreeMap<(*const Expr, *const Expr), Ty>,
    pub stmt_lines: BTreeMap<*const Stmt, usize>,
    pub ctor_lines: Vec<usize>,
    #[allow(dead_code)]
    pub adopt_lines: BTreeMap<String, usize>,
    pub diagnostics: Vec<Diagnostic>,
}

impl ShapeFacts {
    pub fn elem_of(&self, ctor: &Expr) -> Ty {
        let id = self.sites[&(ctor as *const Expr)];
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
        self.free_sites.contains(&(stmt as *const Stmt))
    }
}
