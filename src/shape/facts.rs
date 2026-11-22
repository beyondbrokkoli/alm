use super::core::LayoutVerdict;
use crate::ast::{Expr, NodeId, Stmt};
use crate::diag::Diagnostic;
use crate::shape::Ty;
use std::collections::{BTreeMap, BTreeSet};

/// [ownership] A name a free keeps alive (its row alias survives the
/// drop), or a ghost the release spares. One row, exactly one keeper —
/// the walk's release planning mints these.
#[derive(Clone, PartialEq, Debug)]
pub enum Keep {
    Name(String),
    #[allow(dead_code)]
    Ghost(usize),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TagSrc {
    If(NodeId),
    Call(NodeId),
}

/// [ownership] One arm-split free: a mixed join whose arms release
/// differently, so the free rides the join's tag instead of the drop
/// site.
#[derive(Clone)]
pub struct ArmFreeEntry {
    pub carrier: String,
    pub tag: TagSrc,
    pub nothing_on: bool,
    pub keeps: Vec<Keep>,
}

/// [index-base] How a fast-store key relates to its loop guard (L5's
/// fill-loop detector consumes it; the helpers mint it now because the
/// seam's types belong to the walk). `Guard` is the key the guard name
/// currently names; `GuardOffset(k)` is that name plus the constant
/// `k` (`j - 1` is `GuardOffset(-1)`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum KeyShape {
    Guard,
    GuardOffset(i64),
}

/// One fn literal the checker collected — params, body text, and the
/// monomorphic ret/signature the call expansions unify against.
#[derive(Clone)]
pub struct FnDef {
    pub params: Vec<String>,
    pub body: Vec<Stmt>,
    pub ret: Ty,
    pub signature: Option<Vec<Ty>>,
}

impl FnDef {
    pub fn body(&self) -> &[Stmt] {
        &self.body
    }
}

/// [ffi] One `ffi.new` mint, recorded at the call site the lowerer
/// (L7) and the reserve-plan builder (L5) both consume straight. The
/// elem/capacity come from the cdef registry at the checker's choke
/// point — never re-derived downstream.
#[derive(Clone, Debug)]
pub struct FfiMint {
    /// The local name the minted table binds (the second-writer
    /// contract is per-name).
    pub name: String,
    pub elem: Ty,
    pub capacity: i64,
}

/// [ffi] The checker's resolved verb table — one entry per accepted
/// ffi/async call node; the gate and the lowerer read it straight.
#[derive(Clone)]
pub enum FfiVerb {
    Load,
    ArgKind,
    Cdef,
    New {
        #[allow(dead_code)]
        name: String,
    },
    Sizeof {
        bytes: i64,
    },
    AsyncCreate,
    AsyncResume,
    AsyncYield,
    AsyncStatus,
    AsyncClose,
    Drive {
        base: String,
        sym: String,
    },
}

/// The M2 builtin table: assert/error/tonumber are checker builtins —
/// a call whose name resolves to no user binding falls to the builtin
/// table, the checker records the verb here, and the lowerer (L7)
/// consumes it straight (the ffi_verbs seam, one lane over).
#[derive(Clone)]
pub enum BuiltinVerb {
    Assert,
    Error,
    ToNumber,
}

/// Which lane an index key took — the instance record's per-node
/// fact, minted by the checker's key check.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KeyLane {
    Int,
    Str,
}

/// A call expansion's identity. ROOT (0) is the script's own extent;
/// every `mint_instance` mints the next id (per-compile deterministic:
/// ROOT seeded at construction, first expansion 1 — the same sequence
/// mirror's first compile mints; the counter is the Checker's own, not
/// a process global, so the in-process sweeps compare equal).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstanceId(pub u32);

impl InstanceId {
    pub const ROOT: InstanceId = InstanceId(0);
}

/// [ownership] One call expansion's record. The checker writes it as
/// the expansion runs; the lowerer (L7) reads the ret/env/key-lane/
/// access faces to lower each site against its instance. (The whole
/// struct rides `#[allow(dead_code)]` until then — mirror's readers
/// are the lowerer's files.)
#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct InstanceInfo {
    pub call: Option<NodeId>,
    pub fn_node: Option<NodeId>,
    pub params: Vec<String>,
    pub body: Vec<Stmt>,
    pub frame_base: usize,
    pub break_base: usize,
    pub env_face: Option<BTreeMap<String, Ty>>,
    pub ret: Option<Ty>,
    pub children: BTreeMap<NodeId, BTreeSet<InstanceId>>,
    pub creation_envs: BTreeMap<NodeId, NodeId>,
    pub closure_calls: BTreeSet<NodeId>,
    pub index_key_lanes: BTreeMap<NodeId, KeyLane>,
    pub access_elems: BTreeMap<NodeId, Ty>,
}

/// [ownership] The walk's output plus the checker's (the L4 merge: the
/// interleaved checker mints its families into the same facts) — never
/// a surface field (the P5 cure: the lowerer will take `(ShapeFacts,
/// &Surface)` as two inputs; `index_base` is dropped forever).
///
/// The diet ledger: L5 adds fast_stores/reserve_plans; L6 adds the
/// exit-fate families (do_exit_frees, root_exit_frees,
/// stmt/cond/arm_temp_frees, ret_path_*, break_path_*,
/// arm_do_exit_frees, arm_root_exit_frees).
#[derive(Clone)]
pub struct ShapeFacts {
    pub sites: BTreeMap<NodeId, usize>,
    pub elems: Vec<Ty>,
    #[allow(dead_code)]
    pub layouts: Vec<LayoutVerdict>,
    pub free_sites: BTreeSet<NodeId>,
    pub free_keeps: BTreeMap<NodeId, Vec<Keep>>,
    pub rebind_frees: BTreeMap<NodeId, BTreeMap<String, Vec<Keep>>>,
    pub join_tags: BTreeMap<NodeId, bool>,
    pub call_tags: BTreeMap<NodeId, Vec<bool>>,
    pub store_ghost_keeps: BTreeMap<NodeId, Vec<usize>>,
    pub ctor_ghost_keeps: BTreeMap<NodeId, Vec<(usize, usize)>>,
    pub arm_free_sites: BTreeMap<NodeId, Vec<ArmFreeEntry>>,
    pub arm_rebind_frees: BTreeMap<NodeId, Vec<ArmFreeEntry>>,
    pub move_poisons: BTreeMap<NodeId, BTreeSet<String>>,
    pub stored_ctor_parents: BTreeSet<usize>,
    pub substitutions: BTreeMap<usize, Ty>,
    pub row_reads: BTreeMap<usize, (String, usize)>,
    pub cell_children: BTreeMap<usize, BTreeSet<usize>>,
    pub fn_scope_keys: BTreeMap<NodeId, (NodeId, u8)>,
    pub fn_touched: BTreeMap<NodeId, BTreeSet<String>>,
    /// Each fn literal's capture name -> the walk-scope index its
    /// binding lives at, minted at definition. (The L4 source swap:
    /// the walk stamps it, the checker carries the same map through
    /// its ctx — the facts take the checker's copy.)
    pub fn_capture_depths: BTreeMap<NodeId, BTreeMap<String, usize>>,
    /// Every fn literal's body-scope walk depth: the index its body
    /// scope occupies on the walk stack at the definition site.
    pub fn_body_depths: BTreeMap<NodeId, usize>,
    // — the checker-minted families (L4). Every lowerer-consumed field
    // rides #[allow(dead_code)] until L7 reads it; `ffi_verbs` has its
    // reader now — the pipeline's ffi gate.
    #[allow(dead_code)]
    pub boundary_elem: Option<Ty>,
    #[allow(dead_code)]
    pub local_types: BTreeMap<(NodeId, InstanceId, String), Ty>,
    #[allow(dead_code)]
    pub fn_defs: BTreeMap<NodeId, FnDef>,
    #[allow(dead_code)]
    pub env_faces: BTreeMap<NodeId, BTreeMap<String, Ty>>,
    #[allow(dead_code)]
    pub env_face_depths: BTreeMap<NodeId, BTreeMap<String, usize>>,
    #[allow(dead_code)]
    pub closure_fields: BTreeMap<(usize, String), NodeId>,
    #[allow(dead_code)]
    pub call_fns: BTreeMap<NodeId, BTreeSet<NodeId>>,
    pub ffi_verbs: BTreeMap<NodeId, FfiVerb>,
    #[allow(dead_code)]
    pub builtin_verbs: BTreeMap<NodeId, BuiltinVerb>,
    #[allow(dead_code)]
    pub ffi_mints: BTreeMap<NodeId, FfiMint>,
    #[allow(dead_code)]
    pub instances: BTreeMap<InstanceId, InstanceInfo>,
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

    /// The dump's read of a lattice type: substitutions applied, table
    /// skins resolved inward. (alm-only surface for the stage dump.)
    pub fn resolved(&self, ty: &Ty) -> Ty {
        self.resolve_elem_type(ty.clone())
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
