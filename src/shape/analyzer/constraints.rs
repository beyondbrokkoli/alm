//! The unknown-constraint store — the lattice home of the checker's
//! substitution algebra. Nominal unknown
//! nodes — the boundary `arg` seed, function return nodes, per-call
//! parameter instances — are minted HERE, anchored
//! by the lattice walk where it can see the structure (the boundary seed
//! at lattice construction, returns in `walk_fn_def`); everything the
//! walk cannot anchor (call-site parameter
//! instances, the dummy a function VALUE binds under, and — since B3,
//! fold d — every bare declaration's per-expansion identity node) is
//! minted through the same store by the checking half. Pins and
//! unifications land as
//! substitutions in this ONE store — `resolve` is the query, `bind` and
//! `unify` are the constraint ops, standing beside the elem lattice's
//! `decide`. The assembled facts derive `substitutions` straight from
//! here; the checker owns no algebra of its own.
//!
//! Id-space partition: unknown node ids mint downward from `usize::MAX`,
//! disjoint in practice from real
//! table site ids (`0..n`), row ghosts (`usize::MAX/2` up) and the
//! static-elem ghosts (`usize::MAX/2` down). Substitutions may also key
//! on REAL site ids: a site whose elem was still Pending at
//! `compute_static_elems` (function bodies, boundary-fed constructors)
//! rides `Unknown(site)` into the checking half, whose pins close it —
//! the site and the node disciplines meet in this one store.

use super::checker::type_name;
use crate::ast::Expr;
use crate::diag::Diagnostic;
use crate::shape::Ty;
use alm_rt::{signal, trace};
use std::collections::BTreeMap;

pub(super) struct UnknownStore {
    /// the constraint pins: unknown node id -> the type it was fixed to
    subs: BTreeMap<usize, Ty>,
    /// the minter, counting down from `usize::MAX`
    next_id: usize,
    /// the boundary `arg` table's element node — minted once, at lattice
    /// construction; the checking half's seed reads this same node
    boundary_seed: Option<usize>,
    /// return nodes for function definitions, anchored by `walk_fn_def`
    fn_ret_nodes: BTreeMap<*const Expr, usize>,
    /// value nodes for function definitions — the dummy a function VALUE
    /// binds under, anchored per definition (the name→type view derives
    /// a fn binding's type from it, stably)
    fn_value_nodes: BTreeMap<*const Expr, usize>,
}

impl UnknownStore {
    /// Constructs the store and mints the boundary seed — the lattice's
    /// opening move, exactly where the standalone checker's `seed` used
    /// to mint the first unknown.
    pub(super) fn new() -> Self {
        let mut store = Self {
            subs: BTreeMap::new(),
            next_id: usize::MAX,
            boundary_seed: None,
            fn_ret_nodes: BTreeMap::new(),
            fn_value_nodes: BTreeMap::new(),
        };
        store.boundary_seed = Some(store.mint_id());
        store
    }

    fn mint_id(&mut self) -> usize {
        let id = self.next_id;
        self.next_id -= 1;
        id
    }

    /// Mints a fresh, unanchored unknown node.
    pub(super) fn fresh(&mut self) -> Ty {
        Ty::Unknown(self.mint_id())
    }

    pub(super) fn boundary_seed(&self) -> usize {
        self.boundary_seed
            .expect("the store construction mints the seed")
    }

    /// The return node for one function definition — anchored by
    /// `walk_fn_def`.
    pub(super) fn ensure_fn_ret(&mut self, fn_ptr: *const Expr) -> usize {
        if let Some(&id) = self.fn_ret_nodes.get(&fn_ptr) {
            return id;
        }
        let id = self.mint_id();
        self.fn_ret_nodes.insert(fn_ptr, id);
        id
    }

    /// Read-only view of the same anchor (the walk's use-site pinning
    /// derives a call's node from it).
    pub(super) fn fn_ret_node(&self, fn_ptr: *const Expr) -> Option<usize> {
        self.fn_ret_nodes.get(&fn_ptr).copied()
    }

    /// The value node for one function definition — the dummy its VALUE
    /// binds under. Anchored here (minted by the checking half at the
    /// definition, once per definition) so the name→type view can derive
    /// a fn binding's type without the checker storing an entry.
    pub(super) fn ensure_fn_value(&mut self, fn_ptr: *const Expr) -> usize {
        if let Some(&id) = self.fn_value_nodes.get(&fn_ptr) {
            return id;
        }
        let id = self.mint_id();
        self.fn_value_nodes.insert(fn_ptr, id);
        id
    }

    /// Read-only view of the same anchor.
    pub(super) fn fn_value_node(&self, fn_ptr: *const Expr) -> Option<usize> {
        self.fn_value_nodes.get(&fn_ptr).copied()
    }

    /// Read-only view of the minter's head (the id-space census in
    /// `analyze_with` checks the down-counting families' headroom
    /// against the row ghosts growing up).
    pub(super) fn next_id(&self) -> usize {
        self.next_id
    }

    pub(super) fn take_subs(&mut self) -> BTreeMap<usize, Ty> {
        std::mem::take(&mut self.subs)
    }

    pub(super) fn resolve(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Unknown(id) => match self.subs.get(id) {
                Some(resolved) => self.resolve(resolved),
                None => ty.clone(),
            },
            Ty::Tbl(inner) => Ty::Tbl(Box::new(self.resolve(inner))),
            other => other.clone(),
        }
    }

    fn occurs(&self, id: usize, ty: &Ty) -> bool {
        match ty {
            Ty::Unknown(other) => {
                *other == id
                    || self
                        .subs
                        .get(other)
                        .is_some_and(|bound| self.occurs(id, bound))
            }
            Ty::Tbl(inner) => self.occurs(id, inner),
            _ => false,
        }
    }

    pub(super) fn bind(&mut self, id: usize, ty: Ty) -> Result<(), Diagnostic> {
        if self.occurs(id, &ty) {
            signal!(trace::TRACE_FAIL_OCCURS_CHECK);
            return Err(Diagnostic::ty(
                "cyclic table type — a table's element type \
                 may not contain the table itself (alm's element types are finite)",
            ));
        }
        signal!(trace::TRACE_CHK_UNIFY);
        self.subs.insert(id, ty);
        Ok(())
    }

    pub(super) fn unify(&mut self, expected: &Ty, actual: &Ty) -> Result<(), Diagnostic> {
        let expected = self.resolve(expected);
        let actual = self.resolve(actual);
        match (&expected, &actual) {
            (a, b) if a == b => Ok(()),

            (Ty::Unknown(id_a), Ty::Unknown(id_b)) if id_a != id_b => {
                self.bind(*id_b, Ty::Unknown(*id_a))
            }

            (Ty::Unknown(_), _) | (_, Ty::Unknown(_)) => {
                let (u_id, c_ty) = match (&expected, &actual) {
                    (Ty::Unknown(id), ty) => (*id, ty.clone()),
                    (ty, Ty::Unknown(id)) => (*id, ty.clone()),
                    _ => unreachable!(),
                };
                self.bind(u_id, c_ty)
            }

            (Ty::Tbl(e1), Ty::Tbl(e2)) => self.unify(e1, e2),

            // THE DISPATCH LAW (W3a): two DIFFERENT expansion ids may
            // never join — static monomorphic dispatch needs the
            // singleton id held through the dataflow; a join of two
            // ids at one site is L2 (the fat cell), which is parked.
            (Ty::Closure(a), Ty::Closure(b)) if a != b => Err(Diagnostic::ty(
                "divergent expansions cannot meet at one call",
            )),

            _ => Err(Diagnostic::ty(format!(
                "type conflict — {} vs {}",
                type_name(&expected),
                type_name(&actual)
            ))),
        }
    }
}
