use super::ty::{Ty, join_ty};
use std::collections::{BTreeMap, BTreeSet};

/// [index-base] The sparse-layout threshold, mirror's exact constant.
/// Mirror home is `alm_rt::rt::SPARSE_THRESHOLD` (the runtime crate is
/// the compiler's own lib there); alm re-homes it here at L3 — the
/// walk's threshold check is its first consumer — and the L9 runtime
/// port consumes this const, never re-declares it.
pub const SPARSE_THRESHOLD: i64 = 100_000;
pub const BOUNDS_FAIL_THRESHOLD: i64 = i64::MAX / 8;
pub const NULL_ROOT: usize = usize::MAX;
pub const MOVED_ROOT: usize = usize::MAX - 1;
pub const BOUNDARY_ROOT: usize = usize::MAX - 2;
/// A pre-bound target's shape face is still pending: the binding exists
/// — its fn face rides it through the initializer's body walk — but
/// shape reads must treat the name as not yet declared and resolve
/// outward, exactly as when the shape binding did not exist. The
/// oracle's `resolve` skips it; `is_root` excludes it from every site
/// filter, so no consumer mistakes the marker for a real alias.
pub const DECL_PENDING: usize = usize::MAX - 3;

pub fn is_root(s: &usize) -> bool {
    *s == NULL_ROOT || *s == MOVED_ROOT || *s == BOUNDARY_ROOT || *s == DECL_PENDING
}

pub const ROW_GHOST_FLOOR: usize = usize::MAX / 2;

pub fn is_ghost(s: &usize) -> bool {
    *s >= ROW_GHOST_FLOOR && !is_root(s)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum LayoutVerdict {
    #[default]
    Dense,
    Growing,
    Sparse,
    BoundsFail,
}

impl LayoutVerdict {
    pub fn join(self, other: LayoutVerdict) -> LayoutVerdict {
        use LayoutVerdict::*;
        match (self, other) {
            (BoundsFail, _) | (_, BoundsFail) => BoundsFail,
            (Sparse, _) | (_, Sparse) => Sparse,
            (Growing, _) | (_, Growing) => Growing,
            _ => Dense,
        }
    }
}

pub type RowLineage = BTreeMap<usize, (String, usize)>;

#[derive(Clone, PartialEq, Debug)]
pub struct TableShape {
    pub ty: Ty,
    pub layout: LayoutVerdict,
    pub aliases: BTreeSet<usize>,
    pub lineage: RowLineage,
}

impl TableShape {
    pub fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;

        let new_ty = join_ty(&self.ty, &other.ty);
        if matches!(new_ty, Ty::Conflict) && !matches!(self.ty, Ty::Conflict) {
            crate::alm_dbgln!("[shape-join] {:?} join {:?} = Conflict", self.ty, other.ty);
        }
        if self.ty != new_ty {
            self.ty = new_ty;
            changed = true;
        }

        let new_layout = self.layout.join(other.layout);
        if self.layout != new_layout {
            self.layout = new_layout;
            changed = true;
        }

        let len_before = self.aliases.len();
        self.aliases.extend(&other.aliases);
        if self.aliases.len() > len_before {
            changed = true;
        }

        for (&site, (name, depth)) in &other.lineage {
            match self.lineage.entry(site) {
                std::collections::btree_map::Entry::Vacant(v) => {
                    v.insert((name.clone(), *depth));
                    changed = true;
                }
                std::collections::btree_map::Entry::Occupied(mut o) => {
                    if *depth > o.get().1 {
                        o.get_mut().1 = *depth;
                        changed = true;
                    }
                }
            }
        }

        changed
    }
}
