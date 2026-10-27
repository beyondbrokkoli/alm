//! THE compiler's one type language (the enum unification, deeper-fold
//! step a): `Pending` is the flow-bottom (the walk's not-yet-decided
//! state), `Unknown(id)` the nominal variable (the constraint store's
//! substitution nodes — unknown node ids from `usize::MAX` down, ghost
//! ids from `usize::MAX/2` down, real site ids `0..n` for Pending sites
//! riding into the checking half), `Conflict` the over-constrained
//! top. The two-language bridge (`ty_to_static`/`static_join`'s
//! conversions) is gone — `materialize_elem` (lattice.rs) is the policy
//! that keeps Pending/Conflict OUT of the artifact path by materializing
//! them as ghost/site `Unknown`s inside the elem table, so every
//! consumer downstream of `ShapeFacts` only ever sees decided kinds
//! (scalars, `Tbl`, the module surfaces, `Any`) and `Unknown`s.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub enum Ty {
    #[default]
    Pending,
    Int,
    Flt,
    Bool,
    Str,
    Tbl(Box<Ty>),
    Ffi,
    FfiLib,
    Coro,
    Any,
    /// W3a (the escaped expansion): an owned env table TYPED by its
    /// expansion — the fn-literal pointer is the expansion id, the
    /// env pointer rides a Ptr register at runtime. Atomic in the
    /// lattice: two ids never join (the Dispatch Law — divergent
    /// expansions cannot meet at one call), one id joins itself.
    Closure(*const Expr),
    Unknown(usize),
    Conflict,
}

use crate::ast::Expr;
use Ty::{Any, Bool, Conflict, Flt, Int, Pending, Str, Tbl};

pub fn pinned_scalar(t: &Ty) -> bool {
    matches!(t, Int | Flt | Bool | Str)
}

pub fn value_kind(t: &Ty) -> bool {
    matches!(t, Int | Flt | Bool | Str | Any)
}

pub fn contains_any(t: &Ty) -> bool {
    match t {
        Any => true,
        Tbl(inner) => contains_any(inner),
        _ => false,
    }
}

/// No flow state anywhere: every leaf is a decided kind. This is the
/// predicate the artifact path's `unreachable!` arms rest on —
/// `materialize_elem` clears Pending/Conflict before facts assemble.
pub fn decided(t: &Ty) -> bool {
    match t {
        Pending | Conflict => false,
        Tbl(inner) => decided(inner),
        _ => true,
    }
}

pub fn join_ty(a: &Ty, b: &Ty) -> Ty {
    match (a, b) {
        (Pending, x) | (x, Pending) => x.clone(),
        (Conflict, _) | (_, Conflict) => Conflict,
        (x, y) if x != y && value_kind(x) && value_kind(y) => Any,
        (Tbl(inner_a), Tbl(inner_b)) => {
            let merged = join_ty(inner_a, inner_b);
            if merged != Conflict {
                Tbl(Box::new(merged))
            } else {
                Conflict
            }
        }
        (x, y) if x == y => x.clone(),
        _ => Conflict,
    }
}

pub fn arith_ty(a: Ty, b: Ty) -> Ty {
    if a == Pending || b == Pending {
        Pending
    } else if a == b && matches!(a, Int | Flt) {
        a
    } else {
        Conflict
    }
}
