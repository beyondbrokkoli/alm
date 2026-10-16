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
    Any,
    Conflict,
}

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
