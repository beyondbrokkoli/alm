//! The `Ty` name-renderer, extracted verbatim from mirror's
//! `checker/type_helpers.rs` (L3 receipt: the walk's constraint store
//! errors through `type_name`, so the pure leaf rides early; the rest
//! of that file — `types_compatible`, `body_has_valued_return`,
//! `bin_op_name` — lands with L4's checker, its only consumer).

use crate::shape::ty::Ty;

/// (L4 receipt: the checker's unify error path is this renderer's
/// consumer; it wakes when `UnknownStore::unify` does.)
#[allow(dead_code)]
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
        Ty::Async => "Async".to_string(),
        Ty::Any => "Any".to_string(),
        Ty::Closure(_) => "Closure".to_string(),
        Ty::Pending => "Pending".to_string(),
        Ty::Conflict => "Conflict".to_string(),
    }
}
