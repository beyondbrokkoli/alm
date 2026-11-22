use crate::ast::{BinOp, Stmt};
use crate::shape::ty::Ty;

pub(super) fn types_compatible(l: &Ty, r: &Ty) -> bool {
    match (l, r) {
        (a, b) if a == b => true,
        (Ty::Unknown(_), Ty::Unknown(_)) => true,
        (Ty::Unknown(_), _) | (_, Ty::Unknown(_)) => true,
        (Ty::Tbl(e1), Ty::Tbl(e2)) => types_compatible(e1, e2),
        _ => false,
    }
}

pub(super) fn body_has_valued_return(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Return { value: Some(_), .. } => true,
        Stmt::Do { body, .. } | Stmt::While { body, .. } => body_has_valued_return(body),
        Stmt::If {
            then_body,
            else_body,
            ..
        } => body_has_valued_return(then_body) || body_has_valued_return(else_body),
        _ => false,
    })
}

pub(in crate::shape::analyzer) fn type_name(ty: &Ty) -> String {
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

pub(super) fn bin_op_name(op: &BinOp) -> &'static str {
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
        BinOp::Concat => "..",
        BinOp::And => "and",
        BinOp::Or => "or",
    }
}
