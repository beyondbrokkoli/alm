use super::core::TableShape;
use crate::ast::{BinOp, Expr, UnOp};
use std::collections::BTreeMap;

pub fn const_key_value(e: &Expr) -> Option<i64> {
    match e {
        Expr::Integer(i) => Some(*i),
        Expr::BinaryOp { op, left, right } => {
            let (l, r) = (const_key_value(left)?, const_key_value(right)?);
            match op {
                BinOp::Add => l.checked_add(r),
                BinOp::Sub => l.checked_sub(r),
                BinOp::Mul => l.checked_mul(r),
                _ => None,
            }
        }
        Expr::UnaryOp {
            op: UnOp::Neg,
            expr,
        } => const_key_value(expr).and_then(|v| v.checked_neg()),
        _ => None,
    }
}

/// The fill-loop guard face of a while condition: `guard < bound`
/// answers both halves (H9 — the bound rides out with the guard so the
/// ONE acceptance predicate can check the reserve's stability law at
/// the same site the plan is recorded).
pub fn extract_guard(condition: &Expr) -> Option<(&str, &Expr)> {
    if let Expr::BinaryOp {
        op: BinOp::LessThan,
        left,
        right,
    } = condition
    {
        if let Expr::Identifier(name) = left.as_ref() {
            Some((name.as_str(), right))
        } else {
            None
        }
    } else {
        None
    }
}

pub fn merge_table_scopes(
    into: &mut [BTreeMap<String, TableShape>],
    a: &[BTreeMap<String, TableShape>],
    b: &[BTreeMap<String, TableShape>],
) {
    for ((into_slot, a_slot), b_slot) in into.iter_mut().zip(a).zip(b) {
        for (name, val) in into_slot.iter_mut() {
            if let Some(x) = a_slot.get(name) {
                val.join(x);
            }
            if let Some(x) = b_slot.get(name) {
                val.join(x);
            }
        }
    }
}
