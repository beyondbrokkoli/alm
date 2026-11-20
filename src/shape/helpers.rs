use crate::ast::{BinOp, Expr, UnOp};

/// [index-base] The compile-time value of a key expression in PHYSICAL
/// space: the raw folded literal minus `index_base`. Every consumer
/// that compares against a physical slot (`site_slots`, thresholds) or
/// emits a key goes through this one reader, so a base change has
/// exactly one place to be true. An arithmetic overflow on the shift
/// declines the constant (the key rides the expression lane instead).
pub fn const_key_value(e: &Expr, index_base: i64) -> Option<i64> {
    const_key_raw(e).and_then(|v| v.checked_sub(index_base))
}

fn const_key_raw(e: &Expr) -> Option<i64> {
    match e {
        Expr::Integer { value: i, .. } => Some(*i),
        Expr::BinaryOp {
            op, left, right, ..
        } => {
            let (l, r) = (const_key_raw(left)?, const_key_raw(right)?);
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
            ..
        } => const_key_raw(expr).and_then(|v| v.checked_neg()),
        // C: only literal/arith keys fold — everything else rides the
        // expression lane
        Expr::UnaryOp {
            op: UnOp::Not | UnOp::Len,
            ..
        }
        | Expr::Float { .. }
        | Expr::Boolean { .. }
        | Expr::String { .. }
        | Expr::Nil { .. }
        | Expr::TableCtor { .. }
        | Expr::Identifier { .. }
        | Expr::Index { .. }
        | Expr::SysAllocCount { .. }
        | Expr::SysExecCount { .. }
        | Expr::FfiModule { .. }
        | Expr::AsyncModule { .. }
        | Expr::Field { .. }
        | Expr::Function { .. }
        | Expr::Call { .. } => None,
    }
}

pub fn extract_guard(condition: &Expr) -> Option<(&str, &Expr)> {
    if let Expr::BinaryOp {
        op: BinOp::LessThan,
        left,
        right,
        ..
    } = condition
    {
        if let Expr::Identifier { name, .. } = left.as_ref() {
            Some((name.as_str(), right))
        } else {
            None
        }
    } else {
        None
    }
}

/// [index-base] The key's relation to a loop guard, minted in PHYSICAL
/// space: the guard name itself, or the name plus or minus a constant
/// literal (both operand orders for the sum; a constant minus the guard
/// is not invertible and declines). `GuardOffset` carries the literal
/// already folded by the index base (`K_user - index_base`), so facts
/// never see a user-space offset. `Guard` is the bare name in every
/// base; its physical offset is `-index_base` and is derived where
/// offsets are consumed (admission, reserves). `None` is every other
/// shape. (L5's fill-loop detector is this seam's consumer-to-come.)
pub fn guard_key_shape(key: &Expr, guard: &str, index_base: i64) -> Option<crate::shape::KeyShape> {
    use crate::shape::KeyShape;
    let literal = |e: &Expr| match e {
        Expr::Integer { value, .. } => Some(*value),
        _ => None,
    };
    let fold = |k: i64| k.checked_sub(index_base).map(KeyShape::GuardOffset);
    let is_guard = |e: &Expr| matches!(e, Expr::Identifier { name, .. } if name == guard);
    match key {
        Expr::Identifier { name, .. } if name == guard => Some(KeyShape::Guard),
        Expr::BinaryOp {
            op: BinOp::Add,
            left,
            right,
            ..
        } => {
            if is_guard(left) {
                literal(right).and_then(fold)
            } else {
                literal(left).filter(|_| is_guard(right)).and_then(fold)
            }
        }
        Expr::BinaryOp {
            op: BinOp::Sub,
            left,
            right,
            ..
        } => {
            if is_guard(left) {
                literal(right).and_then(|k| k.checked_neg()).and_then(fold)
            } else {
                None
            }
        }
        // C: every other key shape has no relation to the guard — the
        // arithmetic operators, every non-guard identifier, and every
        // non-numeric leaf or composite
        Expr::BinaryOp { .. }
        | Expr::Integer { .. }
        | Expr::Float { .. }
        | Expr::Boolean { .. }
        | Expr::String { .. }
        | Expr::Nil { .. }
        | Expr::TableCtor { .. }
        | Expr::Identifier { .. }
        | Expr::Index { .. }
        | Expr::UnaryOp { .. }
        | Expr::SysAllocCount { .. }
        | Expr::SysExecCount { .. }
        | Expr::FfiModule { .. }
        | Expr::AsyncModule { .. }
        | Expr::Field { .. }
        | Expr::Function { .. }
        | Expr::Call { .. } => None,
    }
}
