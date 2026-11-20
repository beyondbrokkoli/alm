use crate::ast::{BinOp, Expr, Loc, NodeId, Stmt, UnOp};
use std::collections::BTreeSet;

pub fn desugar_numeric_for(
    at: Loc,
    var: String,
    start: Expr,
    limit: Expr,
    body: Vec<Stmt>,
    inclusive: bool,
) -> Stmt {
    let limit_slot = "for$limit".to_string();
    // [for-limit] The for-limit surface: an inclusive value latches
    // `limit + 1` and keeps the `i < for$limit` guard — the comparison,
    // the census fingerprint, and every downstream consumer are
    // identical in both modes, and the +1 folds once at the latch so
    // the latched-once law survives. The guard never changes.
    let latched_limit = if inclusive {
        Expr::BinaryOp {
            op: BinOp::Add,
            left: Box::new(limit),
            right: Box::new(Expr::Integer {
                value: 1,
                id: NodeId::mint(),
            }),
            id: NodeId::mint(),
        }
    } else {
        limit
    };
    let increment = Stmt::Assignment {
        name: var.clone(),
        expr: Expr::BinaryOp {
            op: BinOp::Add,
            left: Box::new(Expr::Identifier {
                name: var.clone(),
                id: NodeId::mint(),
            }),
            right: Box::new(Expr::Integer {
                value: 1,
                id: NodeId::mint(),
            }),
            id: NodeId::mint(),
        },
        loc: at,
        id: NodeId::mint(),
    };
    Stmt::Do {
        body: vec![
            Stmt::LocalDecl {
                names: vec![var.clone()],
                exprs: vec![start],
                loc: at,
                id: NodeId::mint(),
            },
            Stmt::LocalDecl {
                names: vec![limit_slot.clone()],
                exprs: vec![latched_limit],
                loc: at,
                id: NodeId::mint(),
            },
            Stmt::While {
                condition: Expr::BinaryOp {
                    op: BinOp::LessThan,
                    left: Box::new(Expr::Identifier {
                        name: var,
                        id: NodeId::mint(),
                    }),
                    right: Box::new(Expr::Identifier {
                        name: limit_slot,
                        id: NodeId::mint(),
                    }),
                    id: NodeId::mint(),
                },
                body: vec![
                    Stmt::Do {
                        body,
                        loc: at,
                        id: NodeId::mint(),
                    },
                    increment,
                ],
                loc: at,
                id: NodeId::mint(),
            },
        ],
        loc: at,
        id: NodeId::mint(),
    }
}

/// One target of a tuple assignment: a cell (`t[k]`, or `t.k` with its
/// key already folded to a string) or a bare name.
#[derive(Debug)]
pub enum TupleTarget {
    Cell { obj: Expr, key: Expr },
    Name(String),
}

/// A target prefix (obj or key) latches into a temp iff the judge's
/// pre-store evaluation window can observe it: it reads a cell, calls,
/// samples the system counters, mints a table (a ctor allocates and
/// runs its entries) — or names a variable one of this tuple's own
/// name stores rebinds before the prefix's store lands (`rebound`).
/// Everything else (literals, other names, arithmetic over them) is
/// frozen across the window, so an unlatched prefix reads the same
/// value at store time as it would have at latch time. Literal keys
/// especially stay inline — the static-key laws key on them.
fn prefix_needs_latch(e: &Expr, rebound: &BTreeSet<&str>) -> bool {
    match e {
        Expr::Identifier { name, .. } => rebound.contains(name.as_str()),
        Expr::Index { .. }
        | Expr::Field { .. }
        | Expr::Call { .. }
        | Expr::TableCtor { .. }
        | Expr::SysAllocCount { .. }
        | Expr::SysExecCount { .. } => true,
        Expr::UnaryOp { op: UnOp::Len, .. } => true,
        Expr::UnaryOp { expr, .. } => prefix_needs_latch(expr, rebound),
        Expr::BinaryOp { left, right, .. } => {
            prefix_needs_latch(left, rebound) || prefix_needs_latch(right, rebound)
        }
        _ => false,
    }
}

/// The judge's tuple-assignment law (Lua 5.1 manual §2.4.3; probed on
/// luajit 2.1.1794214635, lua5.4 agreeing): every target's table and
/// key evaluates before any store, then the stores land
/// right-to-left. The temps below compose one decl whose left-to-right
/// evaluation is that order — latch exprs in target order, then the
/// RHS values — followed by the stores in reverse target order.
///
/// A name target has no prefix: it contributes no latch, and its store
/// rebinds the name to its value temp. That rebind is the one store a
/// cell prefix can observe — `b[j], j = 20, j + 1` rebinds `j` first
/// (right-to-left) yet the judge's `b[j]` reads the old `j` — so a
/// cell prefix latches the names that name targets to its RIGHT
/// rebind, the only stores landing before its own. Names stored to its
/// left rebind after it and stay inline: `i, a[i] = i + 1, 20` needs
/// no latch, and a plain-name obj moves no table it does not have to.
pub fn desugar_tuple_assign(at: Loc, targets: Vec<TupleTarget>, values: Vec<Expr>) -> Stmt {
    debug_assert_eq!(
        targets.len(),
        values.len(),
        "tuple counts match (parser-enforced)"
    );
    debug_assert!(
        targets.len() >= 2,
        "single targets never ride the tuple path"
    );
    let n = targets.len();
    // The latch verdicts, right to left: the names seen so far are
    // exactly the rebinds landing before target i's own store.
    let mut latches = vec![(false, false); n];
    {
        let mut rebound: BTreeSet<&str> = BTreeSet::new();
        for (i, target) in targets.iter().enumerate().rev() {
            match target {
                TupleTarget::Cell { obj, key } => {
                    latches[i] = (
                        prefix_needs_latch(obj, &rebound),
                        prefix_needs_latch(key, &rebound),
                    );
                }
                TupleTarget::Name(name) => {
                    rebound.insert(name.as_str());
                }
            }
        }
    }
    // Inline prefixes ride the store unmoved; latched prefixes move
    // into the decl. Each original node lands in the tree exactly once.
    enum Slot {
        Cell {
            obj: Option<Expr>,
            key: Option<Expr>,
        },
        Name(String),
    }
    let mut names: Vec<String> = Vec::with_capacity(2 * n + values.len());
    let mut exprs: Vec<Expr> = Vec::with_capacity(2 * n + values.len());
    let mut slots: Vec<Slot> = Vec::with_capacity(n);
    for (i, target) in targets.into_iter().enumerate() {
        match target {
            TupleTarget::Cell { obj, key } => {
                let (latch_obj, latch_key) = latches[i];
                let obj = if latch_obj {
                    names.push(format!("tuple$o{i}"));
                    exprs.push(obj);
                    None
                } else {
                    Some(obj)
                };
                let key = if latch_key {
                    names.push(format!("tuple$k{i}"));
                    exprs.push(key);
                    None
                } else {
                    Some(key)
                };
                slots.push(Slot::Cell { obj, key });
            }
            TupleTarget::Name(name) => slots.push(Slot::Name(name)),
        }
    }
    for (i, value) in values.into_iter().enumerate() {
        names.push(format!("tuple$t{i}"));
        exprs.push(value);
    }
    let temp = |name: String| Expr::Identifier {
        name,
        id: NodeId::mint(),
    };
    let stores = slots
        .into_iter()
        .enumerate()
        .rev()
        .map(|(i, slot)| match slot {
            Slot::Cell { obj, key } => {
                let obj = obj.unwrap_or_else(|| temp(format!("tuple$o{i}")));
                let key = key.unwrap_or_else(|| temp(format!("tuple$k{i}")));
                Stmt::IndexAssign {
                    obj,
                    key,
                    value: temp(format!("tuple$t{i}")),
                    loc: at,
                    id: NodeId::mint(),
                }
            }
            Slot::Name(name) => Stmt::Assignment {
                name,
                expr: temp(format!("tuple$t{i}")),
                loc: at,
                id: NodeId::mint(),
            },
        });
    let mut body = vec![Stmt::LocalDecl {
        names,
        exprs,
        loc: at,
        id: NodeId::mint(),
    }];
    body.extend(stores);
    Stmt::Do {
        body,
        loc: at,
        id: NodeId::mint(),
    }
}
