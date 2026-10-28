//! THE ELABORATION BOUNDARY (H8). The parser's desugars are PURE
//! tree-to-tree functions, one per sugar — every multi-statement
//! desugar lives HERE, takes the parsed pieces plus the sugar
//! header's `Loc`, and stamps `at` on every synthetic statement it
//! mints (R7's law: the desugar family reports at the header). The
//! 1:1 sugars (D4 `function f`, `local function`, dot-assign) mint
//! exactly ONE core node at their parse sites and stay there — there
//! is no elaboration to draw a boundary around. The checker and the
//! lowerer match ONLY core shapes; they never learn a sugar exists.
//!
//! Three guards hold this boundary, by locality:
//! - the unit goldens (property_tests.rs) pin each elaborator's
//!   output SHAPE and stamps directly, without parsing;
//! - THE DESUGAR ATTRIBUTION CENSUS (analysis.rs, permanent) walks
//!   the finished tree on every compile — the whole-tree omniscience
//!   check that no unspellable-branded family drifted;
//! - the corpus pins exercise the shipped path end to end.
//!
//! Every future sugar (for-in, anything the port rules in) is a new
//! pure function here plus its census family plus its pins — parser
//! entanglement and whole-tree hand-sync do not regrow.

use crate::ast::{BinOp, Expr, Loc, Stmt};

/// `for i = a, b do B end` is half-open (a ..< b) and becomes
/// Do[ local i = a, local for$limit = b,
///              While i < for$limit { Do[ B ]; i = i + 1 } ]
/// so the existing while phi/fill machinery handles everything. The
/// limit LATCHES: b evaluates once at entry, before the first test —
/// a body that rebinds b's source name cannot move the bound
/// mid-flight (the R7 law). `for$limit` is unspellable (identifiers
/// are [a-zA-Z_][a-zA-Z0-9_]*, lexer.rs), so user code cannot read,
/// assign, or collide with it. The user body rides its own inner
/// scope: a `local i` in B shadows the counter only inside B, so the
/// synthetic increment after it still reaches the counter (without
/// the wrap it would increment the shadow — an infinite loop).
/// Analysis walks the desugared tree, so *const Stmt keys stay
/// consistent. All six statements (block Do, counter decl, latch
/// decl, While, inner Do, increment) carry the header's `at`.
pub fn desugar_numeric_for(
    at: Loc,
    var: String,
    start: Expr,
    limit: Expr,
    body: Vec<Stmt>,
) -> Stmt {
    let limit_slot = "for$limit".to_string();
    let increment = Stmt::Assignment {
        name: var.clone(),
        expr: Expr::BinaryOp {
            op: BinOp::Add,
            left: Box::new(Expr::Identifier(var.clone())),
            right: Box::new(Expr::Integer(1)),
        },
        loc: at,
    };
    Stmt::Do {
        body: vec![
            Stmt::LocalDecl {
                names: vec![var.clone()],
                exprs: vec![start],
                loc: at,
            },
            Stmt::LocalDecl {
                names: vec![limit_slot.clone()],
                exprs: vec![limit],
                loc: at,
            },
            Stmt::While {
                condition: Expr::BinaryOp {
                    op: BinOp::LessThan,
                    left: Box::new(Expr::Identifier(var)),
                    right: Box::new(Expr::Identifier(limit_slot)),
                },
                body: vec![Stmt::Do { body, loc: at }, increment],
                loc: at,
            },
        ],
        loc: at,
    }
}

/// Multi-target tuple assignment, ruled PARALLEL (Lua's law, argued
/// probe-first 2026-10-28): `t[k0], t[k1], … = v0, v1, …` becomes
///
/// Do[ local tuple$t0, tuple$t1, … = v0, v1, …
///              t[k0] = tuple$t0; t[k1] = tuple$t1; … ]
///
/// The multi-name LocalDecl evaluates EVERY value before ANY binding
/// (the parallel atom — the swap idiom `o[0], o[1] = o[1], o[0]`
/// swaps, where a sequential store-per-value desugar silently
/// computes the wrong answer, both cells the old o[1]). The stores
/// then run in target order over already-read values; target keys
/// re-read at store time, exactly Lua's assignment phase. Table-valued
/// RHS keep the dialect's own move law unchanged: distinct tables
/// move once each into their cells; the same table twice rejects
/// through the LocalDecl's one-receiving-binding law — the same
/// verdict two sequential store statements earn today, never a silent
/// alias. `tuple$tN` is unspellable (`$` cannot appear in
/// identifiers), so the temps cannot be read, assigned, or shadowed
/// by user code, and the Do scopes them to the statement: two tuple
/// assigns in one block mint independent `tuple$t0`s in sibling
/// scopes. Precondition (parser-enforced, named refusals there):
/// `cells.len() == values.len() >= 2`, every cell an already-shaped
/// index target (bracket or dot-converted — the dot-write law fires
/// at the parse site, not here; this function is pure). The census
/// family in analysis.rs fingerprints the `tuple$tN` names over the
/// loc-derived map on every compile.
pub fn desugar_tuple_assign(at: Loc, cells: Vec<(Expr, Expr)>, values: Vec<Expr>) -> Stmt {
    debug_assert_eq!(
        cells.len(),
        values.len(),
        "tuple counts match (parser-enforced)"
    );
    debug_assert!(cells.len() >= 2, "single targets never ride the tuple path");
    let names: Vec<String> = (0..cells.len()).map(|i| format!("tuple$t{i}")).collect();
    // the temp names are deterministic (tuple$t{i}), so each store
    // remints its own value identifier — identical by construction
    let stores = cells
        .into_iter()
        .enumerate()
        .map(|(i, (obj, key))| Stmt::IndexAssign {
            obj,
            key,
            value: Expr::Identifier(format!("tuple$t{i}")),
            loc: at,
        });
    let mut body = vec![Stmt::LocalDecl {
        names,
        exprs: values,
        loc: at,
    }];
    body.extend(stores);
    Stmt::Do { body, loc: at }
}
