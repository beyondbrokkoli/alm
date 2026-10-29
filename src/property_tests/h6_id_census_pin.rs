
/// H6 pin 2 — the identity census: a cloned node reaching the tree
/// panics analysis by name. A copy of a node IS the node (the id
/// copies with it), so re-materializing a subtree means CONSTRUCTING
/// it; the census keeps that law loud at analysis time instead of
/// letting two "different" statements silently share one fact entry.
#[test]
#[should_panic(expected = "identity census")]
fn h6_id_census_pin() {
    use crate::ast::Loc;
    let at = Loc { line: 1, col: 1 };
    let orig = Stmt::Break {
        loc: at,
        id: NodeId::mint(),
    };
    // the tree carries `orig` TWICE — once as the copy, once as the
    // moved original — so one constructed id reaches it two nodes
    let ast = vec![
        Stmt::Break {
            loc: at,
            id: NodeId::mint(),
        },
        orig.clone(),
        orig,
    ];
    analysis::build_context(&ast);
}
