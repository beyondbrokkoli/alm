//! The pre-analyzer census pins (mirror's h6/h5/h7 property pins,
//! adapted): the identity census trips on a cloned subtree, the
//! desugar attribution censuses trip on drift, and `fn_touched` rides
//! the pass across two fn boundaries.

mod common;

use alm::analysis;
use alm::ast::{BinOp, Expr, Loc, NodeId, Stmt};

#[test]
#[should_panic(expected = "identity census")]
fn h6_id_census_pin() {
    let at = Loc { line: 1, col: 1 };
    let orig = Stmt::Break {
        loc: at,
        id: NodeId::mint(),
    };
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

#[test]
#[should_panic(expected = "attribution drift")]
fn h5_census_trips_on_right_count_wrong_line() {
    let at = |line: u32| Loc { line, col: 1 };
    let ast = vec![Stmt::Do {
        body: vec![
            Stmt::LocalDecl {
                names: vec!["i".into()],
                exprs: vec![Expr::Integer {
                    value: 0,
                    id: NodeId::mint(),
                }],
                loc: at(2),
                id: NodeId::mint(),
            },
            Stmt::LocalDecl {
                names: vec!["for$limit".into()],
                exprs: vec![Expr::Integer {
                    value: 4,
                    id: NodeId::mint(),
                }],
                loc: at(2),
                id: NodeId::mint(),
            },
            Stmt::While {
                condition: Expr::BinaryOp {
                    op: BinOp::LessThan,
                    left: Box::new(Expr::Identifier {
                        name: "i".into(),
                        id: NodeId::mint(),
                    }),
                    right: Box::new(Expr::Identifier {
                        name: "for$limit".into(),
                        id: NodeId::mint(),
                    }),
                    id: NodeId::mint(),
                },
                body: vec![
                    Stmt::Do {
                        body: vec![Stmt::Print {
                            exprs: vec![Expr::Identifier {
                                name: "i".into(),
                                id: NodeId::mint(),
                            }],
                            loc: at(4),
                            id: NodeId::mint(),
                        }],
                        loc: at(4),
                        id: NodeId::mint(),
                    },
                    Stmt::Assignment {
                        name: "i".into(),
                        expr: Expr::BinaryOp {
                            op: BinOp::Add,
                            left: Box::new(Expr::Identifier {
                                name: "i".into(),
                                id: NodeId::mint(),
                            }),
                            right: Box::new(Expr::Integer {
                                value: 1,
                                id: NodeId::mint(),
                            }),
                            id: NodeId::mint(),
                        },
                        // drift: the synthetic increment reports a line
                        // the header never saw
                        loc: at(5),
                        id: NodeId::mint(),
                    },
                ],
                loc: at(3),
                id: NodeId::mint(),
            },
        ],
        loc: at(2),
        id: NodeId::mint(),
    }];
    analysis::build_context(&ast);
}

#[test]
fn h7_fn_touched_rides_the_pass_pin() {
    let source = "\
local outer = 1
local t = {}
local g = function()
    outer = outer + 1
    local inner = 2
    t[0] = inner
    local h = function()
        outer = outer + 2
    end
end
";
    let ast = common::parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let Stmt::LocalDecl { exprs: g_exprs, .. } = &ast[2] else {
        panic!("the third statement declares g");
    };
    let Expr::Function { body: g_body, .. } = &g_exprs[0] else {
        panic!("g's initializer is the fn literal");
    };
    let Stmt::LocalDecl { exprs: h_exprs, .. } = &g_body[3] else {
        panic!("g's fourth body statement declares h");
    };
    let Expr::Function { .. } = &h_exprs[0] else {
        panic!("h's initializer is the nested fn literal");
    };
    let want = ["outer", "t"];
    let touched = ctx
        .fn_touched
        .get(&(g_exprs[0].id()))
        .expect("the pass records the fn literal's touched set");
    assert_eq!(
        touched.iter().map(|s| s.as_str()).collect::<Vec<_>>(),
        want,
        "g touches outer (assigned) and t (stored through) — its own local inner is not touched"
    );
    let h_touched = ctx
        .fn_touched
        .get(&(h_exprs[0].id()))
        .expect("nested fns get their own entry");
    assert_eq!(
        h_touched.iter().map(|s| s.as_str()).collect::<Vec<_>>(),
        vec!["outer"],
        "h touches outer across two fn boundaries"
    );
    assert!(!touched.contains("inner"));
}
