
/// The misattribution direction: a desugar-shaped block whose stamps
/// are count-exact but line-wrong (the increment reports 9 while the
/// header family reports 2). Counts are structural since session 4,
/// so only a wrong stamp can drift — and the census must cry wolf.
/// This is the drift class only a hand-stamping desugar can produce —
/// hand-built here because a correct parser cannot.
#[test]
#[should_panic(expected = "attribution drift")]
fn h5_census_trips_on_right_count_wrong_line() {
    let at = |line: u32| crate::ast::Loc { line, col: 1 };
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
                        body: vec![],
                        loc: at(2),
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
                        loc: at(9),
                        id: NodeId::mint(),
                    },
                ],
                loc: at(2),
                id: NodeId::mint(),
            },
        ],
        loc: at(2),
        id: NodeId::mint(),
    }];
    analysis::build_context(&ast);
}
