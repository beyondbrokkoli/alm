
/// The census's Field face: the H5 tripwire's for family, hidden one
/// face deeper — inside a fn literal under a Field obj. The one pass
/// stamps the family through Field (H7); the census must SEE it
/// there: recursing the pass's faces is the law that keeps the
/// census the every-compile omniscience check, and this pin holds it
/// (drop the census's Field arm and the fingerprint walks past
/// unchecked — this stops compiling).
#[test]
#[should_panic(expected = "attribution drift")]
fn h7_census_sees_through_field_pin() {
    let at = |line: u32| crate::ast::Loc { line, col: 1 };
    let family = vec![
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
    ];
    let ast = vec![Stmt::Expr {
        expr: Expr::Field {
            obj: Box::new(Expr::Function {
                params: vec![],
                body: vec![Stmt::Do {
                    body: family,
                    loc: at(2),
                    id: NodeId::mint(),
                }],
                id: NodeId::mint(),
            }),
            name: "x".into(),
            id: NodeId::mint(),
        },
        loc: at(1),
        id: NodeId::mint(),
    }];
    analysis::build_context(&ast);
}
