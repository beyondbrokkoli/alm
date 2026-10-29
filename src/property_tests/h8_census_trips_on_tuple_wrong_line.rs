
/// The tuple family's misattribution tripwire: a hand-built block
/// with the unforgeable fingerprint and ONE wrong store stamp — the
/// drift class only a hand-stamping desugar can produce, and the
/// census's tuple arm must cry wolf by name.
#[test]
#[should_panic(expected = "tuple-assign attribution drift")]
fn h8_census_trips_on_tuple_wrong_line() {
    use crate::ast::Loc;
    let at = |line: u32| Loc { line, col: 1 };
    let store = |i: usize, line: u32| Stmt::IndexAssign {
        obj: Expr::Identifier {
            name: "o".into(),
            id: NodeId::mint(),
        },
        key: Expr::Integer {
            value: i as i64,
            id: NodeId::mint(),
        },
        value: Expr::Identifier {
            name: format!("tuple$t{i}"),
            id: NodeId::mint(),
        },
        loc: at(line),
        id: NodeId::mint(),
    };
    let ast = vec![Stmt::Do {
        body: vec![
            Stmt::LocalDecl {
                names: vec!["tuple$t0".into(), "tuple$t1".into()],
                exprs: vec![
                    Expr::Integer {
                        value: 1,
                        id: NodeId::mint(),
                    },
                    Expr::Integer {
                        value: 2,
                        id: NodeId::mint(),
                    },
                ],
                loc: at(2),
                id: NodeId::mint(),
            },
            store(0, 2),
            store(1, 9),
        ],
        loc: at(2),
        id: NodeId::mint(),
    }];
    analysis::build_context(&ast);
}
