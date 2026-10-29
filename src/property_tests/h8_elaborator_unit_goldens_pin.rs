
// ---- H8: the elaboration boundary — unit goldens, by locality ----
//
// The multi-statement desugars are PURE functions (elaborate.rs);
// these goldens pin their output shape and stamps DIRECTLY, without
// parsing — the census (analysis.rs, every compile) stays the
// whole-tree omniscience check on top.

/// The elaborators' shapes, unit-level: the for family's six
/// statements and the tuple family's temp-decl + stores all carry the
/// header's stamp, and the wiring (guard against for$limit, store i
/// reads tuple$t{i}) is exactly the census's fingerprint.
#[test]
fn h8_elaborator_unit_goldens_pin() {
    use crate::ast::Loc;
    use crate::elaborate;
    let at = Loc { line: 7, col: 3 };

    let for_stmt = elaborate::desugar_numeric_for(
        at,
        "i".into(),
        Expr::Integer {
            value: 0,
            id: NodeId::mint(),
        },
        Expr::Integer {
            value: 4,
            id: NodeId::mint(),
        },
        vec![Stmt::Expr {
            expr: Expr::Integer {
                value: 1,
                id: NodeId::mint(),
            },
            loc: Loc { line: 8, col: 1 },
            id: NodeId::mint(),
        }],
    );
    let Stmt::Do { body, .. } = &for_stmt else {
        panic!("the numeric-for desugar rides a Do block");
    };
    assert_eq!(body.len(), 3);
    let Stmt::While {
        condition,
        body: wbody,
        ..
    } = &body[2]
    else {
        panic!("the for family's third statement is the While");
    };
    assert!(matches!(
        condition,
        Expr::BinaryOp {
            op: BinOp::LessThan,
            ..
        }
    ));
    assert_eq!(wbody.len(), 2);
    for (what, node) in [
        ("block Do", &for_stmt),
        ("counter decl", (&body[0] as &Stmt)),
        ("latch decl", &body[1]),
        ("While", &body[2]),
        ("inner Do", &wbody[0]),
        ("increment", &wbody[1]),
    ] {
        assert_eq!(
            node.loc(),
            at,
            "the for family's {what} carries the header's stamp"
        );
    }
    // the user body rides its own stamp
    let Stmt::Do { body: ubody, .. } = &wbody[0] else {
        panic!("the While body opens with the user's inner Do");
    };
    assert_eq!(ubody[0].loc().line, 8);

    let cells = vec![
        (
            Expr::Identifier {
                name: "o".into(),
                id: NodeId::mint(),
            },
            Expr::Integer {
                value: 0,
                id: NodeId::mint(),
            },
        ),
        (
            Expr::Identifier {
                name: "o".into(),
                id: NodeId::mint(),
            },
            Expr::Integer {
                value: 1,
                id: NodeId::mint(),
            },
        ),
    ];
    let values = vec![
        Expr::Integer {
            value: 5,
            id: NodeId::mint(),
        },
        Expr::Integer {
            value: 6,
            id: NodeId::mint(),
        },
    ];
    let tuple_stmt = elaborate::desugar_tuple_assign(at, cells, values);
    let Stmt::Do { body, .. } = &tuple_stmt else {
        panic!("the tuple desugar rides a Do block");
    };
    assert_eq!(body.len(), 3);
    let Stmt::LocalDecl { names, exprs, .. } = &body[0] else {
        panic!("the tuple family opens with the temp decl");
    };
    assert_eq!(names, &vec!["tuple$t0".to_string(), "tuple$t1".to_string()]);
    assert_eq!(exprs.len(), 2);
    for (i, stmt) in body[1..].iter().enumerate() {
        let Stmt::IndexAssign {
            obj, key, value, ..
        } = stmt
        else {
            panic!("tuple statement {} is the cell store", i);
        };
        assert!(matches!(obj, Expr::Identifier { name: n, .. } if n == "o"));
        assert!(matches!(key, Expr::Integer { value: k, .. } if *k == i as i64));
        assert!(
            matches!(value, Expr::Identifier { name: v, .. } if v == &format!("tuple$t{i}")),
            "store {i} reads temp {i}"
        );
        assert_eq!(
            stmt.loc(),
            at,
            "the tuple family's store {i} carries the header's stamp"
        );
    }
    assert_eq!(body[0].loc(), at);
    assert_eq!(tuple_stmt.loc(), at);
}
