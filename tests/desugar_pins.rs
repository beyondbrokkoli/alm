//! L2 pins: the desugar latches, their attribution, and the sugars —
//! ported from mirror_experimental property_tests @ 87aca4c
//! (h5_for_desugar_reports_at_the_header_pin,
//! h5_for_desugar_inclusive_latch_pin,
//! h5_one_to_one_sugars_and_elseif_attribution_pin,
//! h8_tuple_assign_attribution_pin, h8_elaborator_unit_goldens_pin,
//! h8_tuple_name_target_goldens_pin).
//!
//! Delta: mirror's pins also call `analysis::build_context` on each
//! result (an L3 seam); that lands with the walk layer.

use alm::ast::{BinOp, CtorKey, Expr, Loc, NodeId, Stmt};
use alm::elaborate::{self, TupleTarget};
use alm::pipeline::front;
use alm::source::SourceFile;
use alm::surface::{Flag, Surface};

fn parse_parts(source: &str) -> Vec<Stmt> {
    parse_parts_with(source, false)
}

fn parse_parts_with(source: &str, for_limit_inclusive: bool) -> Vec<Stmt> {
    let mut surface = Surface::default();
    Flag::ForLimitInclusive(for_limit_inclusive).apply(&mut surface);
    let src = SourceFile::new("pin.lua", source);
    let out = front(&src, &surface);
    assert!(
        out.diagnostics.is_empty(),
        "pin source failed to parse: {:?}",
        out.diagnostics
    );
    out.ast
}

#[test]
fn h5_for_desugar_reports_at_the_header_pin() {
    let source = "local t = {}\nfor i = 0, 4 do\n    t[i] = i * 2\nend\nprint(t[2])\n";
    let ast = parse_parts(source);
    assert_eq!(ast.len(), 3);
    let Stmt::Do { body, .. } = &ast[1] else {
        panic!("the for-desugar rides a Do block");
    };
    let Stmt::While { body: wbody, .. } = &body[2] else {
        panic!("desugar shape: the block's third statement is the While");
    };
    let line_of = |s: &Stmt| Some(s.loc().line as usize);
    for (what, node) in [
        ("block Do", &ast[1] as &Stmt),
        ("counter decl", &body[0]),
        ("for$limit latch decl", &body[1]),
        ("While", &body[2]),
        ("body's inner Do", &wbody[0]),
        ("synthetic increment", &wbody[1]),
    ] {
        assert_eq!(
            line_of(node),
            Some(2),
            "the {what} must report the for header's line"
        );
    }
    let Stmt::Do { body: ubody, .. } = &wbody[0] else {
        panic!("desugar shape: the While body opens with the user's inner Do");
    };
    assert_eq!(
        line_of(&ubody[0]),
        Some(3),
        "the user body reports its own line, not the header's"
    );
    assert_eq!(line_of(&ast[0]), Some(1));
    assert_eq!(line_of(&ast[2]), Some(5));
}

#[test]
fn h5_for_desugar_inclusive_latch_pin() {
    // The inclusive surface's expansion golden: identical statement
    // shape, identical guards, identical stamps — only the latch
    // initializer reads `limit + 1`. The census arm needs no change;
    // this pin is the per-surface twin of
    // h5_for_desugar_reports_at_the_header_pin.
    let source = "for i = 0, 4 do\n    print(i)\nend\n";
    let ast = parse_parts_with(source, true);
    assert_eq!(ast.len(), 1);
    let Stmt::Do { body, .. } = &ast[0] else {
        panic!("the for-desugar rides a Do block");
    };
    // The shape is the exclusive desugar's shape, statement for statement.
    assert!(matches!(&body[0], Stmt::LocalDecl { names, .. } if names[0] == "i"));
    let Stmt::LocalDecl {
        names, exprs, loc, ..
    } = &body[1]
    else {
        panic!("the latch decl is a LocalDecl");
    };
    assert_eq!(names, &vec!["for$limit".to_string()]);
    // The one visible difference: the latch initializer is `limit + 1`
    // — the user limit on the left, the literal 1 on the right.
    assert_eq!(exprs.len(), 1);
    let Expr::BinaryOp {
        op: BinOp::Add,
        left,
        right,
        ..
    } = &exprs[0]
    else {
        panic!("the inclusive latch initializer is `limit + 1`");
    };
    assert!(matches!(left.as_ref(), Expr::Integer { value: 4, .. }));
    assert!(matches!(right.as_ref(), Expr::Integer { value: 1, .. }));
    assert_eq!(*loc, Loc { line: 1, col: 1 });
    let Stmt::While {
        condition,
        body: wbody,
        ..
    } = &body[2]
    else {
        panic!("the block's third statement is the While");
    };
    // The guard never changes: `i < for$limit` in both modes.
    assert!(matches!(
        condition,
        Expr::BinaryOp {
            op: BinOp::LessThan,
            ..
        }
    ));
    let line_of = |s: &Stmt| Some(s.loc().line as usize);
    for (what, node) in [
        ("block Do", &ast[0] as &Stmt),
        ("counter decl", &body[0]),
        ("for$limit latch decl", &body[1]),
        ("While", &body[2]),
        ("body's inner Do", &wbody[0]),
        ("synthetic increment", &wbody[1]),
    ] {
        assert_eq!(
            line_of(node),
            Some(1),
            "the {what} must report the for header's line"
        );
    }
}

#[test]
fn h5_one_to_one_sugars_and_elseif_attribution_pin() {
    let source = "\
function f(a)
    return a + 1
end
local function g(b)
    return b
end
t.cursor = 5
if a then
    print(1)
elseif b then
    print(2)
else
    print(3)
end
";
    let ast = parse_parts(source);
    let line_of = |s: &Stmt| Some(s.loc().line as usize);
    let Stmt::Assignment { expr, .. } = &ast[0] else {
        panic!("D4 desugars to an Assignment");
    };
    assert_eq!(line_of(&ast[0]), Some(1));
    let Expr::Function { body, .. } = expr else {
        panic!("D4's RHS is the fn literal");
    };
    assert_eq!(line_of(&body[0]), Some(2));
    let Stmt::LocalDecl { exprs, .. } = &ast[1] else {
        panic!("local-function desugars to a LocalDecl");
    };
    assert_eq!(line_of(&ast[1]), Some(4));
    let Expr::Function { body, .. } = &exprs[0] else {
        panic!("local-function's RHS is the fn literal");
    };
    assert_eq!(line_of(&body[0]), Some(5));
    assert!(matches!(&ast[2], Stmt::IndexAssign { .. }));
    assert_eq!(line_of(&ast[2]), Some(7));
    let Stmt::If {
        then_body,
        else_body,
        ..
    } = &ast[3]
    else {
        panic!("the source's fourth statement is the if");
    };
    assert_eq!(line_of(&ast[3]), Some(8));
    assert_eq!(line_of(&then_body[0]), Some(9));
    let Stmt::If {
        then_body: inner_then,
        else_body: inner_else,
        ..
    } = &else_body[0]
    else {
        panic!("the elseif desugars to a nested If");
    };
    assert_eq!(line_of(&else_body[0]), Some(10));
    assert_eq!(line_of(&inner_then[0]), Some(11));
    assert_eq!(line_of(&inner_else[0]), Some(13));
}

#[test]
fn h8_tuple_assign_attribution_pin() {
    let source = "\
local o = {0, 0}
o[0], o[1] = o[1], o[0]
print(o[0], o[1])
";
    let ast = parse_parts(source);
    assert_eq!(ast.len(), 3);
    let Stmt::Do { body, .. } = &ast[1] else {
        panic!("the tuple sugar rides a Do block");
    };
    assert_eq!(body.len(), 3);
    let line_of = |s: &Stmt| Some(s.loc().line as usize);
    for (what, node) in [
        ("block Do", &ast[1] as &Stmt),
        ("temp decl", &body[0]),
        ("cell store 0", &body[1]),
        ("cell store 1", &body[2]),
    ] {
        assert_eq!(
            line_of(node),
            Some(2),
            "the {what} reports at the statement's line"
        );
    }
    assert_eq!(line_of(&ast[0]), Some(1));
    assert_eq!(line_of(&ast[2]), Some(3));
}

#[test]
fn h8_elaborator_unit_goldens_pin() {
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
        false,
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
    let Stmt::Do { body: ubody, .. } = &wbody[0] else {
        panic!("the While body opens with the user's inner Do");
    };
    assert_eq!(ubody[0].loc().line, 8);

    let cells = vec![
        elaborate::TupleTarget::Cell {
            obj: Expr::Identifier {
                name: "o".into(),
                id: NodeId::mint(),
            },
            key: Expr::Integer {
                value: 0,
                id: NodeId::mint(),
            },
        },
        elaborate::TupleTarget::Cell {
            obj: Expr::Identifier {
                name: "o".into(),
                id: NodeId::mint(),
            },
            key: Expr::Integer {
                value: 1,
                id: NodeId::mint(),
            },
        },
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
    // Literal keys and name objs stay inline, so the decl is the plain
    // two-temp latch; only the store order turns over.
    for (j, stmt) in body[1..].iter().enumerate() {
        let i = 1 - j; // the stores run right-to-left: target 1, then 0
        let Stmt::IndexAssign {
            obj, key, value, ..
        } = stmt
        else {
            panic!("tuple statement {j} is the cell store");
        };
        assert!(matches!(obj, Expr::Identifier { name: n, .. } if n == "o"));
        assert!(matches!(key, Expr::Integer { value: k, .. } if *k == i as i64));
        assert!(
            matches!(value, Expr::Identifier { name: v, .. } if v == &format!("tuple$t{i}")),
            "store {j} reads target {i}'s temp"
        );
        assert_eq!(
            stmt.loc(),
            at,
            "the tuple family's store {j} carries the header's stamp"
        );
    }
    assert_eq!(body[0].loc(), at);
    assert_eq!(tuple_stmt.loc(), at);

    // The dependent-key shape: target 0's key reads a cell, so it
    // latches into tuple$k0 ahead of the value temps.
    let cells = vec![
        elaborate::TupleTarget::Cell {
            obj: Expr::Identifier {
                name: "o".into(),
                id: NodeId::mint(),
            },
            key: Expr::Index {
                obj: Box::new(Expr::Identifier {
                    name: "o".into(),
                    id: NodeId::mint(),
                }),
                key: Box::new(Expr::Integer {
                    value: 0,
                    id: NodeId::mint(),
                }),
                id: NodeId::mint(),
            },
        },
        elaborate::TupleTarget::Cell {
            obj: Expr::Identifier {
                name: "o".into(),
                id: NodeId::mint(),
            },
            key: Expr::Integer {
                value: 1,
                id: NodeId::mint(),
            },
        },
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
    assert_eq!(
        names,
        &vec![
            "tuple$k0".to_string(),
            "tuple$t0".to_string(),
            "tuple$t1".to_string()
        ]
    );
    assert!(matches!(
        &exprs[0],
        Expr::Index { obj, key, .. }
            if matches!(obj.as_ref(), Expr::Identifier { name, .. } if name == "o")
                && matches!(key.as_ref(), Expr::Integer { value: 0, .. })
    ));
    // Target 1's store (literal key, inline) lands first; target 0's
    // store reads the latched key.
    let Stmt::IndexAssign {
        obj, key, value, ..
    } = &body[1]
    else {
        panic!("tuple statement 0 is the cell store");
    };
    assert!(matches!(obj, Expr::Identifier { name: n, .. } if n == "o"));
    assert!(matches!(key, Expr::Integer { value: 1, .. }));
    assert!(matches!(value, Expr::Identifier { name: v, .. } if v == "tuple$t1"));
    let Stmt::IndexAssign {
        obj, key, value, ..
    } = &body[2]
    else {
        panic!("tuple statement 1 is the cell store");
    };
    assert!(matches!(obj, Expr::Identifier { name: n, .. } if n == "o"));
    assert!(matches!(key, Expr::Identifier { name: k, .. } if k == "tuple$k0"));
    assert!(matches!(value, Expr::Identifier { name: v, .. } if v == "tuple$t0"));
    for (what, node) in [
        ("block Do", &tuple_stmt as &Stmt),
        ("temp decl", (&body[0] as &Stmt)),
        ("cell store 0", &body[1]),
        ("cell store 1", &body[2]),
    ] {
        assert_eq!(
            node.loc(),
            at,
            "the tuple family's {what} carries the header's stamp"
        );
    }
}

#[test]
fn h8_tuple_name_target_goldens_pin() {
    let at = Loc { line: 7, col: 3 };
    let ident = |name: &str| Expr::Identifier {
        name: name.into(),
        id: NodeId::mint(),
    };
    let int = |value: i64| Expr::Integer {
        value,
        id: NodeId::mint(),
    };
    let cell = |obj: Expr, key: Expr| TupleTarget::Cell { obj, key };
    let name = |n: &str| TupleTarget::Name(n.into());
    let is_ident =
        |e: &Expr, want: &str| matches!(e, Expr::Identifier { name, .. } if name == want);
    let open = |stmt: &Stmt| -> (Vec<String>, Vec<Stmt>) {
        let Stmt::Do { body, .. } = stmt else {
            panic!("the tuple desugar rides a Do block");
        };
        let Stmt::LocalDecl { names, .. } = &body[0] else {
            panic!("the tuple family opens with the temp decl");
        };
        for node in body.iter().chain(std::iter::once(stmt)) {
            assert_eq!(node.loc(), at, "every node carries the header's stamp");
        }
        (names.clone(), body[1..].to_vec())
    };
    let temps = |ns: &[&str]| ns.iter().map(|n| n.to_string()).collect::<Vec<_>>();

    // x, y = y, x — names own no prefix: the decl is the value tail
    // alone, and the rebinds land right-to-left.
    let swap = elaborate::desugar_tuple_assign(
        at,
        vec![name("x"), name("y")],
        vec![ident("y"), ident("x")],
    );
    let (names, stores) = open(&swap);
    assert_eq!(names, temps(&["tuple$t0", "tuple$t1"]));
    assert!(matches!(
        &stores[0],
        Stmt::Assignment { name, expr, .. } if name == "y" && is_ident(expr, "tuple$t1")
    ));
    assert!(matches!(
        &stores[1],
        Stmt::Assignment { name, expr, .. } if name == "x" && is_ident(expr, "tuple$t0")
    ));

    // b[j], j = 20, j + 1 — the name store lands before the cell
    // store, so the key latches the old j (the judge prints 4 20 0).
    let capture = elaborate::desugar_tuple_assign(
        at,
        vec![cell(ident("b"), ident("j")), name("j")],
        vec![
            int(20),
            Expr::BinaryOp {
                op: BinOp::Add,
                left: Box::new(ident("j")),
                right: Box::new(int(1)),
                id: NodeId::mint(),
            },
        ],
    );
    let (names, stores) = open(&capture);
    assert_eq!(names, temps(&["tuple$k0", "tuple$t0", "tuple$t1"]));
    assert!(matches!(
        &stores[0],
        Stmt::Assignment { name, expr, .. } if name == "j" && is_ident(expr, "tuple$t1")
    ));
    assert!(matches!(
        &stores[1],
        Stmt::IndexAssign { obj, key, value, .. }
            if is_ident(obj, "b") && is_ident(key, "tuple$k0") && is_ident(value, "tuple$t0")
    ));

    // i, a[i] = i + 1, 20 — the mirror: the cell store lands first,
    // the name rebinds after it, and the key stays inline.
    let classic = elaborate::desugar_tuple_assign(
        at,
        vec![name("i"), cell(ident("a"), ident("i"))],
        vec![
            Expr::BinaryOp {
                op: BinOp::Add,
                left: Box::new(ident("i")),
                right: Box::new(int(1)),
                id: NodeId::mint(),
            },
            int(20),
        ],
    );
    let (names, stores) = open(&classic);
    assert_eq!(names, temps(&["tuple$t0", "tuple$t1"]));
    assert!(matches!(
        &stores[0],
        Stmt::IndexAssign { obj, key, value, .. }
            if is_ident(obj, "a") && is_ident(key, "i") && is_ident(value, "tuple$t1")
    ));
    assert!(matches!(
        &stores[1],
        Stmt::Assignment { name, expr, .. } if name == "i" && is_ident(expr, "tuple$t0")
    ));

    // t[0], t = 5, u — the obj itself rebinds first, so it latches:
    // the store rides the old table (the judge prints u's own cells).
    let displace = elaborate::desugar_tuple_assign(
        at,
        vec![cell(ident("t"), int(0)), name("t")],
        vec![int(5), ident("u")],
    );
    let (names, stores) = open(&displace);
    assert_eq!(names, temps(&["tuple$o0", "tuple$t0", "tuple$t1"]));
    assert!(matches!(
        &stores[0],
        Stmt::Assignment { name, expr, .. } if name == "t" && is_ident(expr, "tuple$t1")
    ));
    assert!(matches!(
        &stores[1],
        Stmt::IndexAssign { obj, key, value, .. }
            if is_ident(obj, "tuple$o0")
                && matches!(key, Expr::Integer { value: 0, .. })
                && is_ident(value, "tuple$t0")
    ));

    // o[0], ({7})[0] = 5, 6 — a ctor prefix mints a table and runs its
    // entries inside the judge's pre-store window, so it latches.
    // (P8 note: the {7} entry is positional — the field says so.)
    let ctor = elaborate::desugar_tuple_assign(
        at,
        vec![
            cell(ident("o"), int(0)),
            cell(
                Expr::TableCtor {
                    entries: vec![(
                        CtorKey::Const {
                            slot: 0,
                            positional: true,
                        },
                        int(7),
                    )],
                    line: 7,
                    id: NodeId::mint(),
                },
                int(0),
            ),
        ],
        vec![int(5), int(6)],
    );
    let (names, stores) = open(&ctor);
    assert_eq!(names, temps(&["tuple$o1", "tuple$t0", "tuple$t1"]));
    assert!(matches!(
        &stores[0],
        Stmt::IndexAssign { obj, value, .. }
            if is_ident(obj, "tuple$o1") && is_ident(value, "tuple$t1")
    ));
    assert!(matches!(
        &stores[1],
        Stmt::IndexAssign { obj, value, .. } if is_ident(obj, "o") && is_ident(value, "tuple$t0")
    ));
}
