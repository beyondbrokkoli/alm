
#[cfg(test)]
mod break_gate_tests {
    use crate::ast::has_break;
    use crate::ast::{Expr, Loc, NodeId, Stmt};

    fn at() -> Loc {
        Loc { line: 1, col: 1 }
    }

    fn assign_i() -> Stmt {
        Stmt::Assignment {
            name: "i".to_string(),
            expr: Expr::Integer {
                value: 1,
                id: NodeId::mint(),
            },
            loc: at(),
            id: NodeId::mint(),
        }
    }

    #[test]
    fn flat_break_is_this_loops() {
        assert!(has_break(&[Stmt::Break {
            loc: at(),
            id: NodeId::mint()
        }]));
        assert!(!has_break(&[assign_i()]));
    }

    #[test]
    fn break_through_do_and_if_counts() {
        let cond = Expr::Boolean {
            value: true,
            id: NodeId::mint(),
        };
        let brk = vec![Stmt::Break {
            loc: at(),
            id: NodeId::mint(),
        }];
        assert!(has_break(&[Stmt::Do {
            body: brk.clone(),
            loc: at(),
            id: NodeId::mint()
        }]));
        assert!(has_break(&[Stmt::If {
            condition: cond.clone(),
            then_body: brk.clone(),
            else_body: vec![],
            loc: at(),
            id: NodeId::mint()
        }]));
        assert!(has_break(&[Stmt::If {
            condition: cond,
            then_body: vec![],
            else_body: brk,
            loc: at(),
            id: NodeId::mint()
        }]));
    }

    #[test]
    fn break_inside_nested_while_binds_to_the_inner_loop() {
        let nested = vec![Stmt::While {
            condition: Expr::Boolean {
                value: true,
                id: NodeId::mint(),
            },
            body: vec![Stmt::Break {
                loc: at(),
                id: NodeId::mint(),
            }],
            loc: at(),
            id: NodeId::mint(),
        }];
        assert!(!has_break(&nested));
    }

    #[test]
    fn break_inside_a_function_body_is_not_this_loops() {
        // R8's AST half: has_break does not recurse into Expr::Function —
        // a body's break binds to a loop written in THAT body, never to
        // the loop enclosing the definition. The walk's cross-boundary
        // gate and the lowerer's BreakCtx base guard this same law.
        let fn_with_break = Stmt::LocalDecl {
            names: vec!["f".to_string()],
            exprs: vec![Expr::Function {
                params: vec![],
                body: vec![Stmt::Break {
                    loc: at(),
                    id: NodeId::mint(),
                }],
                id: NodeId::mint(),
            }],
            loc: at(),
            id: NodeId::mint(),
        };
        assert!(!has_break(&[fn_with_break]));

        let fn_with_own_loop = Stmt::LocalDecl {
            names: vec!["f".to_string()],
            exprs: vec![Expr::Function {
                params: vec![],
                body: vec![Stmt::While {
                    condition: Expr::Boolean {
                        value: true,
                        id: NodeId::mint(),
                    },
                    body: vec![Stmt::Break {
                        loc: at(),
                        id: NodeId::mint(),
                    }],
                    loc: at(),
                    id: NodeId::mint(),
                }],
                id: NodeId::mint(),
            }],
            loc: at(),
            id: NodeId::mint(),
        };
        assert!(!has_break(&[fn_with_own_loop]));
    }
}
