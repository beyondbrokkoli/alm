
/// H6 pin 3 — the fact maps key the node's OWN id: the pairing law
/// (every ctor's id carries its site, and the site's ctor line is the
/// ctor's own `{` — H7's law, re-keyed), and the expansion pair law
/// (`call_defs` keys `(call, site)` id pairs; at the top level a call
/// IS its own site, and the map's VALUE is the callee literal's id).
#[test]
fn h6_maps_key_ids_not_addresses_pin() {
    let source = "\
local f = function(a)
    return a
end
local x = f(1)
local y = f(2)
local t = { 1, 2 }
local g = function()
    local z = { 3 }
    return z
end
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "H6 pin source must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );

    // the pairing law over EVERY ctor of the tree, keyed by id
    let mut ctor_count = 0;
    fn ctors_of_stmt(s: &Stmt, out: &mut Vec<(NodeId, u32)>) {
        fn ctors_of_expr(e: &Expr, out: &mut Vec<(NodeId, u32)>) {
            if let Expr::TableCtor { entries, line, .. } = e {
                out.push((e.id(), *line));
                for (k, v) in entries {
                    if let crate::ast::CtorKey::Expr(ke) = k {
                        ctors_of_expr(ke, out);
                    }
                    ctors_of_expr(v, out);
                }
            }
            match e {
                Expr::Index { obj, key, .. } => {
                    ctors_of_expr(obj, out);
                    ctors_of_expr(key, out);
                }
                Expr::BinaryOp { left, right, .. } => {
                    ctors_of_expr(left, out);
                    ctors_of_expr(right, out);
                }
                Expr::UnaryOp { expr, .. } => ctors_of_expr(expr, out),
                Expr::Call { callee, args, .. } => {
                    ctors_of_expr(callee, out);
                    args.iter().for_each(|a| ctors_of_expr(a, out));
                }
                Expr::Function { body, .. } => body.iter().for_each(|s| ctors_of_stmt(s, out)),
                _ => {}
            }
        }
        match s {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
                exprs.iter().for_each(|e| ctors_of_expr(e, out))
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr, .. } => ctors_of_expr(expr, out),
            Stmt::IndexAssign {
                obj, key, value, ..
            } => {
                ctors_of_expr(obj, out);
                ctors_of_expr(key, out);
                ctors_of_expr(value, out);
            }
            Stmt::While {
                condition, body, ..
            } => {
                ctors_of_expr(condition, out);
                body.iter().for_each(|s| ctors_of_stmt(s, out));
            }
            Stmt::Do { body, .. } => body.iter().for_each(|s| ctors_of_stmt(s, out)),
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                ctors_of_expr(condition, out);
                then_body
                    .iter()
                    .chain(else_body)
                    .for_each(|s| ctors_of_stmt(s, out));
            }
            Stmt::Return { value, .. } => {
                if let Some(e) = value {
                    ctors_of_expr(e, out)
                }
            }
            Stmt::Break { .. } => {}
        }
    }
    let mut ctors = Vec::new();
    ast.iter().for_each(|s| ctors_of_stmt(s, &mut ctors));
    for (id, line) in &ctors {
        let site = ctx
            .sites
            .get(id)
            .expect("the ctor's OWN id carries its site — the map keys ids, not addresses");
        assert_eq!(
            ctx.ctor_lines[*site], *line as usize,
            "ctor_lines[site] is the ctor's own line at every id"
        );
        ctor_count += 1;
    }
    assert_eq!(ctor_count, 2, "the pin's tree carries two ctors");

    // the expansion pair law: each top-level call IS its own site,
    // the value is the fn literal's id, and no cross key exists
    let Stmt::LocalDecl { exprs: f_exprs, .. } = &ast[0] else {
        panic!("the first statement declares f");
    };
    let fn_id = f_exprs[0].id();
    let call_of = |stmt: usize| match &ast[stmt] {
        Stmt::LocalDecl { exprs, .. } => &exprs[0],
        _ => panic!("the statement initializes from a call"),
    };
    let c1 = call_of(1).id();
    let c2 = call_of(2).id();
    assert_ne!(c1, c2, "two call nodes are two identities");
    for call in [c1, c2] {
        assert!(
            shape.call_defs.contains_key(&(call, call)),
            "a top-level call is its own expansion site — keyed by the node's id on both halves"
        );
        assert_eq!(
            shape.call_defs[&(call, call)],
            fn_id,
            "the map's value is the callee literal's id"
        );
    }
    assert!(
        !shape.call_defs.contains_key(&(c1, c2)),
        "a cross-site key is unrepresentable: one node, one site, its own id"
    );
}
