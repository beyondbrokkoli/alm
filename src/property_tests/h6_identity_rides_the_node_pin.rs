
// ---- H6: identity rides the node ----
//
// The checker→lowerer contract keyed raw `*const Expr`/`*const Stmt`
// addresses — an immutability convention ("the AST never moves") with
// no enforcing type, plus `unsafe` derefs in `FnDef::body` and the
// `stmt_lines`/`stmt_locs` lookup maps. The fold: `NodeId(u32)`
// minted at construction rides every node, every fact map keys the
// id, the FnDef OWNS its body, and the derivation pass censuses id
// uniqueness over the whole tree. These three pins hold that law.

/// H6 pin 1 — identity is the mint, and the facts outlive the tree.
/// Ids are born at construction (same-line statements distinguish;
/// a re-parse re-mints), and because the FnDef owns its body while
/// every map keys ids, the finished facts are SELF-CONTAINED: the AST
/// and its context may die, and the recorded decisions stay readable.
/// Pre-H6 the body read after such a drop was a use-after-free riding
/// the immutability convention — the exact disease the fold deletes.
#[test]
fn h6_identity_rides_the_node_pin() {
    // construction mints: two statements on ONE line carry distinct
    // ids (no line-derived key could ever give them that), and two
    // parses of the same source mint disjoint ids (not positional).
    let ast = parse_parts("local a = 1 local b = 2");
    assert_ne!(
        ast[0].id(),
        ast[1].id(),
        "same-line statements carry distinct ids — identity is the mint, not the line"
    );
    let again = parse_parts("local a = 1 local b = 2");
    assert_ne!(
        ast[0].id(),
        again[0].id(),
        "a re-parse re-mints — ids are not positional"
    );

    // the facts outlive the tree: analyze a fn program, remember the
    // fn literal's id and its ctor's id, drop BOTH the context and
    // the AST, then read the fn's owned body and the ctor's site off
    // the facts alone.
    let source = "\
local f = function(n)
    local acc = { 1 }
    return acc
end
local r = f(2)
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "H6 pin source must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );
    let Stmt::LocalDecl { exprs: f_exprs, .. } = &ast[0] else {
        panic!("the first statement declares f");
    };
    let Expr::Function { body: f_body, .. } = &f_exprs[0] else {
        panic!("f's initializer is the fn literal");
    };
    let fn_id = f_exprs[0].id();
    let Stmt::LocalDecl {
        exprs: acc_exprs, ..
    } = &f_body[0]
    else {
        panic!("the fn's first body statement declares acc");
    };
    let Expr::TableCtor {
        line: ctor_line, ..
    } = &acc_exprs[0]
    else {
        panic!("acc's initializer is a ctor");
    };
    let ctor_id = acc_exprs[0].id();
    let ctor_line = *ctor_line as usize;

    drop(ctx);
    drop(ast);

    let def = shape
        .fn_defs
        .get(&fn_id)
        .expect("fn_defs keys the fn literal's own id — readable with the tree gone");
    assert_eq!(
        def.body()[0].loc().line as usize,
        2,
        "the owned body carries the fn's own statements with the tree gone"
    );
    let site = shape
        .sites
        .get(&ctor_id)
        .expect("sites keys the ctor's own id — readable with the tree gone")
        .to_owned();
    assert_eq!(
        shape.ctor_lines[site], ctor_line,
        "the pairing law holds off the facts alone: ctor_lines[site] is the ctor's own line"
    );
}
