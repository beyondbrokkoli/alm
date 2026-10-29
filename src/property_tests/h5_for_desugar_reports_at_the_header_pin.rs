
/// R7's law as a golden register: the for-desugar's six statements
/// (block Do, counter decl, for$limit latch decl, While, inner Do,
/// synthetic increment) ALL report the header's line; the user body and
/// every non-desugar statement report their own.
#[test]
fn h5_for_desugar_reports_at_the_header_pin() {
    let source = "local t = {}\nfor i = 0, 4 do\n    t[i] = i * 2\nend\nprint(t[2])\n";
    let ast = parse_parts(source);
    let _ctx = analysis::build_context(&ast);
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
