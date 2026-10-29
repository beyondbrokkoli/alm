
/// The shipped path: the tuple sugar parses into the elaborated
/// shape and the whole family reports at the statement's line (the
/// census ran green over it inside build_context).
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
    let _ctx = analysis::build_context(&ast);
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
