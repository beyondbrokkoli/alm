
/// The 1:1 sugars (D4 `function f`, `local function`, dot-assign) and
/// the elseif chain attribute one entry per emitted statement at the
/// statement's own leading token — the golden register for every
/// non-fabricating desugar.
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
    let _ctx = analysis::build_context(&ast);
    let line_of = |s: &Stmt| Some(s.loc().line as usize);
    // D4: `function f(a) … end` is ONE Assignment at line 1; its body's
    // return reports the body's own line 2
    let Stmt::Assignment { expr, .. } = &ast[0] else {
        panic!("D4 desugars to an Assignment");
    };
    assert_eq!(line_of(&ast[0]), Some(1));
    let Expr::Function { body, .. } = expr else {
        panic!("D4's RHS is the fn literal");
    };
    assert_eq!(line_of(&body[0]), Some(2));
    // `local function g(b)` is ONE LocalDecl at line 4, body at 5
    let Stmt::LocalDecl { exprs, .. } = &ast[1] else {
        panic!("local-function desugars to a LocalDecl");
    };
    assert_eq!(line_of(&ast[1]), Some(4));
    let Expr::Function { body, .. } = &exprs[0] else {
        panic!("local-function's RHS is the fn literal");
    };
    assert_eq!(line_of(&body[0]), Some(5));
    // dot-assign is ONE IndexAssign at line 7
    assert!(matches!(&ast[2], Stmt::IndexAssign { .. }));
    assert_eq!(line_of(&ast[2]), Some(7));
    // the if at 8, its then-arm print at 9, the elseif's nested If at
    // 10, its print at 11, the else print at 13
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
