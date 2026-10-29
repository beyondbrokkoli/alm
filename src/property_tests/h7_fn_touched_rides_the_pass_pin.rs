
/// The fn-touched scan's law, golden: a fn body's TOUCHED names are
/// the ones it assigns or stores through that no scope at or below
/// its entry depth declares; locals it declares itself are not
/// touched; a nested fn's touches propagate to the parent's set.
/// The scan rode the old five-walk layout as a standalone walk; it
/// is the one pass's scan half now (H7) and these are its values.
#[test]
fn h7_fn_touched_rides_the_pass_pin() {
    let source = "\
local outer = 1
local t = {}
local g = function()
    outer = outer + 1
    local inner = 2
    t[0] = inner
    local h = function()
        outer = outer + 2
    end
end
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let Stmt::LocalDecl { exprs: g_exprs, .. } = &ast[2] else {
        panic!("the third statement declares g");
    };
    let Expr::Function { body: g_body, .. } = &g_exprs[0] else {
        panic!("g's initializer is the fn literal");
    };
    let Stmt::LocalDecl { exprs: h_exprs, .. } = &g_body[3] else {
        panic!("g's fourth body statement declares h");
    };
    let Expr::Function { .. } = &h_exprs[0] else {
        panic!("h's initializer is the nested fn literal");
    };
    let want = ["outer", "t"];
    let touched = ctx
        .fn_touched
        .get(&(g_exprs[0].id()))
        .expect("the pass records the fn literal's touched set");
    assert_eq!(
        touched.iter().map(|s| s.as_str()).collect::<Vec<_>>(),
        want,
        "g touches outer (assigned) and t (stored through) — its own local inner is not touched"
    );
    let h_touched = ctx
        .fn_touched
        .get(&(h_exprs[0].id()))
        .expect("nested fns get their own entry");
    assert_eq!(
        h_touched.iter().map(|s| s.as_str()).collect::<Vec<_>>(),
        vec!["outer"],
        "h touches outer across two fn boundaries"
    );
    // the scope discipline: a fn declared INSIDE g sees g's locals —
    // storing through a name g declares locally is not a touch. h
    // stores nothing such; g's own `inner` store proves the negative.
    assert!(!touched.contains("inner"));
}
