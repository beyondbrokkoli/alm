/// H12 7b-prep — the creation family's site law at depth TWO: a local
/// fn created and returned inside G's body (G inlined inside F's
/// extent, two top-level F calls) mints its creation env against the
/// OUTERMOST extent's call — F's record carries it, the immediate
/// enclosure (G's own record) stays empty by law, and ROOT carries
/// nothing (G's and F's calls are callee/statement positions — the
/// Escape Law's creation is the VALUE read's land). The two events are
/// two pairs over the shared value-read expr, one entry per site,
/// naming the same literal. 7b reads creation off the owner's record;
/// this pin holds the depth-two shape its read must reproduce.
#[test]
fn h12_creation_envs_site_law_at_depth_two_pin() {
    let source = "\
local function G()
    local function Inner(x) return x end
    return Inner
end
local function F()
    local q
    local f = G()
    return 0
end
F()
F()
print(0)
";
    let ll = compile(source).unwrap_or_else(|(stage, diags)| {
        panic!(
            "the depth-two creation program must lower clean at {}: {}",
            stage.name(),
            diags_text(&diags)
        )
    });
    assert!(
        ll.contains("@alm_print_int"),
        "the scalar print rides the boundary"
    );

    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "the creation pin must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );
    assert_eq!(
        shape.instances.len(),
        5,
        "ROOT + two F events + two G events — creations mint no instance"
    );

    // the value read and the literal it names, off the AST (H6: the
    // same ids ride the owned bodies)
    let g_body = match &ast[0] {
        Stmt::LocalDecl { exprs, .. } => match &exprs[0] {
            Expr::Function { body, .. } => body,
            _ => panic!("the local binds G's fn literal"),
        },
        _ => panic!("the statement declares G"),
    };
    let inner_lit = match &g_body[0] {
        Stmt::LocalDecl { exprs, .. } => exprs[0].id(),
        _ => panic!("G's body declares Inner"),
    };
    let inner_read = match &g_body[1] {
        Stmt::Return {
            value: Some(e), ..
        } => e.id(),
        _ => panic!("G's body returns the value read"),
    };

    let root = &shape.instances[&crate::shape::InstanceId::ROOT];
    assert_eq!(
        root.children.len(),
        2,
        "the two top-level F calls self-pair to ROOT"
    );
    assert!(
        root.creation_envs.is_empty(),
        "a callee read never mints — creation is the value read's land"
    );

    let mut saw_creation = 0;
    for set in root.children.values() {
        let f_inst = *set.iter().next().unwrap();
        let f_rec = &shape.instances[&f_inst];
        let f_call = f_rec.call.expect("F's record names its own call expr");
        assert_eq!(
            f_rec.children.len(),
            1,
            "F's extent minted G"
        );
        // THE LAW: the creation rides the OUTERMOST extent's record
        assert_eq!(
            f_rec.creation_envs.get(&inner_read),
            Some(&inner_lit),
            "the value read inside G's body mints against F's call — the \
             OUTERMOST extent, per site"
        );
        saw_creation += 1;
        // the immediate enclosure owns nothing
        let g_inst = *f_rec.children.values().next().unwrap().iter().next().unwrap();
        let g_rec = &shape.instances[&g_inst];
        assert!(
            g_rec.creation_envs.is_empty() && g_rec.children.is_empty(),
            "G's own record carries no shadow maps — the site law keys \
             against the OUTERMOST extent"
        );
        // the bridge names the pair's owner
        assert_eq!(
            shape.instance_of[&(inner_read, f_call)],
            f_inst,
            "the creation pair bridges to F's instance"
        );
    }
    assert_eq!(saw_creation, 2, "one creation entry per site");
}
