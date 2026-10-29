
/// H12 pin 2 — the shadow golden at depth two, over
/// fn_nested_site_keys's own shape: the instance view equals the pair
/// view where the pair-key law is sharpest — an access and a lane
/// derived inside an expansion inside an expansion, and a call-through
/// dispatch at depth two whose owner is the OUTERMOST instance (the
/// site law), never the immediate enclosure.
#[test]
fn h12_shadow_golden_depth_two_pin() {
    let source = "\
local t = {}
t[\"k0\"] = 7
local function Get(s) return t[s] end
local function Twice(s) return Get(s) + Get(s) end
print(Twice(\"k0\"))
local keys = { [0] = \"k0\", [1] = \"k0\" }
local function Sel(i) return t[keys[i]] end
local function Wrap(i) return Sel(i) * 2 end
print(Wrap(0))
print(Wrap(1))
local function Add1(x) return x + 1 end
local function Drive(f, n) return f(n) end
local function Outer(n) return Drive(Add1, n) end
print(Outer(5))
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "H12 pin source must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );

    let only_child = |owner: crate::shape::InstanceId, call: NodeId| {
        *shape.instances[&owner].children[&call]
            .iter()
            .next()
            .unwrap()
    };
    let print_call = |stmt: usize| match &ast[stmt] {
        Stmt::Print { exprs, .. } => exprs[0].id(),
        _ => panic!("the statement prints one call"),
    };
    let fn_lit = |stmt: usize| match &ast[stmt] {
        Stmt::LocalDecl { exprs, .. } => &exprs[0],
        _ => panic!("the statement declares a fn"),
    };
    let fn_body = |stmt: usize| match fn_lit(stmt) {
        Expr::Function { body, .. } => body,
        _ => panic!("the local binds a fn literal"),
    };

    // the depth-two access: `t[s]` inside Get inside Twice — the pair
    // keys against TWICE's call (the outermost), the shadow lives in
    // kTwice's record, and the IMMEDIATE enclosure's record (kGet's)
    // is empty by the site law
    let t_call = print_call(4);
    let k_twice = only_child(crate::shape::InstanceId::ROOT, t_call);
    let (t_read, _s_read) = match &fn_body(2)[0] {
        Stmt::Return {
            value: Some(Expr::Index { obj, key, .. }),
            ..
        } => (obj.id(), key.id()),
        _ => panic!("Get returns one index read"),
    };
    let k_get1 = only_child(
        k_twice,
        match &fn_body(3)[0] {
            Stmt::Return {
                value: Some(Expr::BinaryOp { left, .. }),
                ..
            } => left.id(),
            _ => panic!("Twice returns the sum of two calls"),
        },
    );
    let face = &shape.access_elems[&(t_read, t_call)];
    assert_eq!(
        shape.instance_of[&(t_read, t_call)],
        k_twice,
        "the depth-two access bridges to the OUTERMOST instance"
    );
    assert_eq!(
        shape.instances[&k_twice].access_elems[&t_read], *face,
        "the instance view of the depth-two elem face equals the pair view"
    );
    assert!(
        shape.instances[&k_get1].access_elems.is_empty(),
        "a nested instance's shadow maps are empty by the site law — \
         the facts key against the outermost"
    );

    // the depth-two lane: `t[keys[i]]` inside Sel inside Wrap — the
    // outer key's lane rides Wrap's instance
    let w0 = print_call(8);
    let k_wrap0 = only_child(crate::shape::InstanceId::ROOT, w0);
    let outer_key = match &fn_body(6)[0] {
        Stmt::Return {
            value: Some(Expr::Index { key, .. }),
            ..
        } => match key.as_ref() {
            Expr::Index { .. } => key.id(),
            _ => panic!("Sel's outer key is the nested keys[i] read"),
        },
        _ => panic!("Sel returns one index read"),
    };
    let lane = shape.index_key_lanes[&(outer_key, w0)];
    assert_eq!(
        shape.instance_of[&(outer_key, w0)],
        k_wrap0,
        "the depth-two lane bridges to the OUTERMOST instance"
    );
    assert_eq!(
        shape.instances[&k_wrap0].index_key_lanes[&outer_key], lane,
        "the instance view of the depth-two lane equals the pair view"
    );

    // the depth-two call-through: f(n) inside Drive inside Outer — an
    // IDENTIFIER dispatch through the closure value (closure_calls is
    // the Field-callee face and stays empty here); the dispatch's own
    // pair keys against OUTER's call, its owner is kOuter (never
    // kDrive, the immediate enclosure); the dispatch's instance
    // carries the env face (Add1 captures nothing — the empty face)
    // and mints exactly like a direct call — resolution-keyed minting
    // has no entry for a value dispatch
    let o_call = print_call(13);
    let k_outer = only_child(crate::shape::InstanceId::ROOT, o_call);
    let d_call = match &fn_body(12)[0] {
        Stmt::Return {
            value: Some(call @ Expr::Call { .. }),
            ..
        } => call.id(),
        _ => panic!("Outer returns one call"),
    };
    let k_drive = only_child(k_outer, d_call);
    let f_call = match &fn_body(11)[0] {
        Stmt::Return {
            value: Some(call @ Expr::Call { .. }),
            ..
        } => call.id(),
        _ => panic!("Drive returns one call"),
    };
    assert_eq!(
        shape.instance_of[&(f_call, o_call)],
        k_outer,
        "the call-through's pair keys against the OUTERMOST site — the \
         site law, never the immediate enclosure"
    );
    assert!(
        shape.instances[&k_drive].children.is_empty()
            && shape.instances[&k_drive].closure_calls.is_empty(),
        "the immediate enclosure (kDrive) owns nothing — it is not the \
         outermost"
    );
    let k_f = only_child(k_outer, f_call);
    let add1_lit = fn_lit(10).id();
    let f_rec = &shape.instances[&k_f];
    assert_eq!(f_rec.fn_node, Some(add1_lit), "the dispatch inlines Add1");
    assert_eq!(
        f_rec.env_face,
        Some(std::collections::BTreeMap::new()),
        "R3: the call-through's env face rides its own instance record"
    );
    assert_eq!(
        f_rec.params,
        vec!["x".to_string()],
        "the record carries the INLINED body's params — the dispatch \
         inlines Add1, not Drive"
    );
    assert_eq!(f_rec.body.len(), 1, "the record owns Add1's body");
    assert_eq!(
        f_rec.body[0].loc().line,
        fn_body(10)[0].loc().line,
        "the owned body is the inlined literal's own statements"
    );
    assert_eq!(
        f_rec.frame_base, 2,
        "frames: Outer's and Drive's scopes below the mint"
    );
    assert_eq!(f_rec.break_base, 0, "no loops anywhere in the chain");
}
