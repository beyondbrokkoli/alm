
// H12/7a — the materialized expansion instances: the checker's
// `expand_call` mints `InstanceId` at ENTRY (one id per expansion
// EVENT), records `InstanceInfo`, and builds the instance-keyed shadow
// ALONGSIDE every pair-keyed insert; the bridge `(expr, site) → owner`
// rides them; the assembly-side assert (analyze_with's finish) holds
// the two views equal every compile. These three pins hold the mint
// law, the depth-two golden (fn_nested_site_keys's shape re-aimed at
// instances), and the bridge's totality. Rulings R1–R5 live in the
// InstanceInfo/facts notes; nothing is consumed yet (7b does that).

/// H12 pin 1 — the mint law: instances are EVENT-minted at expansion
/// entry. The same call expr at two sites mints two instances; the
/// same body expanded twice under ONE owner mints twice over ONE pair
/// (the pair is truth-keyed, monomorphism forces the events to agree);
/// ids draw strictly increasing in entry (check) order. Resolution-keyed
/// minting could not produce this shape — the pair view holds eight
/// entries where the instance view holds ten mints.
#[test]
fn h12_instance_mint_law_pin() {
    let source = "\
local function H() return 5 end
local function G() return H() end
local function F() return G() + G() end
print(F())
print(F())
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "H12 pin source must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );

    // node addresses: the two top-level F calls, the two G calls in
    // F's body, and the ONE H call node in G's body
    let call_of_print = |stmt: usize| match &ast[stmt] {
        Stmt::Print { exprs, .. } => &exprs[0],
        _ => panic!("the statement prints one call"),
    };
    let f1 = call_of_print(3).id();
    let f2 = call_of_print(4).id();
    let fn_body = |stmt: usize| match &ast[stmt] {
        Stmt::LocalDecl { exprs, .. } => match &exprs[0] {
            Expr::Function { body, .. } => body,
            _ => panic!("the local binds a fn literal"),
        },
        _ => panic!("the statement declares a fn"),
    };
    let f_body = fn_body(2);
    let (g1, g2) = match &f_body[0] {
        Stmt::Return {
            value: Some(Expr::BinaryOp { left, right, .. }),
            ..
        } => (left.as_ref(), right.as_ref()),
        _ => panic!("F's body returns the sum of two calls"),
    };
    let (g1, g2, h) = (
        g1.id(),
        g2.id(),
        match &fn_body(1)[0] {
            Stmt::Return {
                value: Some(call @ Expr::Call { .. }),
                ..
            } => call.id(),
            _ => panic!("G's body returns one call"),
        },
    );

    // instance addresses: ROOT names the top-level calls; each owner
    // names its own extent's mints
    let root = &shape.instances[&crate::shape::InstanceId::ROOT];
    let only_child =
        |owner_children: &std::collections::BTreeMap<
            NodeId,
            std::collections::BTreeSet<crate::shape::InstanceId>,
        >,
         call: NodeId| { *owner_children[&call].iter().next().unwrap() };
    let kf1 = only_child(&root.children, f1);
    let kf2 = only_child(&root.children, f2);
    let kg1 = only_child(&shape.instances[&kf1].children, g1);
    let kg2 = only_child(&shape.instances[&kf1].children, g2);
    let (kg3, kg4) = (
        only_child(&shape.instances[&kf2].children, g1),
        only_child(&shape.instances[&kf2].children, g2),
    );
    // the SITE LAW: the H call sits in G's body, but its pairs key
    // against the OUTERMOST site (F's call) — so its events hang off
    // kF1/kF2's children sets, and the immediate enclosures (the G
    // instances) own NOTHING (a nested instance's maps are empty by
    // law — the facts key against the outermost)
    let h_under_f1 = {
        let mut v: Vec<_> = shape.instances[&kf1].children[&h].iter().copied().collect();
        v.sort();
        (v[0], v[1])
    };
    let (kh1, kh2) = h_under_f1;
    let h_under_f2 = {
        let mut v: Vec<_> = shape.instances[&kf2].children[&h].iter().copied().collect();
        v.sort();
        (v[0], v[1])
    };
    let (kh3, kh4) = h_under_f2;
    for kg in [kg1, kg2, kg3, kg4] {
        assert!(
            shape.instances[&kg].children.is_empty(),
            "a nested instance owns nothing — the site law keys against the outermost"
        );
    }

    // the mint count: ROOT + 2 F + 4 G + 4 H = 11 records — the pair
    // view holds only 8 keys (F1,F2,g1@F1,g2@F1,g1@F2,g2@F2,h@F1,h@F2);
    // the four H events mint over the two H pairs
    assert_eq!(
        shape.instances.len(),
        11,
        "ten expansion events mint ten instances plus ROOT"
    );
    assert_eq!(
        shape.call_defs.len(),
        8,
        "the pair view is truth-keyed — fewer entries than events"
    );

    // ids mint at ENTRY, in check order, strictly increasing
    let order = [kf1, kg1, kh1, kg2, kh2, kf2, kg3, kh3, kg4, kh4];
    for w in order.windows(2) {
        assert!(
            w[0] < w[1],
            "instance ids draw in entry order: {w:?} out of order"
        );
    }
    assert!(
        order.iter().all(|&k| k > crate::shape::InstanceId::ROOT),
        "ROOT (0) is never drawn from the mint"
    );

    // the same H call node at two sites mints at both — and TWICE per
    // site (G's body expands twice inside each F extent): the owner's
    // children SET carries both events over the ONE pair
    assert_ne!(
        kh1, kh3,
        "the same call expr at two sites mints two instances"
    );
    assert_eq!(
        shape.instances[&kf1].children[&h].len(),
        2,
        "one pair, two events under one owner — children is set-valued"
    );
    assert_eq!(shape.instances[&kf2].children[&h].len(), 2);
    assert_eq!(
        shape.instance_of[&(h, f1)],
        kf1,
        "the bridge names the pair's owner — the outermost expansion's instance"
    );

    // every record's static faces: the call it minted for, the callee
    // it inlines, an owned body, the params
    for (&k, rec) in &shape.instances {
        if k == crate::shape::InstanceId::ROOT {
            assert!(rec.call.is_none() && rec.fn_node.is_none() && rec.ret.is_none());
            continue;
        }
        assert!(rec.call.is_some(), "a minted record names its call");
        let callee = rec.fn_node.expect("a minted record names its callee");
        assert!(
            shape.fn_defs.contains_key(&callee),
            "the record's callee is a real fn literal"
        );
    }
    let h_lit = match &ast[0] {
        Stmt::LocalDecl { exprs, .. } => exprs[0].id(),
        _ => panic!("H's literal is the first declaration"),
    };
    for kh in [kh1, kh2, kh3, kh4] {
        let rec = &shape.instances[&kh];
        assert_eq!(
            rec.fn_node,
            Some(h_lit),
            "every H event inlines the same literal"
        );
        assert_eq!(rec.call, Some(h), "every H event names the same call node");
        assert!(!rec.body.is_empty(), "the record owns the body");
        assert_eq!(rec.body.len(), 1, "H's body is one statement");
    }
}
