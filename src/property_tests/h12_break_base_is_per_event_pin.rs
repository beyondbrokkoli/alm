/// H12 7b-prep — break_base is PER-EVENT, not per-pair. One truth
/// pair can carry MANY minted events (a shared body expanded twice in
/// one extent), and the events' absolute loop bases DIVERGE when the
/// paths reach them at different loop depths. The pair maps stay
/// monomorphic (one entry; every event's pair faces are asserted
/// equal by the every-compile shadow) — but the base lives only in
/// the records, one value per EVENT. 7b's consumption must therefore
/// pick the event's OWN record in mint order; an any-kid pick reads
/// the wrong base at the Break arm and binds a caller's loop.
/// ANALYSIS-ONLY by design: lowering this exact program trips the 7a
/// sentinel's first-kid pick in debug builds (the empirical
/// confirmation rode the 7b prep pass); the ordered cursor retires
/// the pick.
#[test]
fn h12_break_base_is_per_event_pin() {
    let source = "\
local t = { [0] = 7 }
local acc = 0
local function H()
    local m
    acc = acc + 1
    return t[0]
end
local function G()
    return H()
end
local function F()
    local q
    local a = G()
    local n = 0
    while n < 9 do
        n = n + 1
        local c = G()
    end
    return a
end
local z
F()
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "the per-event pin must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );

    // ROOT + F + two G events + two H events — G's two call exprs are
    // two pairs, but H's body is ONE shared expr: two events over ONE
    // pair
    assert_eq!(
        shape.instances.len(),
        6,
        "ROOT + F + two G events + two H events"
    );

    let root = &shape.instances[&crate::shape::InstanceId::ROOT];
    assert_eq!(
        root.children.len(),
        1,
        "F's top-level call is ROOT's only child key"
    );
    let f_inst = *root
        .children
        .values()
        .next()
        .unwrap()
        .iter()
        .next()
        .unwrap();
    let f_rec = &shape.instances[&f_inst];
    assert_eq!(
        f_rec.children.len(),
        3,
        "F's extent minted g1, g2, and h — three call exprs"
    );
    assert_eq!(
        f_rec.break_base, 0,
        "F itself expands at the top level — absolute base 0"
    );

    // THE MULTI-EVENT KEY: h's set carries both events of the ONE
    // pair, ascending id = mint order = F's body order (g1's extent
    // first, then the while's)
    let (&h_expr, h_kids) = f_rec
        .children
        .iter()
        .find(|(_, s)| s.len() == 2)
        .expect("the shared body's call mints two events over one pair");
    let f_call = f_rec.call.expect("F's record names its own call expr");
    assert_eq!(
        shape.instance_of[&(h_expr, f_call)],
        f_inst,
        "the multi-event pair bridges to the OUTERMOST extent's instance"
    );
    let mut bases = h_kids.iter().map(|k| shape.instances[k].break_base);
    let (b1, b2) = (bases.next().unwrap(), bases.next().unwrap());
    assert_eq!(
        (b1, b2),
        (0, 1),
        "the events' absolute bases diverge by exactly the while — break_base \
         is per-EVENT; 7b's pick must be the mint-ordered cursor, an any-kid \
         read binds a caller's loop at the Break arm"
    );

    // the pair faces stay monomorphic — every event's view equals the
    // one pair truth (the shadow asserts this every compile; held here
    // by name)
    let h_lit = shape.instances[h_kids.iter().next().unwrap()].fn_node;
    let rets: Vec<_> = h_kids
        .iter()
        .map(|k| shape.instances[k].ret.clone())
        .collect();
    assert_eq!(rets[0], rets[1], "one truth pair, two events — rets agree");
    for k in h_kids {
        let rec = &shape.instances[k];
        assert_eq!(rec.fn_node, h_lit, "every H event inlines the same literal");
    }
    assert!(
        shape.call_defs.contains_key(&(h_expr, f_call)),
        "the pair truth is ONE entry while children carry BOTH events"
    );

    // the immediate enclosures own nothing — even children
    // registration flattens to the outermost extent
    let g_insts: Vec<_> = f_rec
        .children
        .iter()
        .filter(|(_, s)| s.len() == 1)
        .flat_map(|(_, s)| s.iter().copied())
        .collect();
    assert_eq!(g_insts.len(), 2, "two G events, one per call expr");
    for g in g_insts {
        assert!(
            shape.instances[&g].children.is_empty(),
            "G's extent minted H, but H rides the OUTERMOST owner's children — \
             the immediate enclosure stays empty"
        );
    }

    // the access inside H's body rides the outermost too
    assert_eq!(
        f_rec.access_elems.len(),
        1,
        "t's read inside H's body pairs with F's extent"
    );
    assert!(
        f_rec
            .access_elems
            .values()
            .all(|ty| *ty == crate::shape::Ty::Int),
        "t is an Int table"
    );
}
