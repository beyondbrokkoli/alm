/// H12 7b-prep — the ordered cursor's law generalized: THREE events
/// over ONE pair. G's body (`return H()`, ONE call expr node) expands
/// at loop depths 0, 1, and 2 inside F's extent, so H's three events
/// mint at absolute bases 0, 1, 2 — and the children SET's ascending
/// id order IS the mint order IS F's body order (the pre-order both
/// walks share). 7b's cursor consumes `children[call]` in ascending
/// InstanceId order per (owner, call); this pin holds the three-event
/// arithmetic and the order law exact — a pick that reads the wrong
/// event's base at the Break arm (or any consumer assuming one event
/// per pair) fails here by name.
#[test]
fn h12_three_events_mint_in_body_order_pin() {
    let source = "\
local t = { [0] = 7 }
local function H()
    local m
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
        local b = G()
        local p = 0
        while p < 9 do
            p = p + 1
            local c = G()
        end
    end
    return a
end
local z
F()
";
    // the lowering half: three events ride the divergent bases through
    // the full pipeline (the Call arm's membership sentinel holds per
    // event)
    let ll = compile(source).unwrap_or_else(|(stage, diags)| {
        panic!(
            "the three-event program must lower clean at {}: {}",
            stage.name(),
            diags_text(&diags)
        )
    });
    assert!(
        !ll.contains("@alm_tbl_get_any"),
        "the Int table's reads stay scalar through the three extents"
    );

    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "the three-event pin must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );
    assert_eq!(
        shape.instances.len(),
        8,
        "ROOT + F + three G events + three H events"
    );

    let root = &shape.instances[&crate::shape::InstanceId::ROOT];
    let f_inst = *root
        .children
        .values()
        .next()
        .unwrap()
        .iter()
        .next()
        .unwrap();
    let f_rec = &shape.instances[&f_inst];
    let f_call = f_rec.call.expect("F's record names its own call expr");
    assert_eq!(
        f_rec.children.len(),
        4,
        "F's extent minted g_a, g_b, g_c, and the shared h — four call exprs"
    );

    // THE MULTI-EVENT KEY: three events over the ONE pair, ascending
    // kid order = mint order = F's body order, bases (0, 1, 2)
    let (h_expr, h_kids) = f_rec
        .children
        .iter()
        .find(|(_, s)| s.len() == 3)
        .expect("the shared body's call minted three events over one pair");
    assert_eq!(
        shape.instance_of[&(*h_expr, f_call)],
        f_inst,
        "the three-event pair bridges to the OUTERMOST extent's instance"
    );
    let bases: Vec<_> = h_kids
        .iter()
        .map(|k| shape.instances[k].break_base)
        .collect();
    assert_eq!(
        bases,
        vec![0, 1, 2],
        "three events, three depths, ascending ids = mint order = body \
         order — the ordered cursor's exact law; a wrong pick reads the \
         wrong event's base at the Break arm"
    );

    // the three G events: one per call expr node, one kid each, bases
    // 0/1/2 in body order (the kids' own pairs, distinct sites)
    let mut g_bases = Vec::new();
    for (key, set) in f_rec.children.iter() {
        if set.len() == 1 {
            let g_inst = *set.iter().next().unwrap();
            assert_ne!(
                key, h_expr,
                "the G keys are distinct call exprs — one pair per site"
            );
            g_bases.push(shape.instances[&g_inst].break_base);
            assert!(
                shape.instances[&g_inst].children.is_empty(),
                "G's extent minted H, but H rides the OUTERMOST owner's \
                 children — the immediate enclosure stays empty"
            );
        }
    }
    g_bases.sort();
    assert_eq!(
        g_bases,
        vec![0, 1, 2],
        "the three G events mint at the three loop depths too"
    );

    // the pair truth stays ONE entry while the events are three
    let h_lit = shape.instances[h_kids.iter().next().unwrap()].fn_node;
    let rets: Vec<_> = h_kids
        .iter()
        .map(|k| shape.instances[k].ret.clone())
        .collect();
    assert_eq!(rets[0], rets[1], "one truth pair — the events agree");
    assert_eq!(rets[1], rets[2], "one truth pair — the events agree");
    for k in h_kids {
        assert_eq!(
            shape.instances[k].fn_node, h_lit,
            "every H event inlines the same literal"
        );
    }
    assert!(
        shape.call_defs.contains_key(&(*h_expr, f_call)),
        "the pair view is truth-keyed: one entry, three events"
    );
}
