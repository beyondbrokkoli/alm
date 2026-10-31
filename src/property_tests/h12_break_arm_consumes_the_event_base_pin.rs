/// H12 7b-prep — the Break arm CONSUMES the per-event base: the
/// divergent multi-event shape (one shared body, two events over one
/// pair, absolute bases 0 and 1) whose body carries its OWN
/// `while`+`break`. The lowerer's Break arm reads the CURRENT event's
/// base off the stack today; 7b's ordered cursor must read it off the
/// event's OWN record — an any-kid pick that lands a DEEPER event's
/// base on the shallower event fires the crossing guard spuriously
/// ("break crossing an expansion boundary") and this legal program
/// stops compiling. The body touches no outer name (the loop-phi
/// collectors' law is pinned separately) so the divergence is the only
/// thing on the board. The analysis half holds the exact shape the
/// cursor must reproduce; the lowering half is the consumption proof.
#[test]
fn h12_break_arm_consumes_the_event_base_pin() {
    let source = "\
local t = { [0] = 7 }
local function H()
    local m = 0
    while true do
        break
    end
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
    // the lowering half: the Break arm rides the divergent bases and
    // the program must compile clean — a too-high event pick dies here
    // by name
    let ll = compile(source).unwrap_or_else(|(stage, diags)| {
        panic!(
            "the divergent break program must lower clean at {}: {}",
            stage.name(),
            diags_text(&diags)
        )
    });
    assert!(
        !ll.contains("@alm_tbl_get_any"),
        "the Int table's reads stay scalar through the divergent extents"
    );

    // the analysis half: the exact event shape the cursor must pick from
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "the break-arm pin must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );
    assert_eq!(
        shape.instances.len(),
        6,
        "ROOT + F + two G events + two H events"
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
        3,
        "F's extent minted g_a, g_c, and the shared h — three call exprs"
    );
    let (_, h_kids) = f_rec
        .children
        .iter()
        .find(|(_, s)| s.len() == 2)
        .expect("the shared body's call mints two events over one pair");
    let h_expr = f_rec
        .children
        .iter()
        .find(|(_, s)| s.len() == 2)
        .unwrap()
        .0;
    assert_eq!(
        shape.instance_of[&(*h_expr, f_call)],
        f_inst,
        "the multi-event pair bridges to the OUTERMOST extent's instance"
    );
    let bases: Vec<_> = h_kids
        .iter()
        .map(|k| shape.instances[k].break_base)
        .collect();
    assert_eq!(
        bases,
        vec![0, 1],
        "the events' absolute bases diverge by exactly F's while — the Break \
         arm must consult the CURRENT event's base; an any-kid pick that \
         lands base 1 on the depth-0 event fires the crossing guard \
         spuriously and this legal program stops compiling"
    );
    for k in h_kids {
        assert!(
            shape.instances[k].body.len() == 3,
            "every H event owns the break-bearing body (H6's owned-body shape)"
        );
    }
}
