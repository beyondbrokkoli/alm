/// H12 7b-prep — the W3a dispatch family's site law at depth one of an
/// EXPANSION: a record-field closure dispatch (`box.op(acc)`) checked
/// inside F's extent keys its pair against the OUTERMOST extent (F's
/// own call), so the dispatch's kind rides the OWNER's `closure_calls`,
/// R4's precedence rides the OWNER's `children`, and ROOT carries
/// neither — while the dispatch's own record (the immediate enclosure)
/// stays empty by law. Each Apply event mints at the ABSOLUTE base of
/// F's loop (1) with its call-through env face (R3). 7b reads the
/// dispatch kind, the precedence, the base, and the face off these
/// records; this pin holds every value exact before the stacks die.
#[test]
fn h12_nested_dispatch_rides_the_outer_owner_pin() {
    let source = "\
local function MakeAdder(seed)
    local function Apply(x) return x + seed end
    return Apply
end
local box = { op = MakeAdder(5) }
local acc = 0
local function F()
    local q
    local n = 0
    while n < 2 do
        n = n + 1
        acc = box.op(acc)
    end
    return acc
end
F()
F()
print(acc)
";
    // the full pipeline: the dispatch's pair-map reads resolve inside
    // the expansion and the program lowers clean
    let ll = compile(source).unwrap_or_else(|(stage, diags)| {
        panic!(
            "the nested dispatch program must lower clean at {}: {}",
            stage.name(),
            diags_text(&diags)
        )
    });
    assert!(
        ll.contains("@alm_print_int"),
        "the Int accumulator's print rides the scalar boundary"
    );

    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "the dispatch pin must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );
    assert_eq!(
        shape.instances.len(),
        6,
        "ROOT + MakeAdder + two F events + two Apply events"
    );

    let root = &shape.instances[&crate::shape::InstanceId::ROOT];
    assert_eq!(
        root.children.len(),
        3,
        "MakeAdder's call and the two F calls mint ROOT's children"
    );
    assert!(
        root.closure_calls.is_empty(),
        "the dispatch checked inside F's extent NEVER self-pairs to ROOT — \
         the site law keys it against the OUTERMOST extent"
    );
    assert!(root.creation_envs.is_empty(), "a callee read never mints");

    // the two F extents: identify by their children (each minted one
    // Apply); MakeAdder's record carries the creation env instead
    let mut f_events = Vec::new();
    for set in root.children.values() {
        let kid = *set.iter().next().unwrap();
        let rec = &shape.instances[&kid];
        if !rec.children.is_empty() {
            let f_call = rec.call.expect("F's record names its own call expr");
            let boxop = *rec.children.keys().next().unwrap();
            f_events.push((f_call, kid, boxop));
        }
    }
    assert_eq!(f_events.len(), 2, "two F events, each owning the dispatch");
    let (f1_call, f1_inst, boxop) = f_events[0];
    let (f2_call, _, _) = f_events[1];
    assert_ne!(f1_call, f2_call, "two F calls, two sites");

    // Apply's literal id: either event's record names it
    let apply1 = *shape.instances[&f1_inst].children[&boxop]
        .iter()
        .next()
        .unwrap();
    let apply_lit = shape.instances[&apply1]
        .fn_node
        .expect("the dispatch inlines Apply");
    assert!(
        shape.fn_defs.contains_key(&apply_lit),
        "the dispatch's callee is a real fn literal"
    );

    for (f_call, f_inst, boxop) in &f_events {
        let f_rec = &shape.instances[f_inst];
        assert_eq!(
            f_rec.children.len(),
            1,
            "the dispatch call is the extent's only child key"
        );
        // the OWNER-side kind: closure_calls rides the outermost
        // extent's record (the lowerer's :2090 successor)
        assert!(
            f_rec.closure_calls.contains(boxop),
            "the dispatch's kind rides the OWNER's closure_calls set"
        );
        assert_eq!(
            shape.instance_of[&(*boxop, *f_call)],
            *f_inst,
            "the dispatch's pair bridges to F's instance — the OUTERMOST \
             extent, never the immediate enclosure"
        );
        let apply_inst = *f_rec.children[boxop].iter().next().unwrap();
        let apply_rec = &shape.instances[&apply_inst];
        // the immediate enclosure owns nothing
        assert!(
            apply_rec.closure_calls.is_empty()
                && apply_rec.children.is_empty()
                && apply_rec.creation_envs.is_empty(),
            "the dispatch's own record carries no shadow maps — the site law"
        );
        // R1 at the nested dispatch: absolute base 1 (inside F's while)
        assert_eq!(
            apply_rec.break_base, 1,
            "the dispatch expands at ABSOLUTE base 1 — inside F's loop"
        );
        // R3: the call-through face names the capture and its type
        let face = apply_rec
            .env_face
            .as_ref()
            .expect("the dispatch records its call-through env face");
        assert_eq!(
            face.get("seed"),
            Some(&crate::shape::Ty::Int),
            "the env face names Apply's capture"
        );
        assert_eq!(
            apply_rec.fn_node,
            Some(apply_lit),
            "both events inline the same literal — pair-monomorphic"
        );
    }
}
