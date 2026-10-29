/// H12 7b-prep — R1's absolute base at a W3a record dispatch: a
/// closure call through a record field (`box.op(acc)`) inside a
/// top-level loop expands at ABSOLUTE break base 1 — the same
/// arithmetic as a plain call (the bridge totality pin's leg), while
/// the factory's own call at the top level mints at base 0. R3's
/// recorded call-through face rides the dispatch's record; the plain
/// call carries none. 7b reads the dispatch's base and face off the
/// record; this pin holds those values exact before the stacks die.
#[test]
fn h12_dispatch_mints_at_absolute_base_pin() {
    let source = "\
local function MakeAdder(seed)
    local function Apply(x) return x + seed end
    return Apply
end
local add7 = MakeAdder(7)
local box = { op = add7 }
local acc = 0
while acc < 20 do
    acc = box.op(acc)
end
print(acc)
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "the dispatch pin must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );

    let root = &shape.instances[&crate::shape::InstanceId::ROOT];
    assert_eq!(
        root.children.len(),
        2,
        "MakeAdder's call and the dispatch mint ROOT's children"
    );
    let kids: Vec<_> = root.children.values().flatten().copied().collect();

    // identify by R3's face: the call-through dispatch carries the
    // capture face, the plain factory call does not
    let app_inst = *kids
        .iter()
        .find(|&&k| shape.instances[&k].env_face.is_some())
        .expect("the record-field dispatch records a call-through env face");
    let maker_inst = *kids
        .iter()
        .find(|&&k| shape.instances[&k].env_face.is_none())
        .expect("the plain factory call carries no call-through face");
    let app_rec = &shape.instances[&app_inst];

    // R1 at the dispatch: it expands INSIDE the top-level loop — the
    // ABSOLUTE base is 1, the lowerer's break_ctxs.len() twin; the
    // factory's own call at the top level mints at 0 — the contrast
    // is the pin's teeth
    assert_eq!(
        app_rec.break_base, 1,
        "the dispatch mints at absolute base 1 — inside the loop"
    );
    assert_eq!(
        shape.instances[&maker_inst].break_base, 0,
        "the factory's call mints at the top level — base 0"
    );

    // R3: the call-through face names the capture and its type
    let face = app_rec.env_face.as_ref().unwrap();
    assert_eq!(
        face.get("seed"),
        Some(&crate::shape::Ty::Int),
        "the env face names Apply's capture"
    );

    // the dispatch is a closure call in the pair truth, self-paired
    // at the top level
    let boxop = app_rec
        .call
        .expect("the dispatch's record names its call expr");
    assert!(
        root.closure_calls.contains(&boxop),
        "the Field dispatch rides closure_calls' pair truth"
    );
    assert_eq!(
        shape.instance_of[&(boxop, boxop)],
        crate::shape::InstanceId::ROOT,
        "the top-level dispatch self-pairs to ROOT"
    );

    // the Escape Law's creation family: a CALLEE read never mints
    // ("call arms resolve callees through the fn maps directly and
    // never reach here"), so the top level — whose only fn read is
    // MakeAdder's call — mints no creation env; the value read
    // `return Apply` mints the FACTORY EXTENT's env naming Apply's
    // literal. Creation envs obey the site law too.
    assert!(
        root.creation_envs.is_empty(),
        "a callee-position read never mints — creation is the value read's land"
    );
    let apply_lit = app_rec.fn_node.expect("the dispatch inlines Apply");
    let maker_rec = &shape.instances[&maker_inst];
    let apply_creations: Vec<_> = maker_rec.creation_envs.values().copied().collect();
    assert_eq!(
        apply_creations,
        vec![apply_lit],
        "Apply's escape read (`return Apply`) mints the factory extent's \
         creation env, naming Apply's literal"
    );
}
