/// H12 7b-prep — the union read's inputs. `calls_touched` (H9's
/// deliberate survivor, feeding phi_order and the If arms) unions
/// `call_defs` over ONE call expr across ALL its sites
/// (`range((key, 0)..=(key, MAX))`) — the order-insensitive consumer
/// the per-instantiation keys were designed to leave alone. The same
/// call EXPR node rides both extents (one shared body, H6's
/// self-contained ids), so its pairs exist per site, each naming the
/// same literal. 7c's kill of `call_defs` owes this read a successor
/// (a per-expr projection or an ordered index) — this pin holds its
/// exact read shape loud until that design lands.
#[test]
fn h12_instantiation_facts_cover_every_site_pin() {
    let source = "\
local acc = 0
local function G()
    acc = acc + 1
    return acc
end
local function F()
    return G()
end
F()
F()
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "the union-read pin must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );

    // F's two top-level calls mint two extents; G's ONE call expr
    // node (the shared body) instantiates in both
    let root = &shape.instances[&crate::shape::InstanceId::ROOT];
    assert_eq!(root.children.len(), 2, "two F calls, two extents");
    let f_insts: Vec<_> = root.children.values().flatten().copied().collect();
    let f1_call = shape.instances[&f_insts[0]]
        .call
        .expect("each extent names its own call expr");
    let f2_call = shape.instances[&f_insts[1]]
        .call
        .expect("each extent names its own call expr");
    assert_ne!(f1_call, f2_call, "two sites, two call exprs");
    let g_call = *shape.instances[&f_insts[0]]
        .children
        .keys()
        .next()
        .expect("F's extent minted G");

    // the pair truth exists PER SITE, same expr, same literal
    let g_lit = shape.call_defs[&(g_call, f1_call)];
    assert_eq!(
        shape.call_defs.get(&(g_call, f2_call)),
        Some(&g_lit),
        "both sites resolve the same literal — pair-monomorphic across sites"
    );
    assert!(
        !shape.call_defs.contains_key(&(g_call, g_call)),
        "the nested call never self-pairs — its site is F's extent"
    );

    // fn_touched carries the outer touches the union folds
    let touched = shape
        .fn_touched
        .get(&g_lit)
        .expect("G's literal records its outer touches");
    assert_eq!(
        touched,
        &std::collections::BTreeSet::from(["acc".to_string()]),
        "G assigns exactly its outer acc"
    );

    // THE UNION READ'S EXACT SHAPE — the same range query
    // calls_touched performs, replayed over the facts: one expr, all
    // sites, folded to one touch set
    let mut union = std::collections::BTreeSet::new();
    for (_, &fp) in shape
        .call_defs
        .range((g_call, NodeId(0))..=(g_call, NodeId(u32::MAX)))
    {
        if let Some(t) = shape.fn_touched.get(&fp) {
            union.extend(t.iter().cloned());
        }
    }
    assert_eq!(
        union,
        std::collections::BTreeSet::from(["acc".to_string()]),
        "the union read folds every instantiation's touches — 7c's successor \
         must reproduce exactly this reachability"
    );
}
