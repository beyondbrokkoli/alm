/// H12 7b-prep — the bare-decl family's site is the OUTERMOST extent,
/// the same site law the five expr-fact maps ride: a bare declaration
/// checked inside a nested expansion records its type under the
/// OUTERMOST expansion's call (Some), the top level under None (R2's
/// Option face — 7c re-keys onto ROOT). 7b keeps the triple key one
/// milestone; this pin holds the exact key shape its stopgap
/// derivation must reproduce — the site value is the outermost call
/// expr, never the immediate enclosure's.
#[test]
fn h12_local_types_key_the_outermost_extent_pin() {
    let source = "\
local function G()
    local m
    return 0
end
local function F()
    local q
    return G()
end
local z
F()
F()
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "the bare-decl pin must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );

    let sites_of = |name: &str| -> Vec<Option<NodeId>> {
        let mut sites: Vec<Option<NodeId>> = shape
            .local_types
            .iter()
            .filter(|((_, _, n), _)| n == name)
            .map(|((_, s, _), _)| *s)
            .collect();
        sites.sort();
        sites
    };

    // m is G's body's bare decl — checked once per F extent, keyed by
    // F's OWN call expr (the OUTERMOST site), never the immediate
    // enclosure's. The decl itself records its type; READING it would
    // be the possibly-nil refusal (a compile-time lifetime error), so
    // the pin declares and never reads.
    let m_sites = sites_of("m");
    assert_eq!(m_sites.len(), 2, "m's type records once per F extent");
    assert_ne!(m_sites[0], m_sites[1], "one record per extent");
    for s in &m_sites {
        let site = s.expect("a decl inside an expansion keys Some(site)");
        assert!(
            shape.call_defs.contains_key(&(site, site)),
            "the site is a TOP-LEVEL call (self-paired in call_defs) — the \
             OUTERMOST extent, not the immediate enclosure's g-call"
        );
    }

    // q rides F's own extent the same way
    let q_sites = sites_of("q");
    assert_eq!(q_sites.len(), 2, "F's own bare decl records per extent");
    assert!(
        q_sites.iter().all(|s| s.is_some()),
        "F's body is checked inside F's expansion — Some(site)"
    );

    // the top level keys None — R2's Option face
    assert_eq!(
        sites_of("z"),
        vec![None],
        "the top level's bare decl keys None — 7c re-keys this onto ROOT"
    );
}
