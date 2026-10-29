
/// The rebind-adoption probes, pinned permanently (they lived only in
/// throwaway differential batteries): the nested-table rebind and its
/// nil-severed flavor must adopt in the LATTICE — one elem truth — and
/// the move flavor with them (the move-slot law: `local u = t` severs
/// the name but its type slot survives, so the later rebind adopts
/// across the move exactly as it adopts across a nil).
#[test]
fn rebind_adoption_probes_stay_pinned() {
    let flat: &[(&str, Elem)] = &[
        (
            "local t = {1}\nlocal u = t\nt = {2.5}\nprint(t[0])\nprint(u[0])\n",
            Elem::Any,
        ),
        (
            "local t = {1}\nlocal u = t\nt = nil\nprint(u[0])\n",
            Elem::Int,
        ),
    ];
    for (source, expected) in flat {
        match compile(source) {
            Ok(ll) => assert_elem_congruence(&ll, *expected, "rebind adoption probe"),
            Err((stage, diags)) => panic!(
                "{}",
                report(
                    source,
                    *expected,
                    format!(
                        "adoption probe was rejected at {}: {}",
                        stage.name(),
                        diags_text(&diags)
                    ),
                )
            ),
        }
    }
    for source in [
        "local t = {{1}}\nt = {{2.5}}\nprint(t[0][0])\n",
        "local t = {{1}}\nt = nil\nt = {{2.5}}\nprint(t[0][0])\n",
    ] {
        let ll = compile(source).unwrap_or_else(|(stage, diags)| {
            panic!(
                "{}",
                report(
                    source,
                    Elem::Any,
                    format!(
                        "nested adoption probe was rejected at {}: {}",
                        stage.name(),
                        diags_text(&diags)
                    ),
                )
            )
        });
        let inner_esize16 = ll
            .lines()
            .filter(|l| !l.contains("ptrtoint"))
            .filter(|l| l.contains("@alm_tbl_new(i64 16"))
            .count();
        assert_eq!(
            inner_esize16,
            2,
            "nested adoption probe: expected both inner ctors at esize 16 (retroactive \
             packing)\nprogram:\n{}",
            indent(source)
        );
        assert!(
            ll.lines()
                .any(|l| l.contains("@alm_tbl_get_any") || l.contains("@alm_tbl_set_any")),
            "nested adoption probe: no Any face in the artifact — the packed cells lost \
             their dynamic faces\nprogram:\n{}",
            indent(source)
        );
    }
    assert!(
        compile(
            "local f = function() return 1 end\ndo\n  f = function() return 2 end\nend\nprint(f())\n"
        )
        .is_ok(),
        "block-scoped fn rebind must compile (the rebind takes effect)"
    );
    let (_, diags) = compile("local t = {1}\nlocal u = t\nprint(t[0])\n")
        .expect_err("a read through a moved name must reject");
    assert!(
        diags
            .iter()
            .any(|d| d.render().contains("may be moved here")),
        "moved read rejected with the wrong diagnostic: {diags:?}"
    );
}
