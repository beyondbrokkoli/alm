
/// H11 pin 3 — the kinds table and the desync protocol's render law.
/// The six regular faces own their exact prefixes; Bare and Desync
/// render their text verbatim (the desync message's face and
/// "— … disagree" tail are content, not format — H12's 7c deletes the
/// variant with the class). Desync-ness is the variant, never bytes.
#[test]
fn h11_kinds_and_desync_render_law_pin() {
    let table: &[(Diagnostic, &str)] = &[
        (Diagnostic::syntax("body"), "line 1: Syntax Error: body"),
        (Diagnostic::ty("body"), "line 1: Type Error: body"),
        (Diagnostic::scope("body"), "line 1: Scope Error: body"),
        (Diagnostic::lifetime("body"), "line 1: Lifetime Error: body"),
        (Diagnostic::lower("body"), "line 1: Lower Error: body"),
        (
            Diagnostic::bounds("body"),
            "line 1: Table Bounds Error: body",
        ),
    ];
    for (d, golden) in table {
        let stamped = d.clone().with_site(Some(1));
        assert_eq!(stamped.render(), *golden, "the prefix table is exact");
        assert!(!d.is_desync(), "a regular face is never a desync");
        assert!(d.site.is_none(), "the mint carries no site");
    }
    // Bare: the driver-face refusal shape — verbatim, prefixless
    assert_eq!(Diagnostic::bare("refusal text").render(), "refusal text");
    assert!(!Diagnostic::bare("refusal text").is_desync());
    // Desync: the protocol's face — verbatim (its inline "Lower
    // Error:" face and tail stay), and the variant classifies
    let desync_text = "Lower Error: a stored value's repr disagrees with the table's \
         element type — the checker and the lowerer disagree";
    let desync = Diagnostic::desync(desync_text);
    assert_eq!(desync.render(), desync_text);
    assert!(desync.is_desync());
    assert!(
        desync.with_site(Some(7)).is_desync(),
        "the stamp never changes the class"
    );
}
