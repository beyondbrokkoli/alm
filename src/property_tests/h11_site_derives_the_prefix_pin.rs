
/// H11 pin 2 — the site is the ONLY line source. One diagnostic text,
/// two programs whose failing statements sit on different lines: the
/// renders differ by the prefix alone, derived from the stamp. The
/// unit leg pins the same law at the mint: site None renders no
/// prefix at all (the root-exit/bare pushes' face).
#[test]
fn h11_site_derives_the_prefix_pin() {
    // unit: the prefix appears iff the site does — nothing else moves
    let d = Diagnostic::ty("'+' requires numeric operands");
    assert_eq!(
        d.render(),
        "Type Error: '+' requires numeric operands",
        "site None renders no line prefix"
    );
    assert_eq!(
        d.clone().with_site(Some(3)).render(),
        "line 3: Type Error: '+' requires numeric operands",
        "the prefix is derived from the stamp alone"
    );
    assert_eq!(
        d.with_site(Some(41)).render(),
        "line 41: Type Error: '+' requires numeric operands",
        "the text is unchanged by the stamp"
    );
    // shipped: same reject, same TEXT — the line tracks the statement
    let near =
        compile("local t = {1}\nlocal u = t\nlocal v = t\n").expect_err("the double move rejects");
    let far = compile("local t = {1}\nlocal u = t\n\n\nlocal v = t\n")
        .expect_err("the same double move rejects three lines later");
    let render_near = near.1[0].render();
    let render_far = far.1[0].render();
    assert_eq!(
        render_near,
        "line 3: Lifetime Error: 't' may be moved here — reads through a \
         possibly-moved name are rejected at compile time"
    );
    assert_eq!(
        render_far,
        "line 5: Lifetime Error: 't' may be moved here — reads through a \
         possibly-moved name are rejected at compile time"
    );
    assert_eq!(
        render_near.replace("line 3: ", ""),
        render_far.replace("line 5: ", ""),
        "one text, two sites — only the derived prefix differs"
    );
    assert_eq!(near.1[0].site, Some(3));
    assert_eq!(far.1[0].site, Some(5));
}
