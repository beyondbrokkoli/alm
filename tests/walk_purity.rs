//! The walk-pins purity leg (L3's port of mirror's
//! `walk_pins_are_a_pure_subset_over_the_corpus`, adapted to the
//! walk-only analyzer): the pins may only refine internals —
//! acceptance, refusal stage, diagnostics, and the rendered facts must
//! be identical with the lever on or off. mirror's leg diffs the
//! emitted `.ll`; the `.ll` surface arrives at L7 and the leg tightens
//! back to byte-identical codegen then.

mod common;

use common::{Rng, analyze_with_lever, cases_dir, collect_lua_files, gen_program};

#[test]
fn walk_pins_are_a_pure_subset_over_the_corpus() {
    let mut bases: Vec<(String, String)> = Vec::new();
    let mut rng = Rng::new(0xA11_5EED);
    for i in 0..16 {
        bases.push((format!("generated#{i}"), gen_program(&mut rng)));
    }
    let mut files = Vec::new();
    collect_lua_files(&cases_dir(), &mut files);
    for path in files {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_string();
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{} unreadable: {e}", path.display()));
        bases.push((name, text));
    }
    assert!(
        bases.len() > 16,
        "the corpus pool did not load — only {} bases",
        bases.len()
    );

    let mut accepted = 0usize;
    for (label, source) in &bases {
        let on = analyze_with_lever(label.clone(), source.clone(), true);
        let off = analyze_with_lever(label.clone(), source.clone(), false);
        match (on, off) {
            (Ok(dump_on), Ok(dump_off)) => {
                accepted += 1;
                assert!(
                    facts_equal_modulo_pin_refinement(&dump_on, &dump_off),
                    "walk pins changed the facts for {label}:\n  pins on : {dump_on}\n  \
                     pins off: {dump_off}"
                );
            }
            (Err((stage_on, diags_on)), Err((stage_off, diags_off))) => {
                assert_eq!(
                    stage_on.name(),
                    stage_off.name(),
                    "walk pins moved the refusal stage for {label}"
                );
                assert_eq!(
                    diags_on, diags_off,
                    "walk pins changed diagnostics for {label}"
                );
            }
            (on, off) => {
                panic!(
                    "walk pins flipped acceptance for {label}:\n  pins on : {}\n  pins off: {}",
                    outcome(&on),
                    outcome(&off)
                );
            }
        }
    }
    assert!(
        accepted >= 10,
        "only {accepted} bases reached the walk — the accepted leg never exercised"
    );
    eprintln!(
        "walk-pin differential: {} bases, {accepted} accepted (identical facts)",
        bases.len()
    );
}

fn outcome(r: &Result<String, (alm::pipeline::Stage, String)>) -> String {
    match r {
        Ok(_) => "accepted".to_string(),
        Err((s, d)) => format!("{}: {}", s.name(), d),
    }
}

/// The subset law at the facts tier: identical lines, with an
/// `Unknown(n)` elem on one side refining to a scalar on the other —
/// the chartered refinement, and the only permitted difference. Every
/// other fact family (sites, layouts, ownership, ghosts, fn faces)
/// must match byte-for-byte.
fn facts_equal_modulo_pin_refinement(on: &str, off: &str) -> bool {
    let mut on = on.lines().filter(|l| !l.is_empty());
    let mut off = off.lines().filter(|l| !l.is_empty());
    loop {
        match (on.next(), off.next()) {
            (None, None) => return true,
            (Some(a), Some(b)) => {
                if a == b {
                    continue;
                }
                let is_elem = |l: &str| l.starts_with("  site ") && l.contains(" elem ");
                let refinee = |l: &str| -> (String, String) {
                    // "  site N @line L elem TY layout V" keeps its
                    // identity prefix and its layout; only TY may refine.
                    let (prefix, rest) = l.split_once(" elem ").unwrap_or((l, ""));
                    let layout = rest.split_once(" layout ").map(|x| x.1).unwrap_or("");
                    (prefix.to_string(), layout.to_string())
                };
                if is_elem(a) && is_elem(b) && refinee(a) == refinee(b) {
                    continue;
                }
                return false;
            }
            (None, Some(_)) | (Some(_), None) => return false,
        }
    }
}

#[test]
fn walk_pin_len_deferral_rejects_identically_pin() {
    // (L4 receipt: mirror asserts the case REJECTS at the analyzer with
    // the checker's "'#' requires … got Integer" diagnostic; alm's walk
    // alone accepts it — the rejection is checker-owned. The on/off
    // differential — this layer's law — ports now; the rejection
    // assertions port verbatim with the checker.)
    let source = "print(#arg[0])\nlocal n = arg[0] + 1\n";
    let on = analyze_with_lever("len_deferral".into(), source.into(), true);
    let off = analyze_with_lever("len_deferral".into(), source.into(), false);
    match (&on, &off) {
        (Ok(a), Ok(b)) => assert_eq!(a, b, "the len-deferral pins changed the facts"),
        (Err((s1, d1)), Err((s2, d2))) => {
            assert_eq!(s1.name(), s2.name());
            assert_eq!(d1, d2);
        }
        _ => panic!(
            "the len-deferral case flipped acceptance:\n  pins on : {}\n  pins off: {}",
            outcome(&on),
            outcome(&off)
        ),
    }
}

#[test]
fn walk_pin_computed_scalars_stay_legal_pin() {
    let source = "local n = arg[0] + 1\n\
                  local m = n + 1\n\
                  local copy = m\n\
                  local t = { x = arg[0] + 1 }\n\
                  print(m + copy + t.x)\n";
    let on = analyze_with_lever("computed_scalars".into(), source.into(), true);
    let off = analyze_with_lever("computed_scalars".into(), source.into(), false);
    match (&on, &off) {
        (Ok(a), Ok(b)) => assert_eq!(
            a, b,
            "the computed-scalar pins changed the facts — the subset discipline broke"
        ),
        _ => panic!(
            "the computed-scalar program must stay legal on both lever positions:\n  \
             pins on : {}\n  pins off: {}",
            outcome(&on),
            outcome(&off)
        ),
    }
}

#[test]
fn walk_pin_unary_neg_scalar_stays_legal_pin() {
    let source = "local k = -arg[0]\nprint(k)\n";
    let on = analyze_with_lever("unary_neg".into(), source.into(), true);
    let off = analyze_with_lever("unary_neg".into(), source.into(), false);
    match (&on, &off) {
        (Ok(a), Ok(b)) => assert_eq!(
            a, b,
            "the unary-neg pin changed the facts — the subset discipline broke"
        ),
        _ => panic!(
            "the unary-neg program must stay legal on both lever positions:\n  \
             pins on : {}\n  pins off: {}",
            outcome(&on),
            outcome(&off)
        ),
    }
}

#[test]
fn generated_programs_walk_clean() {
    // The generator's base law at L3: every generated program walks
    // (accepts or refuses at Analyze, never panics, never refuses at
    // the front — the generator's grammar is the dialect's subset).
    let mut rng = Rng::new(0xBEEF);
    for i in 0..64 {
        let source = gen_program(&mut rng);
        let out = analyze_with_lever(format!("gen#{i}"), source, true);
        assert!(
            !matches!(&out, Err((s, _)) if matches!(s, alm::pipeline::Stage::Panicked)),
            "a generated program crashed the walk"
        );
        assert!(
            !matches!(&out, Err((s, d)) if s.name() == "front (lexer/parser)" && !d.is_empty()),
            "a generated program failed the front end"
        );
    }
}
