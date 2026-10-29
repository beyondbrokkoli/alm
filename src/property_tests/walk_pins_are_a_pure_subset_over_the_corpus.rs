
/// THE SUBSET DISCIPLINE'S DIFFERENTIAL LEG (the pin-owed register,
/// census §3 cluster A rows 1/2/3/6/7/8 + cluster D row 25): every
/// walk-side pin is a documented SUBSET of the pin the checker's own
/// discipline would land at the same site — "a walk pin and the
/// checker pin it preempts bind the same resolved head to the same
/// scalar; the final store, and every fact derived from it, is
/// identical" (pins.rs). Violation is silent by nature (both halves
/// run, only the store's contents differ), so the pin is differential:
/// with the lever off, the checker's pins alone must reproduce the
/// byte-identical `.ll` on acceptance and the identical diagnostics on
/// rejection — over the whole corpus and the generated programs.
#[test]
fn walk_pins_are_a_pure_subset_over_the_corpus() {
    let mut bases: Vec<(String, String)> = Vec::new(); // (label, source)
    let mut rng = Rng::new(0xA11_5EED);
    for i in 0..16 {
        let (source, _) = gen_program(&mut rng);
        bases.push((format!("generated#{i}"), source));
    }
    let cases_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("cases");
    let entries = std::fs::read_dir(&cases_dir).unwrap_or_else(|e| {
        panic!(
            "property_tests: failed to read corpus directory {}: {e}",
            cases_dir.display()
        )
    });
    let mut names: Vec<String> = entries
        .flatten()
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.ends_with(".lua"))
        .collect();
    names.sort();
    for name in &names {
        if let Ok(source) = std::fs::read_to_string(cases_dir.join(name)) {
            bases.push((name.clone(), source));
        }
    }
    assert!(
        bases.len() > 16,
        "the differential leg only found {} base programs — cases/ vanished?",
        bases.len()
    );

    let mut accepted = 0usize;
    for (label, source) in &bases {
        match (compile_with(source, true), compile_with(source, false)) {
            (Ok(on), Ok(off)) => {
                accepted += 1;
                assert_eq!(
                    on, off,
                    "walk pins changed the emitted IR for {label} — the subset discipline broke"
                );
            }
            (Err((stage_on, diags_on)), Err((stage_off, diags_off))) => {
                assert_eq!(
                    stage_on.name(),
                    stage_off.name(),
                    "walk pins changed the rejecting stage for {label}"
                );
                assert_eq!(
                    diags_on, diags_off,
                    "walk pins changed the diagnostics for {label} — the subset discipline broke"
                );
            }
            (on, off) => {
                panic!(
                    "walk pins flipped acceptance for {label}:\n  pins on : {}\n  pins off: {}",
                    match &on {
                        Ok(_) => "accepted".to_string(),
                        Err((s, d)) => format!("{}: {}", s.name(), diags_text(d)),
                    },
                    match &off {
                        Ok(_) => "accepted".to_string(),
                        Err((s, d)) => format!("{}: {}", s.name(), diags_text(d)),
                    }
                );
            }
        }
    }
    assert!(
        accepted >= 10,
        "only {accepted}/{} differential bases reached the lowerer — the accepted leg \
         was never exercised",
        bases.len()
    );
    eprintln!(
        "walk-pin differential: {} bases, {accepted} accepted (byte-identical .ll)",
        bases.len()
    );
}
