
/// Generated programs compile clean and stay elem-congruent: one elem
/// truth, decided once, consumed by the ctor AND every access face.
#[test]
fn generated_programs_keep_one_elem_truth() {
    const SEED: u64 = 0x2026_1021;
    const PROGRAMS: usize = 400;
    let mut rng = Rng::new(SEED);
    let mut any_expected = 0usize;
    let mut bool_expected = 0usize;

    for _ in 0..PROGRAMS {
        let (source, expected) = gen_program(&mut rng);
        any_expected += usize::from(expected.is_any());
        bool_expected += usize::from(expected == Elem::Bool);
        match compile(&source) {
            Ok(ll) => assert_elem_congruence(&ll, expected, "generated program"),
            Err((stage, diags)) => panic!(
                "{}",
                report(
                    &source,
                    expected,
                    format!(
                        "valid-by-construction program was rejected at {}: {}",
                        stage.name(),
                        diags_text(&diags)
                    ),
                )
            ),
        }
    }

    // Two-sided distribution bounds: must exercise both Any adoption AND
    // homogeneous scalar lifecycles (including 1-byte Bool tables).
    assert!(
        (PROGRAMS / 4..=PROGRAMS * 3 / 4).contains(&any_expected),
        "skewed Elem::Any distribution: {any_expected}/{PROGRAMS} generated programs \
         expected Any (expected between 25% and 75%)"
    );
    assert!(
        bool_expected >= PROGRAMS / 20,
        "only {bool_expected}/{PROGRAMS} generated programs stayed homogeneous Elem::Bool \
         (esize 1 path under-exercised)"
    );
    eprintln!(
        "property coverage: any_expected={any_expected}/{PROGRAMS} \
         bool_expected={bool_expected}/{PROGRAMS}"
    );
}
