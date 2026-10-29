
/// The fuzz sweep: fresh seeds beyond the pinned one — the property must
/// not hold only for the flagship seed's sample. Same congruence oracle,
/// looser aggregate distribution bounds (per-seed balance is already
/// pinned by the flagship leg).
#[test]
fn generator_sweep_survives_fresh_seeds() {
    const SEEDS: u64 = 32;
    const PROGRAMS_PER_SEED: usize = 125;
    let mut any_expected = 0usize;
    let mut bool_expected = 0usize;
    let mut total = 0usize;

    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x5EED_0000 ^ (seed << 32) ^ seed);
        for _ in 0..PROGRAMS_PER_SEED {
            let (source, expected) = gen_program(&mut rng);
            any_expected += usize::from(expected.is_any());
            bool_expected += usize::from(expected == Elem::Bool);
            total += 1;
            match compile(&source) {
                Ok(ll) => {
                    assert_elem_congruence(&ll, expected, &format!("seed sweep (seed {seed})"))
                }
                Err((stage, diags)) => panic!(
                    "{}",
                    report(
                        &source,
                        expected,
                        format!(
                            "valid-by-construction program (sweep seed {seed}) was rejected \
                             at {}: {}",
                            stage.name(),
                            diags_text(&diags)
                        ),
                    )
                ),
            }
        }
    }

    assert_eq!(total, SEEDS as usize * PROGRAMS_PER_SEED);
    assert!(
        any_expected >= total / 8,
        "sweep never exercised Any adoption: {any_expected}/{total}"
    );
    assert!(
        bool_expected >= total / 20,
        "sweep under-exercised the esize-1 Bool path: {bool_expected}/{total}"
    );
    eprintln!(
        "seed sweep coverage: any_expected={any_expected}/{total} \
         bool_expected={bool_expected}/{total}"
    );
}
