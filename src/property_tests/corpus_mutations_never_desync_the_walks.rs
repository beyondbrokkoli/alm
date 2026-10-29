
/// Corpus mutation: structural edits of every buildable corpus case
/// must keep the walks in sync — a mutant may be rejected by any stage
/// (mutations are free to break validity), but whatever the CHECKER
/// accepts must lower and render clean. A checker-accepted program with
/// lowerer/backend diagnostics is exactly the walk-desync class, with
/// `LowerError::is_desync` naming the known faces of it.
#[test]
fn corpus_mutations_never_desync_the_walks() {
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

    const PER_OP: usize = 3;
    let mut checked = 0usize;
    let mut analyzer_accepted = 0usize;

    for name in &names {
        let path = cases_dir.join(name);
        let Ok(original) = std::fs::read_to_string(&path) else {
            continue;
        };
        // a case that does not build in-process (e.g. exe-only policy
        // in main.rs) cannot discriminate mutation-caused failures
        if compile(&original).is_err() {
            continue;
        }
        let lines: Vec<&str> = original.lines().collect();
        let eligible: Vec<usize> = lines
            .iter()
            .enumerate()
            .filter(|(_, l)| {
                let t = l.trim();
                !t.is_empty() && !t.starts_with("--")
            })
            .map(|(i, _)| i)
            .collect();
        if eligible.is_empty() {
            continue;
        }
        let mut rng = Rng::new(fnv1a(name.as_bytes()));
        for op in 0..3 {
            for _ in 0..PER_OP {
                let i = eligible[rng.below(eligible.len())];
                let mutant: Vec<&str> = match op {
                    0 => {
                        let mut m = lines.clone();
                        m.remove(i.min(m.len() - 1));
                        m
                    }
                    1 => {
                        let mut m = lines.clone();
                        let at = i.min(m.len());
                        m.insert(at, lines[i]);
                        m
                    }
                    _ => {
                        let mut m = lines.clone();
                        if i + 1 < m.len() {
                            m.swap(i, i + 1);
                        }
                        m
                    }
                };
                let mutant = mutant.join("\n");
                match compile(&mutant) {
                    Ok(_) => {
                        analyzer_accepted += 1;
                    }
                    Err((stage, diags))
                        if matches!(stage, Stage::Panicked | Stage::Lower | Stage::Backend) =>
                    {
                        let desyncs: Vec<Diagnostic> =
                            diags.iter().filter(|d| d.is_desync()).cloned().collect();
                        let crime = match stage {
                            Stage::Panicked => "the compiler crashed",
                            _ => "checker-accepted mutant reached a walk desync",
                        };
                        panic!(
                            "{crime} — mutant of {} failed at {}\n\
                             mutation: op {op} at line {}\ndiagnostics: \
                             {}\ndesync-class: {}\nmutant:\n{}",
                            path.display(),
                            stage.name(),
                            i + 1,
                            diags_text(&diags),
                            if desyncs.is_empty() {
                                "no".to_string()
                            } else {
                                diags_text(&desyncs)
                            },
                            indent(&mutant),
                        );
                    }
                    Err(_) => {
                        // Rejected by Front or Analyze — expected for invalid syntax/types.
                    }
                }
                checked += 1;
            }
        }
    }
    assert!(
        checked >= 22,
        "corpus mutation leg only exercised {checked} mutants — \
         the corpus shrank below one round"
    );
    assert!(
        analyzer_accepted >= 1,
        "0/{checked} corpus mutants survived Stage::Analyze — the lowerer/backend \
         implication was never actually exercised"
    );
    eprintln!("corpus mutation coverage: checked={checked} analyzer_accepted={analyzer_accepted}");
}
