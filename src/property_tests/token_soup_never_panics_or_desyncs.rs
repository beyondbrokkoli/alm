
/// The pipeline from a pre-lexed token stream — the token-soup fuzz leg
/// feeds mutated token vectors in here directly (offsets stay valid
/// byte indices of the same source, so diagnostics remain sound).
fn compile_tokenized(
    source: &str,
    tokens: Vec<(lexer::Token<'_>, usize)>,
) -> Result<String, (Stage, Vec<Diagnostic>)> {
    compile_tokenized_with(source, tokens, true)
}

/// Token-level soup fuzz: mutate the token STREAM (delete, duplicate a
/// short run, swap neighbors) of valid programs — generated samples and
/// every buildable corpus case — and run the whole pipeline on the
/// result. Soup is free to be invalid syntax or invalid types, but the
/// two invariants of the harness must hold at this granularity too:
/// the compiler must never panic, and whatever the checker accepts must
/// lower and render clean. Edits are bounded (≤ 4 per mutant, runs
/// duplicated ≤ 3 tokens) so nesting depth cannot run away.
#[test]
fn token_soup_never_panics_or_desyncs() {
    // bases: fresh generated programs + the buildable corpus
    let mut bases: Vec<(String, String)> = Vec::new(); // (label, source)
    let mut rng = Rng::new(0x5050_5EED);
    for i in 0..16 {
        let (source, _) = gen_program(&mut rng);
        bases.push((format!("generated#{i}"), source));
    }
    let cases_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("cases");
    if let Ok(entries) = std::fs::read_dir(&cases_dir) {
        let mut names: Vec<String> = entries
            .flatten()
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| n.ends_with(".lua"))
            .collect();
        names.sort();
        for name in names {
            if let Ok(source) = std::fs::read_to_string(cases_dir.join(&name))
                && compile(&source).is_ok()
            {
                bases.push((name, source));
            }
        }
    }
    assert!(
        bases.len() >= 16,
        "token soup only found {} base programs — cases/ vanished?",
        bases.len()
    );

    const MUTANTS_PER_BASE: usize = 20;
    let mut exercised = 0usize;
    let mut accepted = 0usize;
    for (label, source) in &bases {
        let mut toks: Vec<(lexer::Token<'_>, usize)> = Vec::new();
        let mut lex = lexer::Token::lexer(source);
        while let Some(Ok(t)) = lex.next() {
            toks.push((t, lex.span().start));
        }
        if toks.is_empty() {
            continue;
        }
        let mut rng = Rng::new(fnv1a(label.as_bytes()));
        for _ in 0..MUTANTS_PER_BASE {
            let edits = 1 + rng.below(4);
            let mut soup = toks.clone();
            for _ in 0..edits {
                if soup.is_empty() {
                    break;
                }
                let at = rng.below(soup.len());
                match rng.below(3) {
                    0 => {
                        soup.remove(at);
                    }
                    1 => {
                        let run = 1 + rng.below(3.min(soup.len() - at));
                        let dup: Vec<(lexer::Token<'_>, usize)> = soup[at..at + run].to_vec();
                        for (k, t) in dup.into_iter().enumerate() {
                            soup.insert(at + k, t);
                        }
                    }
                    _ => {
                        if at + 1 < soup.len() {
                            soup.swap(at, at + 1);
                        }
                    }
                }
            }
            if soup.is_empty() {
                continue;
            }
            exercised += 1;
            match compile_tokenized(source, soup.clone()) {
                Ok(_) => accepted += 1,
                Err((stage, diags))
                    if matches!(stage, Stage::Panicked | Stage::Lower | Stage::Backend) =>
                {
                    let desyncs: Vec<Diagnostic> =
                        diags.iter().filter(|d| d.is_desync()).cloned().collect();
                    let crime = match stage {
                        Stage::Panicked => "the compiler crashed on token soup",
                        _ => "checker-accepted token soup reached a walk desync",
                    };
                    panic!(
                        "{crime} — base {label} failed at {}\ndiagnostics: {}\n\
                         desync-class: {}\nsoup (Debug tokens):\n{}\nbase:\n{}",
                        stage.name(),
                        diags_text(&diags),
                        if desyncs.is_empty() {
                            "no".to_string()
                        } else {
                            diags_text(&desyncs)
                        },
                        soup.iter()
                            .map(|(t, _)| format!("  {t:?}"))
                            .collect::<Vec<_>>()
                            .join("\n"),
                        indent(source),
                    );
                }
                Err(_) => {
                    // Rejected by Front or Analyze — soup is free to be invalid.
                }
            }
        }
    }
    assert!(
        exercised >= 400,
        "token soup only exercised {exercised} mutants — the base pool dried up"
    );
    assert!(
        accepted >= 10,
        "0/{exercised} soup mutants compiled — the accepted leg of the implication \
         was never exercised"
    );
    eprintln!(
        "token soup coverage: bases={} exercised={exercised} accepted={accepted}",
        bases.len()
    );
}
