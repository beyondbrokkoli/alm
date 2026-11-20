//! The mutation sweep (L3's port of mirror's
//! `corpus_mutations_never_desync_the_walks`): deterministic line
//! mutations of every corpus case that compiles; a mutant may be
//! accepted or refused at any stage, but the compiler never crashes.
//! (L7 receipt: mirror's invariant also fails the leg when a
//! checker-accepted mutant dies at Lower/Backend — those stages do not
//! exist yet, so the invariant here reduces to never-`Panicked`; the
//! stage arms extend with the lowerer.)

mod common;

use common::{Rng, analyze_with_lever, cases_dir, collect_lua_files, fnv1a};

#[test]
fn corpus_mutations_never_desync_the_walks() {
    const PER_OP: usize = 3;
    let mut checked = 0usize;
    let mut walk_accepted = 0usize;

    let mut files = Vec::new();
    collect_lua_files(&cases_dir(), &mut files);
    files.sort();

    for path in &files {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_string();
        let original = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("{} unreadable: {e}", path.display()));
        if !analyze_with_lever(name.clone(), original.clone(), true).is_ok() {
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
                match analyze_with_lever(name.clone(), mutant.clone(), true) {
                    Ok(_) => {
                        walk_accepted += 1;
                    }
                    Err((stage, diags)) => {
                        if matches!(stage, alm::pipeline::Stage::Panicked) {
                            panic!(
                                "the compiler crashed — mutant of {name}\n\
                                 mutation: op {op} at line {}\ndiagnostics: \
                                 {diags}\nmutant:\n{}",
                                i + 1,
                                indent(&mutant),
                            );
                        }
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
        walk_accepted >= 1,
        "0/{checked} corpus mutants survived the walk — the accepted \
         leg was never actually exercised"
    );
    eprintln!("corpus mutation coverage: checked={checked} walk_accepted={walk_accepted}");
}

fn indent(text: &str) -> String {
    text.lines()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}
