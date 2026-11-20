//! The walk goldens (the §3.3.2 golden ladder's L3 rung): every
//! front-clean corpus case's `--dump-shape` output, frozen. L4's
//! checker ports splice against this diff surface — drift shows up as
//! a diff, not a hunch. Bless with `ALM_BLESS=1 cargo test --test
//! walk_goldens`.

mod common;

use alm::pipeline::analyze_stage;
use alm::source::SourceFile;
use common::{cases_dir, collect_lua_files, is_front_refusal, module_root, surface_flags_of};
use std::path::{Path, PathBuf};

fn goldens_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/goldens/shape")
}

/// The golden name mirrors the parse goldens' convention, nested one
/// level for the module fixtures.
fn golden_rel_path(case: &Path) -> PathBuf {
    let rel = case
        .strip_prefix(cases_dir())
        .expect("case lives under the corpus root");
    let mut rel = rel.to_path_buf();
    rel.set_extension("lua.txt");
    rel
}

#[test]
fn walk_goldens_freeze_the_corpus() {
    let bless = std::env::var("ALM_BLESS").is_ok();
    let mut files = Vec::new();
    collect_lua_files(&cases_dir(), &mut files);
    files.sort();

    let mut frozen = 0usize;
    let mut refusals = 0usize;
    for path in &files {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_string();
        if is_front_refusal(&name) {
            continue;
        }
        let text =
            std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));

        let dump = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn({
                let path = path.display().to_string();
                let text = text.clone();
                move || {
                    let surface = surface_flags_of(&text);
                    let src = SourceFile::new(path, text);
                    let root = module_root();
                    match analyze_stage(&src, &surface, Some(&root), true) {
                        // A walk refusal still dumps — the diagnostics
                        // section is part of the frozen surface. Front
                        // and Modules refusals have no walk to freeze;
                        // their parity lives in the analyze-parity leg.
                        Err((alm::pipeline::Stage::Front | alm::pipeline::Stage::Modules, _)) => {
                            None
                        }
                        Ok(out) => Some(alm::dump::render_shape(&out.facts, &out.ast)),
                        Err((_, diags)) => Some(format!(
                            "diagnostics:\n{}",
                            diags
                                .iter()
                                .map(|d| format!("  {}", d.render()))
                                .collect::<Vec<_>>()
                                .join("\n")
                        )),
                    }
                }
            })
            .expect("spawn golden thread")
            .join()
            .expect("golden thread panicked");

        let Some(dump) = dump else {
            refusals += 1;
            continue;
        };
        let golden = goldens_dir().join(golden_rel_path(path));
        if bless {
            std::fs::create_dir_all(golden.parent().expect("golden has a parent")).unwrap();
            std::fs::write(&golden, &dump).unwrap();
            frozen += 1;
        } else {
            let want = std::fs::read_to_string(&golden)
                .unwrap_or_else(|e| panic!("{} missing/unreadable: {e}", golden.display()));
            assert_eq!(
                want,
                dump,
                "walk drift on {} — re-bless only if the change is the point",
                path.display()
            );
            frozen += 1;
        }
    }
    assert!(
        frozen + refusals > 300,
        "the golden pool came up short: {frozen} frozen, {refusals} pre-walk refusals"
    );
    if bless {
        eprintln!("walk goldens: blessed {frozen} files ({refusals} pre-walk refusals)");
    }
}
