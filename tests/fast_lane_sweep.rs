//! The fast-lane corpus sweep (L5's port of mirror's
//! `fast_lane_facts_hold_over_the_corpus`): over the whole corpus,
//! every fast store's loop carries a reserve plan, and the lane facts
//! are a pure function of the source (two analyses of one file
//! project the same lane shape). mirror's leg drives the parser +
//! analyzer directly at base 0 — no splice, no FLAGS — and this port
//! keeps that law (the walk-pins lever is on, mirror's `analyze_with`
//! default).

mod common;

use alm::analysis::build_context;
use alm::pipeline::front;
use alm::shape::ShapeFacts;
use alm::source::SourceFile;
use alm::surface::Surface;
use common::{cases_dir, collect_lua_files};

/// One analysis run on the sweep thread: base-0 parse + walk, None for
/// any rejection (parse diagnostics, analysis diagnostics, panic).
fn analyze(source: String) -> Option<ShapeFacts> {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let surface = Surface::default();
                let src = SourceFile::new("sweep.lua", source);
                let out = front(&src, &surface);
                if !out.diagnostics.is_empty() {
                    return None;
                }
                let ctx = build_context(&out.ast);
                let facts = alm::shape::analyze(&ctx, true, &surface);
                facts.diagnostics.is_empty().then_some(facts)
            }));
            caught.ok().flatten()
        })
        .expect("spawn sweep thread")
        .join()
        .unwrap_or(None)
}

// NodeIds are minted in parse order, so the fact maps iterate in
// source order and the projection is comparable across two runs.
/// The store projection: (table, row_reserve) per minted fact.
type LaneStores = Vec<(String, bool)>;
/// The plan projection: (pre-header, nested, ctor-reserve count) per
/// plan.
type LanePlans = Vec<(Vec<String>, Vec<String>, usize)>;

fn lane_shape(f: &ShapeFacts) -> (LaneStores, LanePlans) {
    let stores = f
        .fast_stores
        .values()
        .map(|e| (e.table.clone(), e.row_reserve))
        .collect();
    let plans = f
        .reserve_plans
        .values()
        .map(|p| {
            (
                p.pre_header.clone(),
                p.nested.clone(),
                p.ctor_reserves.len(),
            )
        })
        .collect();
    (stores, plans)
}

#[test]
fn fast_lane_facts_hold_over_the_corpus() {
    let mut files = Vec::new();
    collect_lua_files(&cases_dir(), &mut files);
    assert!(
        files.len() > 400,
        "the corpus pool did not load — only {} files",
        files.len()
    );

    let mut analyzed = 0usize;
    let mut total_stores = 0usize;
    let mut total_plans = 0usize;
    for path in files {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_string();
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{} unreadable: {e}", path.display()));
        let Some(facts) = analyze(text.clone()) else {
            continue;
        };
        analyzed += 1;
        for elig in facts.fast_stores.values() {
            assert!(
                facts.reserve_plans.contains_key(&elig.loop_id),
                "{name}: a fast store's loop carries no reserve plan"
            );
        }
        let again = analyze(text)
            .unwrap_or_else(|| panic!("{name}: the second analysis run rejected the source"));
        assert_eq!(
            lane_shape(&facts),
            lane_shape(&again),
            "{name}: the fast-lane facts are not a pure function of the source"
        );
        total_stores += facts.fast_stores.len();
        total_plans += facts.reserve_plans.len();
    }
    assert!(
        analyzed > 100,
        "only {analyzed} corpus cases reached analysis"
    );
    assert!(
        total_stores >= 20 && total_plans >= 10,
        "the corpus fast lane collapsed: {total_stores} stores over {total_plans} plans"
    );
    eprintln!(
        "fast-lane corpus pin: {analyzed} analyzed, {total_stores} stores, {total_plans} plans"
    );
}
