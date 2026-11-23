//! The fast-lane property pins (L5's port of mirror's
//! `fast_lane_facts_pin.rs`): the lane's admission laws pinned on
//! hand-built conversion loops — the group, poison, row-stored, depth,
//! and offset families, with their base-1 twins. The two helper-law
//! pins (`const_key_value`, `guard_key_shape`) live beside the helpers
//! as unit tests (pub(crate) seams).

use alm::analysis::build_context;
use alm::ast::{CtorKey, Expr, NodeId, Stmt};
use alm::shape::KeyShape;
use alm::source::SourceFile;
use alm::surface::{Flag, Surface};

fn surface_with_base(index_base: i64) -> Surface {
    let mut surface = Surface::default();
    Flag::parse(&format!("--index-base={index_base}"))
        .expect("the pins use legal flags only")
        .apply(&mut surface);
    surface
}

fn lane_facts(source: &str) -> Result<(Vec<Stmt>, alm::shape::ShapeFacts), String> {
    lane_facts_base(source, 0)
}

/// The base-1 twin of `lane_facts`: the parser mints shifted Consts and
/// the analyzer folds guard offsets and reads keys in physical space,
/// exactly as the pipeline threads the surface flag.
fn lane_facts_base(
    source: &str,
    index_base: i64,
) -> Result<(Vec<Stmt>, alm::shape::ShapeFacts), String> {
    let surface = surface_with_base(index_base);
    let src = SourceFile::new("pin.lua", source);
    let out = alm::pipeline::front(&src, &surface);
    if !out.diagnostics.is_empty() {
        return Err(out
            .diagnostics
            .iter()
            .map(|d| d.render())
            .collect::<Vec<_>>()
            .join("\n"));
    }
    let ctx = build_context(&out.ast);
    let facts = alm::shape::analyze(&ctx, true, &surface);
    if !facts.diagnostics.is_empty() {
        return Err(facts
            .diagnostics
            .iter()
            .map(|d| d.render())
            .collect::<Vec<_>>()
            .join("\n"));
    }
    Ok((out.ast, facts))
}

/// The corpus statement order is the NodeId mint order, so an
/// IndexAssign's position in this list is its position in the source.
fn store_sites(stmts: &[Stmt], out: &mut Vec<(NodeId, String)>) {
    fn base_of(e: &Expr) -> String {
        match e {
            Expr::Identifier { name, .. } => name.clone(),
            Expr::Index { obj, .. } => base_of(obj),
            _ => "<expr>".to_string(),
        }
    }
    fn walk_expr(e: &Expr, out: &mut Vec<(NodeId, String)>) {
        match e {
            Expr::Function { body, .. } => store_sites(body, out),
            Expr::TableCtor { entries, .. } => {
                for (k, v) in entries {
                    if let CtorKey::Expr(ke) = k {
                        walk_expr(ke, out);
                    }
                    walk_expr(v, out);
                }
            }
            _ => {}
        }
    }
    for s in stmts {
        match s {
            Stmt::IndexAssign { obj, .. } => {
                out.push((s.id(), base_of(obj)));
            }
            Stmt::While {
                condition, body, ..
            } => {
                walk_expr(condition, out);
                store_sites(body, out);
            }
            Stmt::Do { body, .. } => store_sites(body, out),
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                walk_expr(condition, out);
                store_sites(then_body, out);
                store_sites(else_body, out);
            }
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
                for e in exprs {
                    walk_expr(e, out);
                }
            }
            Stmt::Assignment { expr, .. } | Stmt::Expr { expr, .. } => walk_expr(expr, out),
            Stmt::Return { value: Some(e), .. } => walk_expr(e, out),
            _ => {}
        }
    }
}

fn expect_lane(
    source: &str,
    want_stores: &[(&str, bool, KeyShape)],
    want_plans: &[(&[&str], &[&str], Option<i64>)],
) {
    expect_lane_base(source, 0, want_stores, want_plans);
}

fn expect_lane_base(
    source: &str,
    index_base: i64,
    want_stores: &[(&str, bool, KeyShape)],
    want_plans: &[(&[&str], &[&str], Option<i64>)],
) {
    let (ast, facts) = lane_facts_base(source, index_base)
        .unwrap_or_else(|e| panic!("lane pin source rejected: {e}"));
    let mut sites = Vec::new();
    store_sites(&ast, &mut sites);
    let mut got: Vec<(String, bool, KeyShape)> = Vec::new();
    for (id, base) in &sites {
        if let Some(elig) = facts.fast_stores.get(id) {
            got.push((elig.table.clone(), elig.row_reserve, elig.key));
            assert_eq!(
                elig.table, *base,
                "the fact's table name must be the store's base name"
            );
            assert!(
                facts.reserve_plans.contains_key(&elig.loop_id),
                "a fast store's loop carries no reserve plan"
            );
        }
    }
    let want: Vec<(String, bool, KeyShape)> = want_stores
        .iter()
        .map(|(t, r, k)| (t.to_string(), *r, *k))
        .collect();
    assert_eq!(
        got, want,
        "fast-store facts diverged from the pinned lane shape"
    );
    let mut plans: Vec<(Vec<String>, Vec<String>, Option<i64>)> = facts
        .reserve_plans
        .values()
        .map(|p| (p.pre_header.clone(), p.nested.clone(), p.key_offset))
        .collect();
    plans.sort();
    let want_plans: Vec<(Vec<String>, Vec<String>, Option<i64>)> = want_plans
        .iter()
        .map(|(pre, nested, max_k)| {
            (
                pre.iter().map(|s| s.to_string()).collect(),
                nested.iter().map(|s| s.to_string()).collect(),
                *max_k,
            )
        })
        .collect();
    assert_eq!(
        plans, want_plans,
        "reserve plans diverged from the pinned shape"
    );
}

#[test]
fn fast_lane_facts_pin_guard_fill_rides_the_lane() {
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 8 do\n\
         \x20 t[i] = i\n\
         \x20 i = i + 1\n\
         end\n",
        &[("t", false, KeyShape::Guard)],
        &[(&["t"], &[], Some(0))],
    );
}

#[test]
fn fast_lane_facts_pin_compound_host_stays_checked() {
    // The nested claim's host law: `t[0]`'s read is a runtime slot the
    // plan never proved live, so the store keeps the checked face,
    // whose null arm speaks the null-row-store guard. The plan itself
    // still holds the nested name (the row the store would mint is the
    // recognizer's business), while no admitted store means no widest
    // offset for the loop's reserves.
    expect_lane(
        "local t = {{}}\n\
         local i = 0\n\
         while i < 2 do\n\
         \x20 t[0][i] = i\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&[], &["t"], None)],
    );
}

#[test]
fn fast_lane_facts_pin_same_slot_repeat_stays_checked() {
    // The claim law: one fast fact per (loop, base, key). The second
    // store rewrites the first's slot — a replace — so it keeps the
    // checked face, where set_core's replace-reclaim frees the
    // displaced child; only the first sighting rides the lane.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 2 do\n\
         \x20 t[i] = { { i } }\n\
         \x20 t[i] = { { i + 1 } }\n\
         \x20 i = i + 1\n\
         end\n",
        &[("t", false, KeyShape::Guard)],
        &[(&["t"], &["t"], Some(0))],
    );
}

#[test]
fn fast_lane_facts_pin_two_shapes_one_group_collapse_forward() {
    // The group law (post-P23 fix): distinct key shapes over one
    // (loop, base) — `t[i]` and `t[i+1]` — overlap across trips (at
    // trip i, slot i then slot i+1; at trip i+1, slot i+1 again), so
    // the whole group falls to the checked face: the first sighting's
    // mint revokes, nothing remains in `fast_stores`, and the plan
    // widens nothing.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 t[i] = i\n\
         \x20 t[i+1] = i\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &[], None)],
    );
}

#[test]
fn fast_lane_facts_pin_two_shapes_one_group_collapse_backward() {
    // The backward-order twin: `t[i+1]` sighted first (its mint
    // admitted at 0 + 1) collapses when `t[i]` arrives — same group
    // verdict, zero fast facts, the plan keeps None.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 t[i+1] = i\n\
         \x20 t[i] = i\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &[], None)],
    );
}

#[test]
fn fast_lane_facts_pin_unanalyzable_sibling_collapses_the_mint() {
    // The poison service: a store whose key resolves under no key
    // shape (`t[i * 2]`) writes unprovable slots at runtime, so the
    // group that minted earlier in the walk is collapsed — its fact
    // unclaims — and any sighting the walk reaches after that rides
    // the checked face.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 t[i] = i\n\
         \x20 t[i * 2] = i\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &[], None)],
    );
}

#[test]
fn fast_lane_facts_pin_unanalyzable_store_poisons_sightings_that_come_later() {
    // The poison service covers the mint-less first sighting too: the
    // group is born dead when the shapeless store is seen, so the
    // resolvable sighting after it never mints.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 t[i * 2] = i\n\
         \x20 t[i] = i\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &[], None)],
    );
}

#[test]
fn fast_lane_facts_pin_compound_host_sibling_poisons_nothing() {
    // `t[i][0] = v` writes inside a row's cells, never `t`'s own
    // slots: the poison service skips compound hosts, so the
    // guard-keyed constructor store's mint stays claimed.
    let source = "local t = {}\n\
                  local i = 0\n\
                  while i < 2 do\n\
                  \x20 t[i] = {}\n\
                  \x20 t[i][0] = i + 3\n\
                  \x20 i = i + 1\n\
                  end\n";
    let (ast, facts) = lane_facts(source).unwrap();
    let mut sites = Vec::new();
    store_sites(&ast, &mut sites);
    assert_eq!(sites.len(), 2, "the golden carries two stores");
    assert!(
        facts.fast_stores.contains_key(&sites[0].0),
        "the guard-keyed constructor store rides the lane"
    );
    assert!(
        !facts.fast_stores.contains_key(&sites[1].0),
        "the compound-host row store stays checked"
    );
}

#[test]
fn fast_lane_facts_pin_sequential_scalar_fills_stay_claimed() {
    // The cells-hold-one-kind law: replacing a scalar needs no
    // reclaim, so two sequential integer fills on one binding keep
    // riding the lane — the row-stored set never sees them.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 t[i] = i\n\
         \x20 i = i + 1\n\
         end\n\
         local j = 3\n\
         while j < 6 do\n\
         \x20 t[j] = j\n\
         \x20 j = j + 1\n\
         end\n",
        &[("t", false, KeyShape::Guard), ("t", false, KeyShape::Guard)],
        &[(&["t"], &[], Some(0)), (&["t"], &[], Some(0))],
    );
}

#[test]
fn fast_lane_facts_pin_second_row_fill_widens_nothing() {
    // The row-stored law: the first loop's constructor store leaves
    // rows behind it, so the second loop's row store is not proven a
    // fresh slot — it keeps the checked face and the plan widens
    // nothing. The first mint stays (its slots were fresh).
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 2 do\n\
         \x20 t[i] = {}\n\
         \x20 i = i + 1\n\
         end\n\
         local j = 2\n\
         while j < 4 do\n\
         \x20 t[j] = {}\n\
         \x20 j = j + 1\n\
         end\n",
        &[("t", false, KeyShape::Guard)],
        &[(&["t"], &["t"], None), (&["t"], &["t"], Some(0))],
    );
}

#[test]
fn fast_lane_facts_pin_nested_scalar_store_claims_row_stays_checked() {
    // The depth law, split by value kind. A scalar claim re-runs once
    // per enclosing trip and replaces a scalar word wherever it lands
    // — the cells-hold-one-kind law forbids rows on a scalar binding,
    // so nothing needs reclaiming at any depth: the store rides the
    // lane under its own loop's... the frame it resolves under (the
    // outer guard) — the claim books into the outer group and mints.
    // The row-kind twin keeps the checked face: its slots are the
    // enclosing trips' rows, reclaim territory the plan never minted.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 2 do\n\
         \x20 local j = 0\n\
         \x20 while j < 2 do\n\
         \x20   t[i] = j\n\
         \x20   j = j + 1\n\
         \x20 end\n\
         \x20 i = i + 1\n\
         end\n",
        &[("t", false, KeyShape::Guard)],
        &[(&["t"], &[], Some(0))],
    );
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 2 do\n\
         \x20 local j = 0\n\
         \x20 while j < 2 do\n\
         \x20   t[i] = { { j } }\n\
         \x20   j = j + 1\n\
         \x20 end\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &["t"], None)],
    );
}

#[test]
fn fast_lane_facts_pin_ctor_value_under_a_fill_borrows_the_bound() {
    let source = "local t = {}\n\
                  local i = 0\n\
                  while i < 2 do\n\
                  \x20 t[i] = {}\n\
                  \x20 t[i][0] = i + 3\n\
                  \x20 i = i + 1\n\
                  end\n";
    let (ast, facts) = lane_facts(source).unwrap();
    let mut sites = Vec::new();
    store_sites(&ast, &mut sites);
    assert_eq!(sites.len(), 2, "the golden carries two stores");
    assert!(
        facts.fast_stores.contains_key(&sites[0].0),
        "the guard-keyed constructor store rides the lane"
    );
    assert!(
        !facts.fast_stores.contains_key(&sites[1].0),
        "the literal-keyed row store stays checked"
    );
    let plan = facts
        .reserve_plans
        .values()
        .next()
        .expect("the loop carries a reserve plan");
    assert_eq!(plan.pre_header, vec!["t".to_string()]);
    assert_eq!(plan.nested, vec!["t".to_string()]);
    assert_eq!(
        plan.ctor_reserves,
        std::collections::BTreeSet::from_iter([sites[0].0]),
        "the constructor value's reserve rides its store, keyed by NodeId"
    );
}

#[test]
fn fast_lane_facts_pin_guard_rebind_declines_later_stores() {
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 4 do\n\
         \x20 t[i] = i\n\
         \x20 if i == 1 then\n\
         \x20   i = i + 2\n\
         \x20 end\n\
         \x20 t[i] = i\n\
         \x20 i = i + 1\n\
         end\n",
        &[("t", false, KeyShape::Guard)],
        &[(&["t"], &[], Some(0))],
    );
}

#[test]
fn fast_lane_facts_pin_store_after_the_increment_declines() {
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 i = i + 1\n\
         \x20 t[i] = i\n\
         end\n",
        &[],
        &[(&["t"], &[], None)],
    );
}

#[test]
fn fast_lane_facts_pin_guard_shadow_scopes_to_its_block() {
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 do\n\
         \x20   local i = 9\n\
         \x20   t[i] = i\n\
         \x20 end\n\
         \x20 t[i] = i\n\
         \x20 i = i + 1\n\
         end\n",
        &[("t", false, KeyShape::Guard)],
        &[(&["t"], &[], Some(0))],
    );
}

#[test]
fn fast_lane_facts_pin_offset_key_rides_with_a_constant_entry() {
    // Tight reserves: the plan carries the signed offset (-1), not the
    // old `max(K, 0)` clamp, so the reserve is `bound - 1` cells and
    // the border equals the stored span.
    expect_lane(
        "local t = {}\n\
         local j = 1\n\
         while j < 9 do\n\
         \x20 t[j-1] = j - 1\n\
         \x20 j = j + 1\n\
         end\n",
        &[("t", false, KeyShape::GuardOffset(-1))],
        &[(&["t"], &[], Some(-1))],
    );
}

#[test]
fn fast_lane_facts_pin_zero_start_offset_declines() {
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 t[i-1] = i + 4\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &[], None)],
    );
}

#[test]
fn fast_lane_facts_pin_positive_offset_widens_the_reserve() {
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 t[i+1] = i * 3\n\
         \x20 i = i + 1\n\
         end\n",
        &[("t", false, KeyShape::GuardOffset(1))],
        &[(&["t"], &[], Some(1))],
    );
}

#[test]
fn fast_lane_facts_pin_offset_without_a_constant_entry_admits_through_the_entry_bound() {
    // `2 * 2` is provably nonnegative (the loop converts) and is not
    // a literal, so the exact constant is unknown — but the plan's
    // minted entry bound (the product's floor 4) re-proves the first
    // key: 4 + 1 >= 0, so the store rides the lane and the plan
    // carries the claimed offset.
    expect_lane(
        "local t = {}\n\
         local i = 2 * 2\n\
         while i < 6 do\n\
         \x20 t[i+1] = i * 3\n\
         \x20 i = i + 1\n\
         end\n",
        &[("t", false, KeyShape::GuardOffset(1))],
        &[(&["t"], &[], Some(1))],
    );
}

#[test]
fn fast_lane_facts_pin_base1_bare_guard_folds_and_tightens() {
    // Under base 1 the bare guard key t[i] is a physical offset key of
    // -1: the gate re-proves at entry 1 (1 - 1 = 0 >= 0) and the plan
    // carries the signed -1, so the reserve is bound - 1 cells.
    expect_lane_base(
        "local t = {}\n\
         local i = 1\n\
         while i < 9 do\n\
         \x20 t[i] = i\n\
         \x20 i = i + 1\n\
         end\n",
        1,
        &[("t", false, KeyShape::Guard)],
        &[(&["t"], &[], Some(-1))],
    );
}

#[test]
fn fast_lane_facts_pin_base1_zero_start_declines_the_lane() {
    // A zero-start fill under base 1 has a negative first physical key
    // (0 - 1 = -1), so the admission gate declines the fast lane; the
    // declined store contributes no offset and the plan keeps None
    // (the reserve stays at the raw bound).
    expect_lane_base(
        "local t = {}\n\
         local i = 0\n\
         while i < 8 do\n\
         \x20 t[i] = i\n\
         \x20 i = i + 1\n\
         end\n",
        1,
        &[],
        &[(&["t"], &[], None)],
    );
}

#[test]
fn fast_lane_facts_pin_var_chain_entry_admits_through_the_plan_bound() {
    // The Var-chain spelling the placeholder era declined: `i`'s entry
    // has no exact constant (ConstEnv records only Integer inits), but
    // the plan mints the entry bound from the same num_assigns its
    // nonneg gate read — start holds Lit 1, so lb(i) = 1 and the bare
    // guard's first physical key 1 - 1 = 0 admits under base 1.
    let source = "local start = 1\n\
                  local t = {}\n\
                  local i = start\n\
                  while i < 9 do\n\
                  \x20 t[i] = i\n\
                  \x20 i = i + 1\n\
                  end\n";
    let (ast, facts) = lane_facts_base(source, 1).unwrap();
    let mut sites = Vec::new();
    store_sites(&ast, &mut sites);
    assert_eq!(
        facts.fast_stores.len(),
        1,
        "the bare-guard fill rides the lane through the plan bound"
    );
    let plan = facts
        .reserve_plans
        .values()
        .next()
        .expect("the loop carries a reserve plan");
    assert_eq!(
        plan.entry_lb,
        Some(1),
        "the Var chain's floor is the entry bound"
    );
    assert_eq!(
        plan.key_offset,
        Some(-1),
        "the claimed physical offset is -1"
    );
}

#[test]
fn fast_lane_facts_pin_if_join_entry_admits_through_the_plan_bound() {
    // An if-join entry: the walk appends both arms' assignment shapes
    // to the declaration's, so the bound is the minimum over every
    // recorded shape — the arms' lows (1 and 2) — and the base-1 bare
    // guard admits exactly as the Var-chain spelling does. A stale
    // high decl (3) does not loosen the floor.
    let source = "local t = {}\n\
                  local start = 3\n\
                  if 0 < 1 then\n\
                  \x20 start = 1\n\
                  else\n\
                  \x20 start = 2\n\
                  end\n\
                  local i = start\n\
                  while i < 9 do\n\
                  \x20 t[i] = i\n\
                  \x20 i = i + 1\n\
                  end\n";
    let (ast, facts) = lane_facts_base(source, 1).unwrap();
    let mut sites = Vec::new();
    store_sites(&ast, &mut sites);
    assert_eq!(
        facts.fast_stores.len(),
        1,
        "the if-join entry re-proves the first key through the bound"
    );
    let plan = facts
        .reserve_plans
        .values()
        .next()
        .expect("the loop carries a reserve plan");
    assert_eq!(
        plan.entry_lb,
        Some(1),
        "the arms' minimum is the entry bound"
    );
    assert_eq!(
        plan.key_offset,
        Some(-1),
        "the claimed physical offset is -1"
    );
}

#[test]
fn fast_lane_facts_pin_base1_offset_folds_at_recognition() {
    // The user offset +2 folds to physical +1 at recognition; the gate
    // proves entry 1 lands at 2 >= 0 and the reserve widens by the
    // folded value, not the spelled one.
    expect_lane_base(
        "local t = {}\n\
         local i = 1\n\
         while i < 9 do\n\
         \x20 t[i+2] = i\n\
         \x20 i = i + 1\n\
         end\n",
        1,
        &[("t", false, KeyShape::GuardOffset(1))],
        &[(&["t"], &[], Some(1))],
    );
}

#[test]
fn fast_lane_facts_pin_mintless_sibling_shape_collapses_the_group() {
    // The group law holds even when no earlier sighting minted: the
    // inner loop's `t[i+1]` books its shape into the outer group and
    // the depth law declines its mint (loop_depth 2), but the store
    // still runs once per outer trip — the checked face — writing
    // slot i + 1. A `t[i]` mint at the outer level would land its
    // fast window on slots the checked shape already filled (at trip
    // 1, slot 1 holds trip 0's `t[i+1]` store). The distinct shape
    // collapses the group instead: zero fast facts, the plan widens
    // nothing. Scalars keep the example inside one cell kind; the law
    // is about the shape pair, not the value kind.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 2 do\n\
         \x20 local j = 0\n\
         \x20 while j < 2 do\n\
         \x20   t[i + 1] = j + 7\n\
         \x20   j = j + 1\n\
         \x20 end\n\
         \x20 t[i] = i + 3\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &[], None)],
    );
}

#[test]
fn fast_lane_facts_pin_depth_declined_sibling_shape_collapses_the_group() {
    // The nesting twin: the inner loop's `t[i+1]` books its shape into
    // the outer group and the depth law declines its mint (loop_depth
    // 2), but the store still runs — the checked face — once per outer
    // trip, writing slot i + 1. The outer `t[i]`'s mint would clobber
    // those slots at trip 1 onward; the distinct shape collapses.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 2 do\n\
         \x20 local j = 0\n\
         \x20 while j < 2 do\n\
         \x20   t[i + 1] = { { j } }\n\
         \x20   j = j + 1\n\
         \x20 end\n\
         \x20 t[i] = { { i } }\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &["t"], None)],
    );
}

#[test]
fn fast_lane_facts_pin_identifier_row_store_marks_the_base() {
    // The row-kind law reads the walk's Tbl-value fact, not the ctor
    // spelling: loop 1's `t[i] = r` moves rows into fresh slots and
    // keeps the lane (its slots were fresh), and it marks the base —
    // so loop 2's row store is not proven a fresh slot and keeps the
    // checked face, whose replace-reclaim frees loop 1's displaced
    // rows. The syntactic-only check missed both markings.
    expect_lane(
        "local t = {}\n\
         local i = 0\n\
         while i < 2 do\n\
         \x20 local r = { { i } }\n\
         \x20 t[i] = r\n\
         \x20 i = i + 1\n\
         end\n\
         local j = 2\n\
         while j < 4 do\n\
         \x20 t[j] = { { j } }\n\
         \x20 j = j + 1\n\
         end\n",
        &[("t", false, KeyShape::Guard)],
        &[(&["t"], &["t"], None), (&["t"], &["t"], Some(0))],
    );
}

#[test]
fn fast_lane_facts_pin_pre_loop_identifier_row_store_declines_the_lane() {
    // The pre-loop twin of the marking law: `t[0] = r` moves a row
    // into slot 0 before the loop — no ctor anywhere — and the
    // fail-closed marking at the mint-less path records the base, so
    // the conversion loop's row store keeps the checked face instead
    // of clobbering slot 0 with no reclaim face in between.
    expect_lane(
        "local t = {}\n\
         local r = { { 9 } }\n\
         t[0] = r\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 t[i] = { { i } }\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &["t"], None)],
    );
}

#[test]
fn fast_lane_facts_pin_pre_populated_ctor_declines_the_lane() {
    // The literal twin of the marking law: `local t = { {} }` houses a
    // row at slot 0 at construction time — a LocalDecl, never an
    // IndexAssign, so the store-side marking never sees it. A decl
    // whose init is not a provably empty fresh table marks the base
    // fail-closed, and the fill loop's row store keeps the checked
    // face instead of clobbering the constructor's row with no
    // reclaim face in between.
    expect_lane(
        "local t = { {} }\n\
         local i = 0\n\
         while i < 3 do\n\
         \x20 t[i] = { { i } }\n\
         \x20 i = i + 1\n\
         end\n",
        &[],
        &[(&["t"], &["t"], None)],
    );
}
