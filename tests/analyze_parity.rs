//! The walk-tier parity leg vs the frozen mirror oracle (the
//! FRONT_REFUSALS pattern, continued at the Analyze boundary): the
//! corpus is the specification, and the rebuilt mirror release binary
//! at 87aca4c is the oracle it runs against.
//!
//! Three frozen catalogs classify every front-clean case (release vs
//! release, modulo the sanctioned ALM_TRACE poke lines):
//!
//! - `WALK_REFUSALS` (61): both compilers refuse; the FIRST
//!   diagnostic is byte-identical (walk-tier truth — the full stderr
//!   may carry checker-tier trailing lines mirror also prints).
//! - `CHECKER_OWNED` (61): mirror's first failure is
//!   checker-tier; alm's walk accepts or diverges — **L4's acceptance
//!   bar** (the checker ports until this catalog is empty).
//! - `CHECKER_MEDIATED` (9): mirror ACCEPTS because its
//!   interleaved checker unifies the site unknowns before
//!   `check_row_reads` resolves them (`lat.unify(&elem, &val_ty)` in
//!   the checker's IndexAssign arm); alm's walk-only pass fires the
//!   row-read diagnostic — **L4 retires these**.
//!
//! The hard law: mirror accepts => alm accepts, except the mediated
//! nine; and alm never refuses outside the catalogs (drift tripwire).

mod common;

use alm::pipeline::analyze_stage;
use alm::source::SourceFile;
use common::{cases_dir, collect_lua_files, is_front_refusal, module_root, surface_flags_of};
use std::path::PathBuf;
use std::process::Command;

pub const WALK_REFUSALS: &[&str] = &[
    "01_pin_direct_move.lua",
    "02_pin_carrier_move.lua",
    "03_pin_transitive_move.lua",
    "04_pin_bare_return_taint.lua",
    "05_pin_deep_pass_through.lua",
    "09_pin_ctor_entry_move.lua",
    "10_pin_assignment_move.lua",
    "11_pin_self_nest.lua",
    "12_pin_transitive_mover_chain.lua",
    "13_pin_deep_chain_depth3.lua",
    "14_pin_positional_remap.lua",
    "34_pin_row_store_refused.lua",
    "40_pin_row_cycle_refused.lua",
    "41_pin_row_boundary_store_refused.lua",
    "42_pin_row_claimed_read_refused.lua",
    "any_store_table_neg.lua",
    "bare_local_nil_use_rejected.lua",
    "bare_local_print_unbound_ir_fail.lua",
    "borrow_escape_store_rejected.lua",
    "ctor_expr_key_reads_rejected.lua",
    "ctor_nested_shape_neg.lua",
    "ctor_scalar_table_mix_rejected.lua",
    "cyclic_store_mutual_rejected.lua",
    "cyclic_store_rejected.lua",
    "do_exit_alias_survives_rejected.lua",
    "escape_self_capture_rejected.lua",
    "exprkey_const_bounds_rejected.lua",
    "fn_break_boundary_rejected.lua",
    "if_arm_borrow_conflict_rejected.lua",
    "index_base1_claimed_read_refused.lua",
    "index_base1_cycle_refused.lua",
    "index_base1_row_housing_conflict.lua",
    "len_string_scalar_rejected.lua",
    "line_number_pin.lua",
    "alpha.lua",
    "beta.lua",
    "moved_in_loop_rejected.lua",
    "moved_twice_rejected.lua",
    "move_poisoning_rejected.lua",
    "move_read_rejected.lua",
    "named_ctor_row_pending_rejected.lua",
    "nested_alias_row_read_before_value_rejected.lua",
    "nested_alias_row_store_link_rejected.lua",
    "nested_null_child_store_silent.lua",
    "nested_row_read_before_value_rejected.lua",
    "rebind_shape_conflict_neg.lua",
    "require_bit_rejected.lua",
    "require_cycle_rejected.lua",
    "require_missing_module_rejected.lua",
    "require_no_return_rejected.lua",
    "require_not_top_level_rejected.lua",
    "require_selfref_rejected.lua",
    "shape_errors.lua",
    "three_deep_pierce_rejected.lua",
    "tuple_alias_move_rejected.lua",
    "tuple_name_double_move_rejected.lua",
    "tuple_name_pinned_arg_rejected.lua",
    "tuple_name_undeclared_rejected.lua",
    "tuple_row_swap_rejected.lua",
    "tuple_same_table_rejected.lua",
    "while_body_borrow_conflict_rejected.lua",
];

pub const CHECKER_OWNED: &[&str] = &[
    "22_interop_panic_div_zero.lua",
    "any_adopt_key_neg.lua",
    "any_adopt_read_neg.lua",
    "args_any_len_int_panic.lua",
    "args_any_len_str.lua",
    "args_bool_int_reject.lua",
    "args_boundary_death.lua",
    "args_key_conflict.lua",
    "args_mixed_reject.lua",
    "assert_fail_msg.lua",
    "async_resume_invalid_panics.lua",
    "async_yield_drain_word_panics.lua",
    "boundary_lane_mixed_store_rejected.lua",
    "boundary_lane_str_dispatch_rejected.lua",
    "concat_reject_mixed.lua",
    "ctor_expr_key_type_rejected.lua",
    "cyclic_ctor_assign_rejected.lua",
    "div_zero_runtime_error.lua",
    "error_raises.lua",
    "error_value_position_rejected.lua",
    "escape_block_local_dispatch_rejected.lua",
    "escape_cond_mint_rejected.lua",
    "escape_face_extract_bare_assign_rejected.lua",
    "escape_face_extract_rejected.lua",
    "escape_face_extract_scope_rejected.lua",
    "escape_monomorphic_divergent_rejected.lua",
    "escape_no_crossing.lua",
    "escape_record_bool_field_rejected.lua",
    "escape_record_table_field_rejected.lua",
    "ffi_cdef_malformed.lua",
    "ffi_cdef_nonliteral_string.lua",
    "ffi_new_negative_capacity.lua",
    "ffi_new_nonliteral_capacity.lua",
    "ffi_new_struct_elem.lua",
    "ffi_new_unknown_name.lua",
    "ffi_sizeof_unknown_name.lua",
    "ffi_so_load_refused.lua",
    "ffi_static_key_over_capacity.lua",
    "fill_reserve_huge_bound_panic.lua",
    "fill_reserve_offset_wrap_panic.lua",
    "fixed_math_monomorphic_rejected.lua",
    "fn_monomorphic_return_rejected.lua",
    "fn_mutual_recursion_rejected.lua",
    "fn_not_a_function_one_prefix.lua",
    "fn_param_shadow_rejected.lua",
    "fn_valueless_call_rejected.lua",
    "fn_value_print_rejected.lua",
    "fn_value_table_rejected.lua",
    "index_nontable_rejected.lua",
    "len_defer_pin_neg.lua",
    "counter.lua",
    "counter.lua",
    "nested_fill_nil_row_store_runtime_error.lua",
    "nested_oob_row_store_runtime_error.lua",
    "null_host_inner_fill_base1_inclusive_panic.lua",
    "null_host_inner_fill_base1_panic.lua",
    "rebind_scalar_conflict_rejected.lua",
    "rebind_scalar_table_cross_rejected.lua",
    "redecl_same_scope_rejected.lua",
    "tuple_displace_wip.lua",
    "type_errors.lua",
];

pub const CHECKER_MEDIATED: &[&str] = &[
    "cross_arm_row_adoption.lua",
    "ctor_expr_keys_tables.lua",
    "ctor_nested.lua",
    "nested_alias_row_decided.lua",
    "nested_fill_ctor_row_reserve.lua",
    "nested_fill_minted_rows.lua",
    "nested_inner_first_touch_sizing.lua",
    "nested_shapes.lua",
    "soundness_edge_gauntlet.lua",
];

fn mirror_binary() -> PathBuf {
    let p = cases_dir()
        .parent()
        .expect("corpus root has a parent")
        .join("target/release/alm");
    assert!(
        p.exists(),
        "the frozen oracle is missing — rebuild it:          (cd ../mirror_experimental && cargo build --release)"
    );
    p
}

/// mirror's verdict: (accepted, first filtered stderr line).
fn mirror_run(binary: &PathBuf, case: &PathBuf, flags: &[String]) -> (bool, String) {
    // The oracle writes its build artifacts (alm_out*, .alm_rt_trace)
    // into its working directory — run it from a scratch dir so the
    // alm tree stays clean.
    let scratch = std::env::temp_dir().join("alm_l3_parity_scratch");
    std::fs::create_dir_all(&scratch).expect("scratch dir");
    let out = Command::new(binary)
        .args(flags)
        .arg(format!("--module-root={}", module_root().display()))
        .arg(case)
        .current_dir(&scratch)
        .output()
        .expect("the oracle binary runs");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let first = stderr
        .lines()
        .find(|l| !l.starts_with("ALM_TRACE:"))
        .unwrap_or_default()
        .to_string();
    (out.status.success(), first)
}

/// alm's walk verdict: (accepted, first diagnostic line).
fn alm_walk(name: &str, text: &str) -> (bool, String) {
    let name = name.to_string();
    let text = text.to_string();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let surface = surface_flags_of(&text);
            let src = SourceFile::new(name, text);
            let root = module_root();
            match analyze_stage(&src, &surface, Some(&root), true) {
                Ok(_) => (true, String::new()),
                Err((_stage, diags)) => {
                    let first = diags.first().map(|d| d.render()).unwrap_or_default();
                    (false, first)
                }
            }
        })
        .expect("spawn parity thread")
        .join()
        .expect("parity thread panicked")
}

fn case_flags(text: &str) -> Vec<String> {
    text.lines()
        .find_map(|l| l.strip_prefix("-- FLAGS:"))
        .map(|rest| rest.split_whitespace().map(str::to_string).collect())
        .unwrap_or_default()
}

#[test]
fn walk_tier_parity_against_the_frozen_oracle() {
    let binary = mirror_binary();

    let mut files = Vec::new();
    collect_lua_files(&cases_dir(), &mut files);
    files.sort();
    assert!(files.len() >= 449, "corpus pool shrank: {}", files.len());

    let mut both_accept = 0usize;
    let mut walk_tier = 0usize;
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
        let (m_ok, m_first) = mirror_run(&binary, path, &case_flags(&text));
        let (a_ok, a_first) = alm_walk(&name, &text);

        if m_ok {
            if a_ok {
                both_accept += 1;
            } else if CHECKER_MEDIATED.contains(&name.as_str()) {
                // the documented shape: a walk-tier refusal the checker
                // retires (all nine carry the row-read diagnostic)
                assert!(
                    a_first.starts_with("line ")
                        && a_first.contains("Type Error: a row of")
                        && a_first.contains("is read before it is ever given a value"),
                    "{name} left the mediated shape: {a_first}"
                );
            } else {
                panic!(
                    "the walk over-rejects {name} — mirror accepts:
  alm: {a_first}"
                );
            }
        } else if a_ok {
            assert!(
                CHECKER_OWNED.contains(&name.as_str()),
                "{name} accepted where the oracle refuses — uncatalogued divergence                  (mirror: {m_first})"
            );
        } else {
            assert!(
                WALK_REFUSALS.contains(&name.as_str()) || CHECKER_OWNED.contains(&name.as_str()),
                "{name} refuses outside every catalog — drift                  (mirror: {m_first}; alm: {a_first})"
            );
            if WALK_REFUSALS.contains(&name.as_str()) {
                walk_tier += 1;
                assert_eq!(
                    m_first, a_first,
                    "{name}: the walk-tier first diagnostic drifted from the oracle"
                );
            }
        }
    }
    assert!(
        both_accept >= 250,
        "the accepted pool shrank: {both_accept}"
    );
    assert_eq!(
        walk_tier,
        WALK_REFUSALS.len(),
        "a walk-tier case went missing"
    );
    eprintln!(
        "parity: {both_accept} both-accept, {walk_tier} walk-tier byte-exact,          {} checker-owned, {} checker-mediated (L4's ledger)",
        CHECKER_OWNED.len(),
        CHECKER_MEDIATED.len()
    );
}
