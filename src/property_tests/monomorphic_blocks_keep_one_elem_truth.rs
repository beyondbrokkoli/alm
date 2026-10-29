/// H12 7b-prep — multi-block fuzz leg: independent monomorphic table
/// blocks (one name owns one elem kind per block) ridden through the
/// FULL pipeline, expansions included — the emitted `.ll` must stay
/// scalar (never `@alm_tbl_get_any`) and every block must compile
/// clean. The every-compile shadow, the identity census, and the 7a
/// sentinel ride all 50 compiles; a multi-block program exercises
/// independent facts under one walk where the single-table generator
/// legs emit one table per program.
#[test]
fn monomorphic_blocks_keep_one_elem_truth() {
    const SEED: u64 = 0xCAFE_BABE_2026;
    let mut rng = Rng::new(SEED);

    // Types kept strictly monomorphic inside each block
    let types = [Elem::Int, Elem::Flt, Elem::Bool];

    for iteration in 0..50 {
        let mut script_lines = Vec::new();
        let num_blocks = 2 + rng.below(4);

        for block_idx in 0..num_blocks {
            let elem = types[rng.below(types.len())];
            let lit0 = elem.lit(&mut rng);
            let lit1 = elem.lit(&mut rng);

            // an isolated block with a depth-2 inlined lookup
            script_lines.push("do".to_string());
            script_lines.push(format!(
                "  local tbl_{block_idx} = {{ [0] = {lit0}, [1] = {lit1} }}"
            ));
            script_lines.push(format!(
                "  local idx_map_{block_idx} = {{ [0] = 0, [1] = 1 }}"
            ));
            script_lines.push(format!("  local function Fetch_{block_idx}(k)"));
            script_lines.push(format!(
                "    return tbl_{block_idx}[idx_map_{block_idx}[k]]"
            ));
            script_lines.push("  end".to_string());
            script_lines.push(format!("  local function Wrap_{block_idx}(k)"));
            script_lines.push(format!("    return Fetch_{block_idx}(k)"));
            script_lines.push("  end".to_string());
            script_lines.push(format!("  print(Wrap_{block_idx}(0))"));
            script_lines.push("end".to_string());
        }

        let full_program = script_lines.join("\n") + "\n";

        // full pipeline — analyze_with's shadow assert rides every
        // compile; a panic surfaces as Stage::Panicked and fails here
        match compile(&full_program) {
            Ok(ll) => {
                assert!(
                    !ll.contains("@alm_tbl_get_any"),
                    "iteration {iteration}: monomorphic blocks degraded to Any\n{full_program}"
                );
            }
            Err((stage, diags)) => {
                panic!(
                    "iteration {iteration}: valid monomorphic blocks rejected \
                     at {}: {}\n{full_program}",
                    stage.name(),
                    diags_text(&diags)
                );
            }
        }
    }
}
