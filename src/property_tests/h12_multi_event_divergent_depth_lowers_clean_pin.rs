/// H12 7b-prep — the divergent twin of the equal-depth pin: the same
/// multi-event shape (one shared body, two events over one pair)
/// whose events' absolute bases DIVERGE by a loop, through the FULL
/// pipeline. The 7a sentinel watches by MEMBERSHIP — the lowering
/// event's own base is always among the pair's minted events (same
/// walk, same order), so per-event divergence never false-fires —
/// and the lowerer's own stacks are correct-by-construction, so this
/// program lowers clean today. 7b's ordered cursor must keep it green
/// while reading records instead of stacks; the analysis-side facts
/// of the divergence live in h12_break_base_is_per_event_pin.
#[test]
fn h12_multi_event_divergent_depth_lowers_clean_pin() {
    let source = "\
local t = { [0] = 7 }
local acc = 0
local function H()
    local m
    acc = acc + 1
    return t[0]
end
local function G()
    return H()
end
local function F()
    local q
    local a = G()
    local n = 0
    while n < 9 do
        n = n + 1
        local c = G()
    end
    return a
end
local z
F()
";
    let ll = compile(source).unwrap_or_else(|(stage, diags)| {
        panic!(
            "the divergent-depth multi-event program must lower clean at {}: {}",
            stage.name(),
            diags_text(&diags)
        )
    });
    assert!(
        !ll.contains("@alm_tbl_get_any"),
        "the Int table's reads stay scalar through the divergent extents"
    );
}
