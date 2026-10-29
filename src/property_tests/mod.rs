//! Property harness for the desync class. The ctor's physical allocation
//! (`TableNew` esize + elem-kind flags byte) and every access face come
//! from ONE decision; this harness turns any regression of that
//! unification into a CI signal without linking or running anything:
//!
//! 1. valid-by-construction single-table programs (the generator below)
//!    must compile clean end to end, and the emitted `.ll` must be
//!    elem-congruent — every `alm_tbl_new` esize/kind, the any/scalar
//!    family of every `alm_tbl_get*`/`alm_tbl_set*` call, the trailing
//!    cell size on scalar `alm_tbl_get` calls, and the LLVM storage type
//!    of every scalar cell seam (`%ts*.dst`/`%ts*.valp` alloca) must
//!    match the oracle's expected element type — Int/Flt/Bool/Str are
//!    verified beyond esize: the flags byte names the kind, the seams
//!    name the repr (i64/double/i8/ptr), and Any programs must carry NO
//!    scalar cell seams at all (i128 register faces only);
//! 2. checker-accepted ⇒ lowerer clean: a program that survives the
//!    checker must never produce a lowerer (or backend) diagnostic —
//!    that implication is the walk-desync definition, checked over the
//!    whole corpus under structural mutation AND over token-level soup
//!    of generated + corpus programs (the fuzz legs);
//! 3. the C≡Rust str-key ABI identity: every interned string's prefix
//!    key (written by str_pool.c's FNV-1a-62 derive) must equal the
//!    Rust mirror `str_key_of_bytes` for random strings and every
//!    string literal in the corpus.
//!
//! The oracle is the documented name-global join law (README "Tables
//! unify to Any on mixed assignments"; the nil-slot law): the element
//! discipline of a name is the flow-insensitive join of every scalar
//! kind ever witnessed into it — through ctor entries, stores, and
//! rebinds, across `t = nil`, inside loops and both arms of every
//! branch — where two distinct kinds join to Any.
//!
//! Every program the generator emits owns exactly ONE table name, so
//! module-global face counting in the `.ll` is a sound congruence
//! oracle: the only `alm_tbl_new` calls are that name's ctors.

use crate::analysis;
use crate::ast::{BinOp, Expr, NodeId, Stmt};
use crate::diag::Diagnostic;
use crate::lexer;
use crate::parser::Parser;
use crate::pipeline::{self, PipelineOpts, Stage};
use logos::Logos;
use std::panic::AssertUnwindSafe;
use std::path::Path;

// ---- deterministic rng (xorshift64*) — no crate dep, fixed seeds ----

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed | 1)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// Unbiased upper-bit range reduction via 128-bit fixed-point multiply.
    fn below(&mut self, n: usize) -> usize {
        debug_assert!(n > 0, "Rng::below called with n == 0");
        ((u128::from(self.next()) * u128::from(n as u64)) >> 64) as usize
    }
}

fn fnv1a(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

// ---- the in-process pipeline (the ONE pipeline, H10: the harness
// drives the same walk the driver does — src/pipeline.rs — minus
// clang/host; only the catch_unwind wrappers and the opts live here) ---

/// The harness's fixed opts: `standalone: false` keeps EntryKind at Lib
/// (the artifact bytes are exactly the pre-fold harness's) and thereby
/// runs the ffi gate — the surfaced drift this fold exists to name: an
/// ffi program now rejects in-process, as it always did in the driver's
/// .so mode. `source_file` stays "property_case.lua".
fn property_opts(walk_pins: bool) -> PipelineOpts {
    PipelineOpts {
        standalone: false,
        source_file: "property_case.lua".into(),
        walk_pins,
    }
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "unknown panic".into())
}

/// The failure-report face of the format law: rendered diagnostics,
/// joined for assert messages only (the pins compare full renders).
fn diags_text(diags: &[Diagnostic]) -> String {
    diags
        .iter()
        .map(|d| d.render())
        .collect::<Vec<_>>()
        .join("; ")
}

/// Runs the full compile pipeline on `source` and returns the `.ll`
/// text, or the stage that rejected it with its diagnostics. Panics
/// inside a phase are caught and reported as their own stage — the
/// compiler must diagnose, never crash.
fn compile(source: &str) -> Result<String, (Stage, Vec<Diagnostic>)> {
    compile_with(source, true)
}

/// The differential leg's entry (the pin-owed register, census §3
/// cluster A): `walk_pins = false` routes the analyzer with its
/// use-site pins disarmed, so only the checker's own land — the subset
/// discipline's A/B leg.
fn compile_with(source: &str, walk_pins: bool) -> Result<String, (Stage, Vec<Diagnostic>)> {
    match std::panic::catch_unwind(AssertUnwindSafe(|| {
        pipeline::compile(source, &property_opts(walk_pins))
    })) {
        Ok(r) => r,
        Err(payload) => Err((
            Stage::Panicked,
            vec![Diagnostic::bare(format!(
                "panic: {}",
                panic_message(payload)
            ))],
        )),
    }
}

/// The exe-opts leg: the ffi surface is legal standalone, so probes of
/// it reach the TYPE discipline at analysis instead of the packaging
/// gate (their .so-opts twin rejects at `Stage::Ffi`).
fn compile_exe(source: &str) -> Result<String, (Stage, Vec<Diagnostic>)> {
    match std::panic::catch_unwind(AssertUnwindSafe(|| {
        pipeline::compile(
            source,
            &PipelineOpts {
                standalone: true,
                source_file: "property_case.lua".into(),
                walk_pins: true,
            },
        )
    })) {
        Ok(r) => r,
        Err(payload) => Err((
            Stage::Panicked,
            vec![Diagnostic::bare(format!(
                "panic: {}",
                panic_message(payload)
            ))],
        )),
    }
}

fn compile_tokenized_with(
    source: &str,
    tokens: Vec<(lexer::Token<'_>, usize)>,
    walk_pins: bool,
) -> Result<String, (Stage, Vec<Diagnostic>)> {
    match std::panic::catch_unwind(AssertUnwindSafe(|| {
        pipeline::compile_parts(tokens, source, &property_opts(walk_pins))
    })) {
        Ok(r) => r,
        Err(payload) => Err((
            Stage::Panicked,
            vec![Diagnostic::bare(format!(
                "panic: {}",
                panic_message(payload)
            ))],
        )),
    }
}

// ---- the oracle: the name-global element join law ----

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Elem {
    Int,
    Flt,
    Bool,
    Str,
    Any,
}

impl Elem {
    /// The physical cell size `TableNew` must allocate (`elem_size`).
    fn esize(self) -> u64 {
        match self {
            Elem::Bool => 1,
            Elem::Any => 16,
            _ => 8,
        }
    }

    /// The elem-kind field of the `TableNew` flags byte — bits 1..=3,
    /// `kind << 1` (rt.rs's ctor packs `((kind as u8) & 0x07) << 1`).
    /// Int=0, Flt=2, Bool=4, Str=6, Any=8 — verified against the
    /// backend's emission for every kind.
    fn kind_flag(self) -> u8 {
        match self {
            Elem::Int => 0,
            Elem::Flt => 2,
            Elem::Bool => 4,
            Elem::Str => 6,
            Elem::Any => 8,
        }
    }

    /// The LLVM storage type of the scalar cell seam slots (the
    /// backend's `Repr::storage()`); Any has none — its cells ride
    /// i128 register faces end to end.
    fn storage(self) -> Option<&'static str> {
        match self {
            Elem::Int => Some("i64"),
            Elem::Flt => Some("double"),
            Elem::Bool => Some("i8"),
            Elem::Str => Some("ptr"),
            Elem::Any => None,
        }
    }

    fn is_any(self) -> bool {
        self == Elem::Any
    }

    /// The adoption join: same kind stays, two distinct scalars go Any.
    fn join(self, other: Elem) -> Elem {
        if self == other { self } else { Elem::Any }
    }

    fn lit(self, rng: &mut Rng) -> &'static str {
        match self {
            Elem::Int => ["3", "7"][rng.below(2)],
            Elem::Flt => ["2.5", "0.5"][rng.below(2)],
            Elem::Bool => ["true", "false"][rng.below(2)],
            Elem::Str => ["\"s\"", "\"w\""][rng.below(2)],
            Elem::Any => unreachable!("literals are per-kind, Any only arises by joining"),
        }
    }
}

/// A random kind for a literal witness (Any never appears as a literal).
fn witness_kind(rng: &mut Rng) -> Elem {
    [Elem::Int, Elem::Flt, Elem::Bool, Elem::Str][rng.below(4)]
}

/// Picks a witness kind under the program's homogeneity policy: when
/// `locked` is `Some(k)`, all witnesses in the program stick to `k` so
/// homogeneous tables (`Int`, `Flt`, `Bool`, `Str`) survive across
/// multi-rebind lifecycles without collapsing into `Elem::Any`.
fn pick_witness_kind(rng: &mut Rng, locked: Option<Elem>) -> Elem {
    locked.unwrap_or_else(|| witness_kind(rng))
}

fn record_witness(kind: Elem, elem: &mut Option<Elem>) {
    *elem = Some(match *elem {
        Some(e) => e.join(kind),
        None => kind,
    });
}

/// Names the expected elem for failure messages.
fn elem_name(elem: Elem) -> &'static str {
    match elem {
        Elem::Int => "Int",
        Elem::Flt => "Flt",
        Elem::Bool => "Bool",
        Elem::Str => "Str",
        Elem::Any => "Any",
    }
}

// ---- the generator: one table name, valid by construction ----

/// Emits one small program over the single table name `t` and the elem
/// the join law predicts for it.
///
/// Coverage invariants:
/// - ~45% of programs lock onto a single scalar kind (`locked = Some(k)`)
///   so homogeneous multi-rebind and `Bool` (esize 1) paths are heavily
///   exercised instead of collapsing to `Elem::Any` on the second store.
/// - Opening declaration can be either a non-empty ctor (`local t = {...}`)
///   or an empty ctor (`local t = {}`) immediately followed by a witnessing
///   store before any read, testing retroactive esize patching on the
///   initial declaration.
/// - Control flow (`if`/`else`, `do` blocks, `for`, `while`+`break`)
///   wraps not only stores and reads, but also plain rebinds (`t = {...}`)
///   and nil-severed rebinds (`t = nil` followed immediately by
///   `t = {...}` within the same block). The join is flow-insensitive,
///   so never-taken arms and `while false` bodies still witness.
fn gen_program(rng: &mut Rng) -> (String, Elem) {
    let mut elem: Option<Elem> = None;
    let mut lines: Vec<String> = Vec::new();

    // Lock ~45% of generated programs to a single homogeneous scalar kind.
    let locked: Option<Elem> = if rng.below(20) < 9 {
        Some(witness_kind(rng))
    } else {
        None
    };

    // Opening declaration: 20% empty ctor + immediate witness store, 80% non-empty ctor.
    if rng.below(5) == 0 {
        lines.push("local t = {}".to_string());
        let k0 = pick_witness_kind(rng, locked);
        record_witness(k0, &mut elem);
        lines.push(format!("t[{}] = {}", rng.below(8), k0.lit(rng)));
    } else {
        let mixed = locked.is_none() && rng.below(4) == 0;
        let n = 1 + rng.below(2);
        let k0 = pick_witness_kind(rng, locked);
        let entries: Vec<String> = (0..n)
            .map(|i| {
                let k = if mixed && i == 1 {
                    pick_witness_kind(rng, locked)
                } else {
                    k0
                };
                record_witness(k, &mut elem);
                k.lit(rng).to_string()
            })
            .collect();
        lines.push(format!("local t = {{{}}}", entries.join(", ")));
    }

    let stmts = 2 + rng.below(6);
    for _ in 0..stmts {
        match rng.below(11) {
            0 => {
                let k = pick_witness_kind(rng, locked);
                record_witness(k, &mut elem);
                lines.push(format!("t[{}] = {}", rng.below(8), k.lit(rng)));
            }
            1 | 2 => lines.push(format!("print(t[{}])", rng.below(8))),
            3 => lines.push("print(#t)".to_string()),
            4 | 5 => {
                lines.push(ctor_line(rng, locked, &mut elem));
            }
            6 => {
                lines.push("t = nil".to_string());
                lines.push(ctor_line(rng, locked, &mut elem));
            }
            7 => {
                // Single-branch `if` or `do` wrapping stores, reads, rebinds, or nil-severs.
                let body = branch_body(rng, locked, &mut elem);
                if rng.below(2) == 0 {
                    let cond = ["true", "false"][rng.below(2)];
                    lines.push(format!("if {cond} then\n{body}\nend"));
                } else {
                    lines.push(format!("do\n{body}\nend"));
                }
            }
            8 | 9 => {
                // Two-way `if ... else ... end` where both arms may rebind, nil-sever, or store.
                let cond = ["true", "false"][rng.below(2)];
                let then_body = branch_body(rng, locked, &mut elem);
                let else_body = branch_body(rng, locked, &mut elem);
                lines.push(format!(
                    "if {cond} then\n{then_body}\nelse\n{else_body}\nend"
                ));
            }
            _ => {
                // Loops: `for` over the loop index, and `while`+`break`
                // in a plain while (the corpus's every break sits inside
                // a `for`; this arm keeps the plain-while shape on the
                // board). Static conditions stay legal — the join is
                // flow-insensitive, `while false` bodies still witness.
                let bound = 2 + rng.below(4);
                match rng.below(3) {
                    0 => {
                        let k = pick_witness_kind(rng, locked);
                        record_witness(k, &mut elem);
                        lines.push(format!(
                            "for i = 0, {bound} do\n  t[i] = {}\nend",
                            k.lit(rng)
                        ));
                    }
                    1 => lines.push(format!("for i = 0, {bound} do\n  print(t[i])\nend")),
                    _ => {
                        let k = pick_witness_kind(rng, locked);
                        record_witness(k, &mut elem);
                        let cond = ["true", "false"][rng.below(2)];
                        lines.push(format!(
                            "while {cond} do\n  t[{}] = {}\n  break\nend",
                            rng.below(8),
                            k.lit(rng)
                        ));
                    }
                }
            }
        }
    }

    // A final read guarantees at least one access face in the artifact.
    lines.push(format!("print(t[{}])", rng.below(8)));

    (
        lines.join("\n") + "\n",
        elem.expect("the opening sequence always witnesses at least one kind"),
    )
}

/// Generates a block-safe statement sequence for inside an `if`, `else`, or
/// `do` body. Any `t = nil` is immediately paired with a rebind inside the
/// same block so `t` is always live on block exit.
fn branch_body(rng: &mut Rng, locked: Option<Elem>, elem: &mut Option<Elem>) -> String {
    match rng.below(4) {
        0 => {
            let k = pick_witness_kind(rng, locked);
            record_witness(k, elem);
            format!("t[{}] = {}", rng.below(8), k.lit(rng))
        }
        1 => format!("print(t[{}])", rng.below(8)),
        2 => ctor_line(rng, locked, elem),
        _ => {
            let rebind = ctor_line(rng, locked, elem);
            format!("t = nil\n{rebind}")
        }
    }
}

/// One rebind ctor: empty (`{}`), single-kind, or mixed.
fn ctor_line(rng: &mut Rng, locked: Option<Elem>, elem: &mut Option<Elem>) -> String {
    let n = rng.below(3);
    if n == 0 {
        return "t = {}".to_string();
    }
    let k0 = pick_witness_kind(rng, locked);
    let entries: Vec<String> = (0..n)
        .map(|i| {
            let k = if i == 1 && locked.is_none() && rng.below(2) == 0 {
                pick_witness_kind(rng, locked)
            } else {
                k0
            };
            record_witness(k, elem);
            k.lit(rng).to_string()
        })
        .collect();
    format!("t = {{{}}}", entries.join(", "))
}

// ---- the congruence oracle over the .ll text ----

/// Every `alm_tbl_new` must allocate the expected elem's cell size AND
/// name the expected elem kind in its flags byte; every table access
/// face must belong to the expected family (`_any` iff Any); scalar
/// `alm_tbl_get` calls must carry the expected trailing cell size; and
/// every scalar cell seam alloca must use the expected storage type
/// (Any programs must carry no scalar seams at all) — the ctor/access
/// congruence whose violation is the §2 bug class (an esize-8 header
/// under any-cell faces dies at runtime with "no register cell face";
/// the reverse mix misreads silently; an Int/Flt confusion behind one
/// esize is exactly as silent and is what the seam/flag checks catch).
fn assert_elem_congruence(ll: &str, expected: Elem, context: &str) {
    let mut news = 0usize;
    let mut accesses = 0usize;
    let mut seams = 0usize;
    for line in ll.lines() {
        if line.contains("ptrtoint") {
            continue; // the coro wrapper anchor names table symbols without calling them
        }
        if let Some(rest) = line.split("@alm_tbl_new(i64 ").nth(1) {
            news += 1;
            let esize: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            let esize: u64 = esize.parse().unwrap_or(u64::MAX);
            assert_eq!(
                esize,
                expected.esize(),
                "{context}: alm_tbl_new allocated esize {esize}, expected {} for elem {}\
                 \noffending line: {line}",
                expected.esize(),
                elem_name(expected),
            );
            // the flags byte's elem-kind field (bits 1..=3) and the
            // nested-table bit (0x80) must agree too; the low bit is
            // the dense/sparse switch and stays free
            let flags: String = rest
                .split(", i8 ")
                .nth(1)
                .unwrap_or("missing")
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .collect();
            let flags: u8 = flags.trim().parse().unwrap_or(u8::MAX);
            assert_eq!(
                (flags >> 1) & 0x07,
                expected.kind_flag() >> 1,
                "{context}: alm_tbl_new flags byte names elem kind {}, expected {} for elem {}\
                 \noffending line: {line}",
                (flags >> 1) & 0x07,
                expected.kind_flag() >> 1,
                elem_name(expected),
            );
            assert_eq!(
                flags & 0x80,
                0,
                "{context}: flat scalar program allocated a nested-table ctor\
                 \noffending line: {line}"
            );
        }
        if line.contains("call") && line.contains("@alm_tbl_") {
            let sym_start = line.find("@alm_tbl_").expect("checked above");
            let tail = &line[sym_start..];
            let sym: &str = &tail[..tail.find('(').unwrap_or(tail.len())];
            if sym.starts_with("@alm_tbl_get") || sym.starts_with("@alm_tbl_set") {
                accesses += 1;
                assert_eq!(
                    sym.contains("_any"),
                    expected.is_any(),
                    "{context}: access face {sym} is {} family, expected {} for elem {}\
                     \noffending line: {line}",
                    if sym.contains("_any") {
                        "an Any"
                    } else {
                        "a scalar"
                    },
                    if expected.is_any() {
                        "the Any"
                    } else {
                        "the scalar"
                    },
                    elem_name(expected),
                );
                if sym == "@alm_tbl_get" {
                    // the scalar int-lane get carries the cell size it
                    // will validate against as its trailing argument
                    let tail_size: String = line
                        .rsplit("i64 ")
                        .next()
                        .unwrap_or("missing")
                        .chars()
                        .take_while(|c| c.is_ascii_digit())
                        .collect();
                    let tail_size: u64 = tail_size.trim().parse().unwrap_or(u64::MAX);
                    assert_eq!(
                        tail_size,
                        expected.esize(),
                        "{context}: scalar alm_tbl_get names cell size {tail_size}, expected {} \
                         for elem {}\noffending line: {line}",
                        expected.esize(),
                        elem_name(expected),
                    );
                }
            }
        }
        // every `%ts*.dst`/`%ts*.valp` alloca is a scalar cell seam —
        // the only three emission sites are the get/set cell paths, all
        // typed by the cell repr. A seam under an Any expectation (or a
        // mistyped seam under a scalar one) is the desync class.
        if line.contains(" = alloca ") && (line.contains(".dst") || line.contains(".valp")) {
            seams += 1;
            let storage = line.rsplit("alloca ").next().unwrap_or("").trim();
            match expected.storage() {
                Some(want) => assert_eq!(
                    storage,
                    want,
                    "{context}: cell seam allocates `{storage}`, expected `{want}` for elem {}\
                     \noffending line: {line}",
                    elem_name(expected),
                ),
                None => panic!(
                    "{context}: scalar cell seam under an Any expectation — Any cells ride \
                     i128 register faces and must never touch a cell seam\
                     \noffending line: {line}"
                ),
            }
        }
    }
    assert!(
        news >= 1,
        "{context}: the artifact contains no alm_tbl_new — the ctor never lowered"
    );
    assert!(
        accesses >= 1,
        "{context}: the artifact contains no @alm_tbl_get*/@alm_tbl_set* calls — \
         table accesses never lowered"
    );
    if !expected.is_any() {
        assert!(
            seams >= 1,
            "{context}: the artifact contains no scalar cell seams for elem {} — \
             the accesses never touched a cell",
            elem_name(expected)
        );
    }
}

// ---- the properties ----

fn report(source: &str, expected: Elem, detail: String) -> String {
    format!(
        "{detail}\nexpected elem: {}\nprogram:\n{}",
        elem_name(expected),
        source
            .lines()
            .enumerate()
            .map(|(i, l)| format!("  {:2}| {}", i + 1, l))
            .collect::<Vec<_>>()
            .join("\n"),
    )
}

fn indent(source: &str) -> String {
    source
        .lines()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}

// ---- H5: the attribution census — desugaring omniscience ----
//
// Attribution rides the AST node (`loc` stamps minted at
// construction); the parser's parallel arrays and their pre-push
// discipline are gone, so the count-misfit class they made possible
// is unrepresentable and its two tripwire pins died with them
// (session 4). What remains: the multi-statement desugars (the for
// loop, and the tuple assignment since H8) stamp their whole family
// at the header — the census runs on every compile (analysis.rs)
// and these tests are its golden register and its tripwire proof.

/// Parse-only parts for the H5 pins: the AST, gated on clean front
/// diagnostics. Attribution rides the nodes — there are no parallel
/// arrays to hand through (they died in session 4).
fn parse_parts(source: &str) -> Vec<Stmt> {
    let mut tokens = Vec::new();
    let mut offsets = Vec::new();
    let mut lex = lexer::Token::lexer(source);
    loop {
        match lex.next() {
            Some(Ok(token)) => {
                offsets.push(lex.span().start);
                tokens.push(token);
            }
            Some(Err(_)) => panic!("H5 pin source failed to lex"),
            None => break,
        }
    }
    let mut parser = Parser::new(tokens.into_iter().zip(offsets).collect(), source);
    let ast = parser.parse_program();
    assert!(
        parser.diagnostics.is_empty(),
        "H5 pin source failed to parse: {:?}",
        parser.diagnostics
    );
    ast
}

// --- Per-Test Included Units (100% Verbatim) ---
include!("generated_programs_keep_one_elem_truth.rs");
include!("generator_sweep_survives_fresh_seeds.rs");
include!("hand_pinned_shapes_match_the_any_law.rs");
include!("rebind_adoption_probes_stay_pinned.rs");
include!("corpus_mutations_never_desync_the_walks.rs");
include!("token_soup_never_panics_or_desyncs.rs");
include!("str_key_derives_agree_across_the_abi.rs");
include!("walk_pins_are_a_pure_subset_over_the_corpus.rs");
include!("w3a_crossing_faces_reject_on_both_drive_and_spawn.rs");
include!("h5_for_desugar_reports_at_the_header_pin.rs");
include!("h5_one_to_one_sugars_and_elseif_attribution_pin.rs");
include!("h5_census_trips_on_right_count_wrong_line.rs");
include!("h8_elaborator_unit_goldens_pin.rs");
include!("h8_tuple_assign_attribution_pin.rs");
include!("h8_census_trips_on_tuple_wrong_line.rs");
include!("h7_one_pass_pairing_and_faces_pin.rs");
include!("h7_fn_touched_rides_the_pass_pin.rs");
include!("h7_census_sees_through_field_pin.rs");
include!("h11_one_formatter_shipped_path_pin.rs");
include!("h11_site_derives_the_prefix_pin.rs");
include!("h11_kinds_and_desync_render_law_pin.rs");
include!("h6_identity_rides_the_node_pin.rs");
include!("h6_id_census_pin.rs");
include!("h6_maps_key_ids_not_addresses_pin.rs");
include!("h12_instance_mint_law_pin.rs");
include!("h12_shadow_golden_depth_two_pin.rs");
include!("h12_bridge_totality_pin.rs");
include!("h12_shadow_maps_empty_by_site_law_pin.rs");
include!("h12_break_base_is_per_event_pin.rs");
include!("h12_multi_event_lowers_clean_at_equal_depth_pin.rs");
include!("h12_local_types_key_the_outermost_extent_pin.rs");
include!("h12_instantiation_facts_cover_every_site_pin.rs");
include!("h12_dispatch_mints_at_absolute_base_pin.rs");
include!("monomorphic_blocks_keep_one_elem_truth.rs");
