//! Property harness for the desync class. The ctor's physical allocation
//! (`TableNew` esize + elem-kind flags byte) and every access face come
//! from ONE decision; this harness turns any regression of that
//! unification into a CI signal without linking or running anything:
//!
//! 1. valid-by-construction single-table programs (the generator below)
//!    must compile clean end to end, and the emitted `.ll` must be
//!    elem-congruent — every `glm_tbl_new` esize/kind, the any/scalar
//!    family of every `glm_tbl_get*`/`glm_tbl_set*` call, the trailing
//!    cell size on scalar `glm_tbl_get` calls, and the LLVM storage type
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
//! oracle: the only `glm_tbl_new` calls are that name's ctors.

use crate::analysis;
use crate::ast::Stmt;
use crate::backend;
use crate::lexer;
use crate::lowerer::{IrLowerer, LowerError};
use crate::parser::Parser;
use crate::shape;
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

// ---- the in-process pipeline (main.rs's phases, minus clang/host) ----

#[derive(Debug)]
enum Stage {
    Panicked,
    Front,
    Analyze,
    Lower,
    Backend,
}

impl Stage {
    fn name(&self) -> &'static str {
        match self {
            Stage::Panicked => "panicked",
            Stage::Front => "front (lexer/parser)",
            Stage::Analyze => "shape analyzer + checker (one walk)",
            Stage::Lower => "lowerer",
            Stage::Backend => "backend",
        }
    }
}

/// Runs the full compile pipeline on `source` and returns the `.ll`
/// text, or the stage that rejected it with its diagnostics. Panics
/// inside a phase are caught and reported as their own stage — the
/// compiler must diagnose, never crash.
fn compile(source: &str) -> Result<String, (Stage, Vec<String>)> {
    match std::panic::catch_unwind(AssertUnwindSafe(|| compile_inner(source))) {
        Ok(r) => r,
        Err(payload) => {
            let msg = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "unknown panic".into());
            Err((Stage::Panicked, vec![format!("panic: {msg}")]))
        }
    }
}

fn compile_inner(source: &str) -> Result<String, (Stage, Vec<String>)> {
    let mut tokens = Vec::new();
    let mut offsets = Vec::new();
    let mut lexer = lexer::Token::lexer(source);
    loop {
        match lexer.next() {
            Some(Ok(token)) => {
                offsets.push(lexer.span().start);
                tokens.push(token);
            }
            Some(Err(_)) => {
                let line = 1 + source.as_bytes()[..lexer.span().start]
                    .iter()
                    .filter(|b| **b == b'\n')
                    .count();
                return Err((
                    Stage::Front,
                    vec![format!("line {line}: Syntax Error: Lexer error")],
                ));
            }
            None => break,
        }
    }
    compile_tokenized(source, tokens.into_iter().zip(offsets).collect())
}

/// The pipeline from a pre-lexed token stream — the token-soup fuzz leg
/// feeds mutated token vectors in here directly (offsets stay valid
/// byte indices of the same source, so diagnostics remain sound).
fn compile_tokenized(
    source: &str,
    tokens: Vec<(lexer::Token<'_>, usize)>,
) -> Result<String, (Stage, Vec<String>)> {
    let wrap = |r: Result<String, (Stage, Vec<String>)>| r;
    match std::panic::catch_unwind(AssertUnwindSafe(|| {
        let mut parser = Parser::new(tokens, source);
        let ast: Vec<Stmt> = parser.parse_program();
        let front_diagnostics = parser.diagnostics;
        if !front_diagnostics.is_empty() {
            return Err((Stage::Front, front_diagnostics));
        }

        let ctx = analysis::build_context(
            &ast,
            &parser.stmt_line_seq,
            &parser.stmt_col_seq,
            parser.ctor_line_seq.clone(),
        );

        // one walk: the analyzer's recorded pass IS the checker — its
        // diagnostics cover both halves
        let shape = shape::analyze(&ctx);
        if !shape.diagnostics.is_empty() {
            return Err((Stage::Analyze, shape.diagnostics));
        }

        let mut ir_lowerer = IrLowerer::new(&shape, ctx.stmt_locs);
        let mut ir_program = ir_lowerer.lower_program(&ast);
        if !ir_lowerer.diagnostics.is_empty() {
            return Err((Stage::Lower, ir_lowerer.diagnostics));
        }
        ir_program.source_file = "property_case.lua".into();

        backend::generate_llvm_ir(&ir_program).map_err(|d| (Stage::Backend, d))
    })) {
        Ok(r) => wrap(r),
        Err(payload) => {
            let msg = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "unknown panic".into());
            Err((Stage::Panicked, vec![format!("panic: {msg}")]))
        }
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

/// Every `glm_tbl_new` must allocate the expected elem's cell size AND
/// name the expected elem kind in its flags byte; every table access
/// face must belong to the expected family (`_any` iff Any); scalar
/// `glm_tbl_get` calls must carry the expected trailing cell size; and
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
        if let Some(rest) = line.split("@glm_tbl_new(i64 ").nth(1) {
            news += 1;
            let esize: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            let esize: u64 = esize.parse().unwrap_or(u64::MAX);
            assert_eq!(
                esize,
                expected.esize(),
                "{context}: glm_tbl_new allocated esize {esize}, expected {} for elem {}\
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
                "{context}: glm_tbl_new flags byte names elem kind {}, expected {} for elem {}\
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
        if line.contains("call") && line.contains("@glm_tbl_") {
            let sym_start = line.find("@glm_tbl_").expect("checked above");
            let tail = &line[sym_start..];
            let sym: &str = &tail[..tail.find('(').unwrap_or(tail.len())];
            if sym.starts_with("@glm_tbl_get") || sym.starts_with("@glm_tbl_set") {
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
                if sym == "@glm_tbl_get" {
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
                        "{context}: scalar glm_tbl_get names cell size {tail_size}, expected {} \
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
        "{context}: the artifact contains no glm_tbl_new — the ctor never lowered"
    );
    assert!(
        accesses >= 1,
        "{context}: the artifact contains no @glm_tbl_get*/@glm_tbl_set* calls — \
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

/// Generated programs compile clean and stay elem-congruent: one elem
/// truth, decided once, consumed by the ctor AND every access face.
#[test]
fn generated_programs_keep_one_elem_truth() {
    const SEED: u64 = 0x2026_1021;
    const PROGRAMS: usize = 400;
    let mut rng = Rng::new(SEED);
    let mut any_expected = 0usize;
    let mut bool_expected = 0usize;

    for _ in 0..PROGRAMS {
        let (source, expected) = gen_program(&mut rng);
        any_expected += usize::from(expected.is_any());
        bool_expected += usize::from(expected == Elem::Bool);
        match compile(&source) {
            Ok(ll) => assert_elem_congruence(&ll, expected, "generated program"),
            Err((stage, diags)) => panic!(
                "{}",
                report(
                    &source,
                    expected,
                    format!(
                        "valid-by-construction program was rejected at {}: {}",
                        stage.name(),
                        diags.join("; ")
                    ),
                )
            ),
        }
    }

    // Two-sided distribution bounds: must exercise both Any adoption AND
    // homogeneous scalar lifecycles (including 1-byte Bool tables).
    assert!(
        (PROGRAMS / 4..=PROGRAMS * 3 / 4).contains(&any_expected),
        "skewed Elem::Any distribution: {any_expected}/{PROGRAMS} generated programs \
         expected Any (expected between 25% and 75%)"
    );
    assert!(
        bool_expected >= PROGRAMS / 20,
        "only {bool_expected}/{PROGRAMS} generated programs stayed homogeneous Elem::Bool \
         (esize 1 path under-exercised)"
    );
    eprintln!(
        "property coverage: any_expected={any_expected}/{PROGRAMS} \
         bool_expected={bool_expected}/{PROGRAMS}"
    );
}

/// The fuzz sweep: fresh seeds beyond the pinned one — the property must
/// not hold only for the flagship seed's sample. Same congruence oracle,
/// looser aggregate distribution bounds (per-seed balance is already
/// pinned by the flagship leg).
#[test]
fn generator_sweep_survives_fresh_seeds() {
    const SEEDS: u64 = 32;
    const PROGRAMS_PER_SEED: usize = 125;
    let mut any_expected = 0usize;
    let mut bool_expected = 0usize;
    let mut total = 0usize;

    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x5EED_0000 ^ (seed << 32) ^ seed);
        for _ in 0..PROGRAMS_PER_SEED {
            let (source, expected) = gen_program(&mut rng);
            any_expected += usize::from(expected.is_any());
            bool_expected += usize::from(expected == Elem::Bool);
            total += 1;
            match compile(&source) {
                Ok(ll) => {
                    assert_elem_congruence(&ll, expected, &format!("seed sweep (seed {seed})"))
                }
                Err((stage, diags)) => panic!(
                    "{}",
                    report(
                        &source,
                        expected,
                        format!(
                            "valid-by-construction program (sweep seed {seed}) was rejected \
                             at {}: {}",
                            stage.name(),
                            diags.join("; ")
                        ),
                    )
                ),
            }
        }
    }

    assert_eq!(total, SEEDS as usize * PROGRAMS_PER_SEED);
    assert!(
        any_expected >= total / 8,
        "sweep never exercised Any adoption: {any_expected}/{total}"
    );
    assert!(
        bool_expected >= total / 20,
        "sweep under-exercised the esize-1 Bool path: {bool_expected}/{total}"
    );
    eprintln!(
        "seed sweep coverage: any_expected={any_expected}/{total} \
         bool_expected={bool_expected}/{total}"
    );
}

/// Hand-pinned shapes for the law's sharpest corners: the
/// rebind_nil_slot_adopt shape, the direct mix (a lock-pinned path),
/// the nil-less rebind, the empty-opening deferred store, the branching
/// nil-severed rebind, the same-kind rebind, the 1-byte Bool cell, a
/// Str witness, the read-BEFORE-mix program — the flow-insensitive
/// total join means a textually-earlier read still carries the Any face
/// the later mix decided — and the loop shapes (for-store through the
/// loop index, while+break in a plain while) the corpus's compile-only
/// for/break cases leave unpinned.
#[test]
fn hand_pinned_shapes_match_the_any_law() {
    let cases: &[(&str, Elem)] = &[
        (
            "local t = {1}\nt = nil\nt = {}\nt[0] = 2.5\nprint(t[0])\n",
            Elem::Any,
        ),
        ("local t = {1}\nt[0] = 2.5\nprint(t[0])\n", Elem::Any),
        (
            "local t = {1}\nt = {}\nt[0] = 2.5\nprint(t[0])\n",
            Elem::Any,
        ),
        ("local t = {}\nt[0] = 2.5\nprint(t[0])\n", Elem::Flt),
        (
            "local t = {}\nt[0] = 1\nt[1] = 2.5\nprint(t[0])\n",
            Elem::Any,
        ),
        (
            "local t = {1}\nif true then\n  t = nil\n  t = {2.5}\nend\nprint(t[0])\n",
            Elem::Any,
        ),
        (
            "local t = {1}\nprint(t[0])\nt[0] = 2.5\nprint(t[0])\n",
            Elem::Any,
        ),
        ("local t = {1}\nt[0] = 2\nt = {3}\nprint(t[0])\n", Elem::Int),
        ("local t = {true}\nt[1] = false\nprint(t[1])\n", Elem::Bool),
        ("local t = {\"s\"}\nt[0] = 2.5\nprint(t[0])\n", Elem::Any),
        // a statically-dead arm still witnesses — flow-insensitive join
        (
            "local t = {1}\nif false then\n  t[0] = 2.5\nend\nprint(t[0])\n",
            Elem::Any,
        ),
        // the loop shapes: for-store through the loop index adopts on
        // the opening empty ctor; plain-while break keeps the elem truth
        (
            "local t = {}\nfor i = 0, 3 do\n  t[i] = 2.5\nend\nprint(t[0])\n",
            Elem::Flt,
        ),
        (
            "local t = {1}\nfor i = 0, 3 do\n  t[i] = 2.5\nend\nprint(t[0])\n",
            Elem::Any,
        ),
        (
            "local t = {true}\nwhile true do\n  t[0] = false\n  break\nend\nprint(t[0])\n",
            Elem::Bool,
        ),
    ];
    for (source, expected) in cases {
        match compile(source) {
            Ok(ll) => assert_elem_congruence(&ll, *expected, "hand-pinned shape"),
            Err((stage, diags)) => panic!(
                "{}",
                report(
                    source,
                    *expected,
                    format!(
                        "pinned shape was rejected at {}: {}",
                        stage.name(),
                        diags.join("; ")
                    ),
                )
            ),
        }
    }
}

/// The rebind-adoption probes, pinned permanently (they lived only in
/// throwaway differential batteries): the nested-table rebind and its
/// nil-severed flavor must adopt in the LATTICE — one elem truth — and
/// the move flavor with them (the move-slot law: `local u = t` severs
/// the name but its type slot survives, so the later rebind adopts
/// across the move exactly as it adopts across a nil).
#[test]
fn rebind_adoption_probes_stay_pinned() {
    let flat: &[(&str, Elem)] = &[
        (
            "local t = {1}\nlocal u = t\nt = {2.5}\nprint(t[0])\nprint(u[0])\n",
            Elem::Any,
        ),
        (
            "local t = {1}\nlocal u = t\nt = nil\nprint(u[0])\n",
            Elem::Int,
        ),
    ];
    for (source, expected) in flat {
        match compile(source) {
            Ok(ll) => assert_elem_congruence(&ll, *expected, "rebind adoption probe"),
            Err((stage, diags)) => panic!(
                "{}",
                report(
                    source,
                    *expected,
                    format!(
                        "adoption probe was rejected at {}: {}",
                        stage.name(),
                        diags.join("; ")
                    ),
                )
            ),
        }
    }
    for source in [
        "local t = {{1}}\nt = {{2.5}}\nprint(t[0][0])\n",
        "local t = {{1}}\nt = nil\nt = {{2.5}}\nprint(t[0][0])\n",
    ] {
        let ll = compile(source).unwrap_or_else(|(stage, diags)| {
            panic!(
                "{}",
                report(
                    source,
                    Elem::Any,
                    format!(
                        "nested adoption probe was rejected at {}: {}",
                        stage.name(),
                        diags.join("; ")
                    ),
                )
            )
        });
        let inner_esize16 = ll
            .lines()
            .filter(|l| !l.contains("ptrtoint"))
            .filter(|l| l.contains("@glm_tbl_new(i64 16"))
            .count();
        assert_eq!(
            inner_esize16,
            2,
            "nested adoption probe: expected both inner ctors at esize 16 (retroactive \
             packing)\nprogram:\n{}",
            indent(source)
        );
        assert!(
            ll.lines()
                .any(|l| l.contains("@glm_tbl_get_any") || l.contains("@glm_tbl_set_any")),
            "nested adoption probe: no Any face in the artifact — the packed cells lost \
             their dynamic faces\nprogram:\n{}",
            indent(source)
        );
    }
    assert!(
        compile(
            "local f = function() return 1 end\ndo\n  f = function() return 2 end\nend\nprint(f())\n"
        )
        .is_ok(),
        "block-scoped fn rebind must compile (the rebind takes effect)"
    );
    let (_, diags) = compile("local t = {1}\nlocal u = t\nprint(t[0])\n")
        .expect_err("a read through a moved name must reject");
    assert!(
        diags.iter().any(|d| d.contains("may be moved here")),
        "moved read rejected with the wrong diagnostic: {diags:?}"
    );
}

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
                        let desyncs: Vec<String> = diags
                            .iter()
                            .filter(|d| LowerError((*d).clone()).is_desync())
                            .cloned()
                            .collect();
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
                            diags.join("; "),
                            if desyncs.is_empty() {
                                "no".to_string()
                            } else {
                                desyncs.join("; ")
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
                    let desyncs: Vec<String> = diags
                        .iter()
                        .filter(|d| LowerError((*d).clone()).is_desync())
                        .cloned()
                        .collect();
                    let crime = match stage {
                        Stage::Panicked => "the compiler crashed on token soup",
                        _ => "checker-accepted token soup reached a walk desync",
                    };
                    panic!(
                        "{crime} — base {label} failed at {}\ndiagnostics: {}\n\
                         desync-class: {}\nsoup (Debug tokens):\n{}\nbase:\n{}",
                        stage.name(),
                        diags.join("; "),
                        if desyncs.is_empty() {
                            "no".to_string()
                        } else {
                            desyncs.join("; ")
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

/// The frozen str-key ABI (C2): every string's identity key must agree
/// across the derive that WRITES it (str_pool.c's FNV-1a-62, packed in
/// the 8-byte prefix by the C pool) and the Rust mirror the backend
/// folds constants with (`str_key_of_bytes`) — for random strings and
/// for every string literal in the corpus. A disagreement is a silent
/// wrong-record-cell class: the C side and the compiler would address
/// two different cells for one field name.
#[test]
fn str_key_derives_agree_across_the_abi() {
    use glm_rt::rt::{glm_str_intern, glm_str_key, is_str_key, str_key_of_bytes};

    let mut words: Vec<Vec<u8>> = Vec::new();
    // random strings over a corpus-flavored alphabet
    const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.:-";
    let mut rng = Rng::new(0xAB1_5EED);
    for _ in 0..1500 {
        let len = 1 + rng.below(24);
        let word: Vec<u8> = (0..len)
            .map(|_| ALPHABET[rng.below(ALPHABET.len())])
            .collect();
        words.push(word);
    }
    // every string literal in the corpus (the lexer's rule: `"[^"]*"`)
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
    let mut corpus_literals = 0usize;
    for name in &names {
        let Ok(source) = std::fs::read_to_string(cases_dir.join(name)) else {
            continue;
        };
        let bytes = source.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                let mut j = i + 1;
                while j < bytes.len() && bytes[j] != b'"' && bytes[j] != b'\n' {
                    j += 1;
                }
                if j < bytes.len() && bytes[j] == b'"' && j > i + 1 {
                    words.push(bytes[i + 1..j].to_vec());
                    corpus_literals += 1;
                }
                i = j + 1;
            } else {
                i += 1;
            }
        }
    }
    assert!(
        corpus_literals >= 10,
        "extracted only {corpus_literals} corpus string literals — cases/ vanished?"
    );

    for word in &words {
        let interned = unsafe { glm_str_intern(word.as_ptr(), word.len()) };
        assert!(
            !interned.is_null(),
            "the C pool refused to intern {:?} (malloc failure?)",
            String::from_utf8_lossy(word)
        );
        let c_derive = unsafe { glm_str_key(interned) };
        let rust_derive = str_key_of_bytes(word);
        assert_eq!(
            c_derive,
            rust_derive,
            "C pool prefix key and Rust derive disagree on {:?} — the frozen ABI broke",
            String::from_utf8_lossy(word)
        );
        assert!(
            is_str_key(c_derive),
            "key for {:?} fell outside the reserved str-key range",
            String::from_utf8_lossy(word)
        );
    }
    eprintln!(
        "str-key ABI coverage: {} strings ({} corpus literals) through both derives",
        words.len(),
        corpus_literals
    );
}

fn indent(source: &str) -> String {
    source
        .lines()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}
