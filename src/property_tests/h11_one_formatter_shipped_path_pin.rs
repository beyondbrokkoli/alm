
/// H11 pin 1 — ONE formatter, shipped-path golden renders. Every
/// reachable rejection face (parse, the lex latch, the bounds guard,
/// scope, the checker, the walk, the lattice, the elem table, the ffi
/// gate's bare refusal) through the ONE pipeline, compared as FULL
/// rendered strings — not substrings — so the format bytes
/// (`line N: Kind: text`, the bare face verbatim) cannot drift
/// between mints. The goldens are the pre-fold binary's bytes
/// (probed byte-for-byte at the fold).
#[test]
fn h11_one_formatter_shipped_path_pin() {
    let faces: &[(&str, Stage, &str)] = &[
        // the parser: site from the token stream, kind Syntax
        (
            "local a = 1\nlocal b =\n",
            Stage::Front,
            "line 2: Syntax Error: Expected expression",
        ),
        // a lexer error LATCHES: the truncated stream still parses,
        // both halves reject together at the front gate
        (
            "local a = 1\nlocal b = 1 $\n",
            Stage::Front,
            "line 2: Syntax Error: Lexer error",
        ),
        // the sixth face: the dialect's bounds guard (parser site)
        (
            "local t = {[1152921504606846976]=1}\n",
            Stage::Front,
            "line 1: Table Bounds Error: table index overflow",
        ),
        // the walk's scope face
        (
            "print(q)\n",
            Stage::Analyze,
            "line 1: Scope Error: reference to undeclared variable 'q'",
        ),
        // the checker's arithmetic face
        (
            "local a = \"x\"\nlocal b = a + 1\n",
            Stage::Analyze,
            "line 2: Type Error: '+' requires numeric operands",
        ),
        // the walk's lifetime face (the move law)
        (
            "local t = {1}\nlocal u = t\nlocal v = t\n",
            Stage::Analyze,
            "line 3: Lifetime Error: 't' may be moved here — reads through a \
             possibly-moved name are rejected at compile time",
        ),
        // the lattice's conflict face — site from ctor_lines
        (
            "local t = {1}\nlocal u = {2}\nt[0] = u\n",
            Stage::Analyze,
            "line 1: Type Error: a table's cells hold one scalar kind — mixing scalar \
             kinds chooses the dynamic cell (Any), but a table value never rides a \
             cell (table site #0)",
        ),
        // the elem table's read-before-value face
        (
            "local t = {}\nprint(t[0])\n",
            Stage::Analyze,
            "line 1: Type Error: a table is read before it is ever given a value \
             (table site #0)",
        ),
        // the ffi gate: bare — no site, no kind prefix, verbatim text
        (
            "local ffi = require(\"ffi\")\nffi.cdef(\"void* alm_exec(void*);\")\n",
            Stage::Ffi,
            "alm compiler error: the ffi surface (require(\"ffi\") / ffi.load / \
             lib.sym) is --exe-only — rebuild with --exe; a shared object loading \
             shared objects is not acyclic destiny",
        ),
    ];
    for (source, want_stage, golden) in faces {
        let Err((stage, diags)) = compile(source) else {
            panic!("the face must reject: {golden:?}");
        };
        assert_eq!(
            stage.name(),
            want_stage.name(),
            "the face rejected at the wrong stage: {golden:?}"
        );
        let rendered: Vec<String> = diags.iter().map(|d| d.render()).collect();
        assert_eq!(
            rendered,
            vec![golden.to_string()],
            "the rendered bytes drifted — the format law is byte-stable"
        );
        // the typed face behind the bytes: a real rejection is never a
        // desync — the variant names the internal class only
        assert!(
            diags.iter().all(|d| !d.is_desync()),
            "a shipped rejection minted as desync: {golden:?}"
        );
    }
}
