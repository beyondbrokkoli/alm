//! The omni layer — the watch post the boundary side points at the
//! scope machinery.
//!
//! The walk owns the master `scopes` stack; the checker rides it with
//! its own frames. Both tiers evolved by patching whichever stack was
//! nearest, and the receipts (p30's orphan, fn_defcollection's
//! time-travel) all share one shape: a face moved somewhere no
//! observer was watching. The omni layer is that observer — built
//! FROM the boundary root outward, the direction `arg` comes from.
//!
//! `arg` is the canary-in-chief. It is the one binding the HOST
//! mints (`boundary_root_scope` seeds it at depth 0 before any walk
//! pass) — the seed of the future global foundation. Phase 1 of the
//! layer was strictly observational: it never wrote a face, never
//! reordered a stack, never gated a diagnostic — it recorded,
//! rendered, and tripped three invariants. Phase 2 plugged the
//! foundation in: the checker now carries its own root fn-face home
//! (`Checker::root_fns` — the rider-side twin of the walk's
//! boundary-root scope at d0), so top-level fn faces live on the
//! checker's own statement-order timeline and `resolve_fn_binding`
//! answers through it BEFORE the master snapshot. The layer stays
//! observational — the checker's writes are its own; the layer only
//! renders them.
//!
//! The three invariants stand:
//!
//! - ORPHAN-BURIAL (hard): a scope's life may not cost a surviving
//!   binding a fn face it carried when the scope opened, unless a
//!   write inside that scope moved the face. This is the p30 pre-fix
//!   bug shape ("exit_scope buried it"), still live as a law the
//!   master stack must keep proving. The checker-side twin reads the
//!   birthplace: a face DECLARED at the dying frame dies with it —
//!   the scope's own grave, never an orphan — while a face whose
//!   binding outlived the frame must be re-supplied by a surviving
//!   home (inline chain → root home → master snapshot) or the law
//!   trips.
//! - ROOT-DRAG (soft, xfail-pinned): a fn-body collection that moves
//!   a depth-0 binding's fn face — the defcollection travels back in
//!   time (fn_defcollection_order: the first print answers 2 before
//!   g() ever ran). The trip is a receipt, not a rejection: the
//!   divergence is chartered on the MASTER side — the walk's own
//!   type story — while the checker's resolution no longer reads the
//!   dragged state (the root home answers first), so the runtime
//!   divergence the pin named is retired.
//! - CHAIN-FREEZE (hard): a defcollection chain must not freeze a
//!   root fn FACE in — a chain entry that IS a depth-0 fn-bound
//!   binding's own face would answer past a rebind of that binding
//!   (functions.rs excludes them exactly so resolve_fn_binding's
//!   snapshot fallback sees the CURRENT binding; the trip is face
//!   identity, not name presence — a deeper shadow of the same name
//!   is a different binding and its face rides the chain by right).
//!
//! Everything rides the env gate `ALM_OMNI`; default builds compile
//! the calls down to an enabled() check and emit nothing, so the
//! trace plate and every golden output stay byte-identical. With
//! `ALM_OMNI` set, events stream to stderr prefixed `[omni]`, stage
//! dumps render on request (`dump`/`all`/`1` values), and the run
//! ends with a report. `ALM_OMNI_STRICT=1` turns ORPHAN-BURIAL and
//! CHAIN-FREEZE trips into a panic — the plug-in phases want the
//! hard gate on while the foundation is rewired.
//!
//! The five plate signals (195-199, trace_signals.txt) fire only
//! under the gate, so plate.py decodes them on demand and the
//! default plates stay quiet.
//! [ownership] The five plate signals never port — alm has no plate.

use crate::ast::NodeId;
use crate::shape::core::{BOUNDARY_ROOT, DECL_PENDING, MOVED_ROOT, NULL_ROOT};
use crate::shape::ty::Ty;
use std::cell::RefCell;
use std::collections::BTreeMap;

use super::{Binding, Prov, Scope};

/// The layer's gate: `ALM_OMNI` in the environment turns the watch
/// on. A OnceLock read per hook — the disabled path is one branch.
pub(super) fn enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("ALM_OMNI").is_some())
}

/// Stage dumps (scopes snapshots, chain tables) ride `ALM_OMNI`
/// values `dump`, `all`, or `1`. Plain `ALM_OMNI=<anything-else>`
/// keeps the event log and report but skips the bulky dumps.
fn dump_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| match std::env::var("ALM_OMNI") {
        Ok(v) => matches!(v.as_str(), "dump" | "all" | "1"),
        Err(_) => false,
    })
}

/// The hard-gate switch: `ALM_OMNI_STRICT=1` panics the analysis at
/// report time on any hard trip. Soft trips (the chartered
/// divergences) never panic.
fn strict() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("ALM_OMNI_STRICT").is_some())
}

/// A root binding's fn face, as a snapshot sees it.
pub(super) type RootFaces = BTreeMap<String, Option<NodeId>>;

/// The fn face's fn_ptr as a renderable token.
fn face(ptr: Option<NodeId>) -> String {
    match ptr {
        Some(p) => format!("fn#{}", p.0),
        None => "—".to_string(),
    }
}

/// Which tier answered a fn resolution — the tier IS the story: a
/// top-level name answering through the master snapshot means the
/// rider's own foundation (frames + root home) had no home for it.
#[derive(Clone, Copy, PartialEq)]
pub(super) enum Tier {
    Frames,
    RootHome,
    InlineChain,
    MasterSnap,
}

impl Tier {
    fn label(self) -> &'static str {
        match self {
            Tier::Frames => "rider-frames",
            Tier::RootHome => "root-home",
            Tier::InlineChain => "inline-chain",
            Tier::MasterSnap => "master-snapshot",
        }
    }
}

/// One open walk scope's stake in the resurrection law.
struct ScopeStake {
    depth: usize,
    /// The root bindings' fn faces when this scope opened.
    root_faces: RootFaces,
    /// Every root name a write touched while this scope lived, with
    /// the faces the writes set. A pop may only lose a face a write
    /// moved.
    writes: BTreeMap<String, Vec<Option<NodeId>>>,
}

/// One fn-body collection's stake in the drag law.
struct CollectionStake {
    fn_ptr: NodeId,
    label: String,
    /// The root faces when the body walk began.
    root_faces: RootFaces,
    /// The names the chain froze out of the depth-0 tier.
    excluded_root_fns: Vec<String>,
}

/// A fired event's rendered line, kept for the end-of-run report.
struct Event {
    line: String,
}

struct Omni {
    pass: u32,
    phase: &'static str,
    stmt_line: Option<usize>,
    events: Vec<Event>,
    scopes: Vec<ScopeStake>,
    collections: Vec<CollectionStake>,
    /// The chain notes gathered at collection time for the final
    /// defcollection table.
    chain_notes: Vec<String>,
    orphan_trips: usize,
    drag_trips: usize,
    chain_trips: usize,
}

impl Omni {
    fn new() -> Self {
        Omni {
            pass: 0,
            phase: "",
            stmt_line: None,
            events: Vec::new(),
            scopes: Vec::new(),
            collections: Vec::new(),
            chain_notes: Vec::new(),
            orphan_trips: 0,
            drag_trips: 0,
            chain_trips: 0,
        }
    }

    /// The event prefix: pass · phase · line — the coordinates every
    /// receipt needs to be readable.
    fn ctx(&self) -> String {
        let line = self.stmt_line.map(|l| format!("·L{l}")).unwrap_or_default();
        format!("p{}·{}{}", self.pass, self.phase, line)
    }

    fn record(&mut self, line: String) {
        // A runaway fixpoint loop floods the log; the cap keeps the
        // report bounded while the counters stay exact.
        if self.events.len() < 4096 {
            self.events.push(Event { line });
        }
    }
}

thread_local! {
    static OMNI: RefCell<Omni> = RefCell::new(Omni::new());
}

fn with<R>(f: impl FnOnce(&mut Omni) -> R) -> R {
    OMNI.with(|o| f(&mut o.borrow_mut()))
}

// ── lifecycle ────────────────────────────────────────────────────────

pub(super) fn begin_analysis() {
    if !enabled() {
        return;
    }
    with(|o| *o = Omni::new());
}

pub(super) fn begin_pass(pass: u32, phase: &'static str) {
    if !enabled() {
        return;
    }
    with(|o| {
        o.pass = pass;
        o.phase = phase;
        o.stmt_line = None;
        o.scopes.clear();
        o.collections.clear();
    });
}

pub(super) fn note_stmt(line: usize) {
    if !enabled() {
        return;
    }
    with(|o| o.stmt_line = Some(line));
}

// ── face vocabulary ──────────────────────────────────────────────────

/// The walk's scopes stack renders here — the master's own view, one
/// line per binding with every face the Binding carries.
pub(super) fn fmt_ty(t: &Ty) -> String {
    match t {
        Ty::Pending => "pend".to_string(),
        Ty::Int => "int".to_string(),
        Ty::Flt => "flt".to_string(),
        Ty::Bool => "bool".to_string(),
        Ty::Str => "str".to_string(),
        Ty::Ffi => "ffi".to_string(),
        Ty::FfiLib => "ffilib".to_string(),
        Ty::Async => "async".to_string(),
        Ty::Any => "any".to_string(),
        Ty::Conflict => "conflict".to_string(),
        Ty::Tbl(e) => format!("tbl({})", fmt_ty(e)),
        Ty::Closure(p) => format!("fn#{}", p.0),
        Ty::Unknown(id) => format!("u#{id}"),
    }
}

fn fmt_alias(a: &usize) -> String {
    match *a {
        BOUNDARY_ROOT => "boundary".to_string(),
        MOVED_ROOT => "moved".to_string(),
        NULL_ROOT => "null".to_string(),
        DECL_PENDING => "decl-pend".to_string(),
        _ => format!("s{}", a),
    }
}

fn fmt_prov(p: &Option<Prov>) -> String {
    match p {
        Some(Prov::If(n)) => format!("if#{}", n.0),
        Some(Prov::Call(n)) => format!("call#{}", n.0),
        None => "—".to_string(),
    }
}

fn fmt_binding(name: &str, b: &Binding) -> String {
    let canary = b.shape.aliases.contains(&BOUNDARY_ROOT) || name == "arg";
    let aliases: Vec<String> = b.shape.aliases.iter().take(4).map(fmt_alias).collect();
    let aliases = if b.shape.aliases.len() > 4 {
        format!("{}…+{}", aliases.join(","), b.shape.aliases.len() - 4)
    } else {
        aliases.join(",")
    };
    format!(
        "  {name:<10} ty={:<14} fn={:<8} prov={:<9} node={:<4} roots=[{}]{}",
        fmt_ty(&b.shape.ty),
        face(b.fn_ptr),
        fmt_prov(&b.prov),
        b.scalar_node
            .map(|n| n.to_string())
            .unwrap_or_else(|| "—".to_string()),
        aliases,
        if canary { "  ⌑canary" } else { "" },
    )
}

/// The root faces of a scopes stack — what the canary watches.
pub(super) fn root_faces_of(scopes: &[Scope]) -> RootFaces {
    scopes
        .first()
        .map(|root| {
            root.iter()
                .map(|(n, b)| (n.clone(), b.fn_ptr))
                .collect::<RootFaces>()
        })
        .unwrap_or_default()
}

fn render_scopes(label: &str, scopes: &[Scope]) -> Vec<String> {
    let mut out = vec![format!(
        "┌ {} · {} deep · root bindings {}",
        label,
        scopes.len(),
        scopes.first().map(|s| s.len()).unwrap_or(0)
    )];
    for (d, scope) in scopes.iter().enumerate() {
        let tag = if d == 0 { "root" } else { "scope" };
        out.push(format!("│ d{d} {tag} ─ {} binding(s)", scope.len()));
        for (name, b) in scope {
            for line in fmt_binding(name, b).lines() {
                out.push(format!("│ {line}"));
            }
        }
    }
    out.push("└".to_string());
    out
}

/// A stage dump of the master stack, straight to stderr.
pub(super) fn dump_scopes(label: &str, scopes: &[Scope]) {
    if !enabled() || !dump_on() {
        return;
    }
    with(|o| {
        for line in render_scopes(label, scopes) {
            eprintln!("[omni] {}", o.ctx() + " " + &line);
        }
    });
}

// ── walk-side hooks ──────────────────────────────────────────────────

pub(super) fn scope_push(depth: usize, root_faces: &RootFaces) {
    if !enabled() {
        return;
    }
    with(|o| {
        o.scopes.push(ScopeStake {
            depth,
            root_faces: root_faces.clone(),
            writes: BTreeMap::new(),
        });
    });
}

/// A scope died. The resurrection law: every root face the scope's
/// birth snapshot carried must still be carried — unless a write
/// inside the scope's lifetime moved it. A loss with no write is the
/// p30 pre-fix burial, the hard trip.
pub(super) fn scope_pop(depth: usize, root_faces_now: &RootFaces) {
    if !enabled() {
        return;
    }
    with(|o| {
        if let Some(stake) = o.scopes.pop() {
            debug_assert_eq!(
                stake.depth, depth,
                "omni scope stakes ride the walk's stack"
            );
            for (name, before) in &stake.root_faces {
                let now = root_faces_now.get(name).copied().flatten();
                if now == *before {
                    continue;
                }
                let moved_by_write = stake.writes.contains_key(name);
                if !moved_by_write {
                    o.orphan_trips += 1;
                    o.record(format!(
                        "{} ⚑ORPHAN scope d{depth} buried '{}' fn face {} → {} \
                         with no write in its lifetime",
                        o.ctx(),
                        name,
                        face(*before),
                        face(now),
                    ));
                }
            }
        }
    });
}

/// A fn face moved on the master stack. `home_depth` is where the
/// binding lives; the writer always sits in the innermost scope. A
/// write landing on a depth-0 binding while a body collection is
/// open is the defcollection drag — the receipt the
/// fn_defcollection divergence rides on.
pub(super) fn fn_face_write(
    name: &str,
    home_depth: usize,
    writer_depth: usize,
    ptr: Option<NodeId>,
    via: &str,
) {
    if !enabled() {
        return;
    }
    let canary = home_depth == 0;
    with(|o| {
        // stake the write on every open scope — a root face's life
        // spans them all
        for stake in &mut o.scopes {
            stake.writes.entry(name.to_string()).or_default().push(ptr);
        }
        let drag = canary && !o.collections.is_empty();
        o.record(format!(
            "{} ✎fn-face '{}' home=d{} writer=d{} → {} ({}){}{}",
            o.ctx(),
            name,
            home_depth,
            writer_depth,
            face(ptr),
            via,
            if canary { "  ⌑root" } else { "" },
            if drag { "  ⇜DRAG-CANDIDATE" } else { "" },
        ));
    });
}

/// A fn-body collection opened: the chain is frozen, the body walk
/// begins. The stake records the root faces so `collection_end` can
/// name exactly what the collection dragged.
pub(super) fn collection_begin(
    fn_ptr: NodeId,
    chain: &BTreeMap<String, Option<NodeId>>,
    excluded_root_fns: &[String],
    root_faces: &RootFaces,
) {
    if !enabled() {
        return;
    }
    with(|o| {
        // CHAIN-FREEZE: the chain must not freeze a ROOT face in — a
        // Some entry for an excluded root fn name that IS the root
        // binding's own face would answer past a rebind of the root
        // binding (fn_key_late_binding: 1 then 2). A deeper shadow of
        // the same name is a DIFFERENT binding — inner wins, the
        // definition-site truth the chain exists to carry — and its
        // face dies with its scope, never masquerading as the root
        // face. So the trip is face identity, not name presence.
        let frozen_in: Vec<&String> = excluded_root_fns
            .iter()
            .filter(|n| {
                match (
                    chain.get(*n).copied().flatten(),
                    root_faces.get(*n).copied().flatten(),
                ) {
                    (Some(frozen), Some(root)) => frozen == root,
                    _ => false,
                }
            })
            .collect();
        if !frozen_in.is_empty() {
            o.chain_trips += 1;
            o.record(format!(
                "{} ⚑CHAIN fn#{}/{} froze root fn name(s) {} INTO the chain",
                o.ctx(),
                fn_ptr.0,
                chain.len(),
                frozen_in
                    .iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(","),
            ));
        }
        o.chain_notes.push(format!(
            "fn#{:<4} {:>3} entry(s) · root-fn exclusions: {}",
            fn_ptr.0,
            chain.len(),
            if excluded_root_fns.is_empty() {
                "∅".to_string()
            } else {
                excluded_root_fns.join(",")
            },
        ));
        o.collections.push(CollectionStake {
            fn_ptr,
            label: format!("fn#{} collection", fn_ptr.0),
            root_faces: root_faces.clone(),
            excluded_root_fns: excluded_root_fns.to_vec(),
        });
    });
}

/// The body walk returned. The drag law reads the delta: every root
/// face the collection moved is a receipt — the future applied at
/// the definition point.
pub(super) fn collection_end(fn_ptr: NodeId, root_faces_now: &RootFaces) {
    if !enabled() {
        return;
    }
    with(|o| {
        if let Some(stake) = o.collections.pop() {
            debug_assert_eq!(
                stake.fn_ptr, fn_ptr,
                "omni collection stakes ride the body walk's nesting"
            );
            for (name, before) in &stake.root_faces {
                let now = root_faces_now.get(name).copied().flatten();
                if now != *before {
                    o.drag_trips += 1;
                    o.record(format!(
                        "{} ⇜DRAG collection {} dragged root '{}' fn face {} → {} \
                         — the body's future applied at the definition point{}",
                        o.ctx(),
                        stake.label,
                        name,
                        face(*before),
                        face(now),
                        if stake.excluded_root_fns.contains(name) {
                            " · chain-excluded (the chain stayed clean; the master moved)"
                                .to_string()
                        } else {
                            String::new()
                        },
                    ));
                }
            }
        }
    });
}

// ── checker-side hooks ───────────────────────────────────────────────

/// Where a checker-side fn-face write landed. `Frame` is a rider
/// frame, `Root` is the rider's root fn-face home (the checker-side
/// twin of the walk's boundary-root scope — the phase-2 global
/// foundation), `None` is a write with no home at all: it drops.
pub(super) enum FnHome {
    Frame(usize),
    Root,
    None,
}

/// The checker's own fn-face write into its rider foundation. A
/// `None` home is the "no home anywhere" receipt; the root home is
/// where top-level fn faces live since phase 2 — the checker's own
/// statement-order timeline, so a top-level call resolves at its
/// binding point's state instead of the master snapshot's dragged
/// future.
pub(super) fn checker_fn_write(name: &str, home: FnHome, ptr: Option<NodeId>, via: &str) {
    if !enabled() {
        return;
    }
    with(|o| {
        o.record(match home {
            FnHome::Frame(d) => format!(
                "{} ✎checker-fn '{}' frame=d{} → {} ({})",
                o.ctx(),
                name,
                d,
                face(ptr),
                via,
            ),
            FnHome::Root => format!(
                "{} ✎checker-fn '{}' home=root → {} ({}) — the rider's \
                 global foundation carries this face",
                o.ctx(),
                name,
                face(ptr),
                via,
            ),
            FnHome::None => format!(
                "{} ✎checker-fn '{}' → {} ({}) — DROPPED: no home \
                 anywhere (the master snapshot may carry this face)",
                o.ctx(),
                name,
                face(ptr),
                via,
            ),
        });
    });
}

/// A checker frame died carrying fn faces. The law reads the
/// birthplace (`born_here` — the binding was minted at the dying
/// frame, so the death is the scope's own grave) against the rescue
/// (`rescue` — a surviving home still carries the name: the inline
/// chain's definition-site truth, the rider's root home, or the
/// master snapshot). A shadow death with a rescue is the outer
/// binding living on; a face with neither birthplace nor rescue is
/// the orphan — a binding outlived its home and nothing re-supplies.
pub(super) fn checker_burial(
    name: &str,
    ptr: Option<NodeId>,
    born_here: bool,
    rescue: bool,
    rescuer: &str,
) {
    if !enabled() {
        return;
    }
    with(|o| {
        if ptr.is_some() {
            o.record(format!(
                "{} ⚑checker-burial '{}' carried {} in a dying frame — {}",
                o.ctx(),
                name,
                face(ptr),
                match (born_here, rescue) {
                    (true, true) => {
                        format!(
                            "the face was born in this frame and dies with it; the \
                             outer binding still answers (the {} re-supplies)",
                            rescuer
                        )
                    }
                    (true, false) => {
                        "the face was born in this frame and dies with it — the \
                         scope owns its grave, nothing re-supplies and nothing owes one"
                            .to_string()
                    }
                    (false, true) => {
                        format!("masked: the {} re-supplies the binding", rescuer)
                    }
                    (false, false) => {
                        "UNMASKED: the binding outlived this frame and nothing \
                         re-supplies — the checker-side orphan"
                            .to_string()
                    }
                },
            ));
            if !born_here && !rescue {
                o.orphan_trips += 1;
            }
        }
    });
}

/// A fn resolution answered. The tier IS the diagnosis: at top level
/// the frames digest comes back empty and the master snapshot
/// answers — with whatever the defcollection last left there.
pub(super) fn resolve_fn(
    name: &str,
    tier: Tier,
    answered: Option<Option<NodeId>>,
    frames_digest: &str,
) {
    if !enabled() {
        return;
    }
    with(|o| {
        o.record(format!(
            "{} →resolve '{}' tier={} → {} · frames{}",
            o.ctx(),
            name,
            tier.label(),
            match answered {
                Some(Some(p)) => face(Some(p)),
                Some(None) => "Some(None) — a known value binding".to_string(),
                None => "miss — no tier carries the name".to_string(),
            },
            frames_digest,
        ));
    });
}

// ── the report ───────────────────────────────────────────────────────

/// End of analysis: the final defcollection table, the event log,
/// the trip counters, the strict gate.
pub(super) fn finish() {
    if !enabled() {
        return;
    }
    with(|o| {
        eprintln!("[omni] ══ omni report ══");
        for note in &o.chain_notes {
            eprintln!("[omni] defcollection · {note}");
        }
        eprintln!(
            "[omni] events: {} · trips: orphan-burial {} (hard) · root-drag {} (soft) · chain-freeze {} (hard)",
            o.events.len(),
            o.orphan_trips,
            o.drag_trips,
            o.chain_trips,
        );
        for ev in &o.events {
            eprintln!("[omni]   {}", ev.line);
        }
        if o.orphan_trips > 0 || o.chain_trips > 0 {
            eprintln!(
                "[omni] ⚑ {} hard trip(s) — the scope law the omni layer guards was broken",
                o.orphan_trips + o.chain_trips,
            );
            if strict() {
                panic!("omni: hard invariant tripped under ALM_OMNI_STRICT");
            }
        }
        eprintln!("[omni] ══ end ══");
    });
}
