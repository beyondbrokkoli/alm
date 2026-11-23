use super::*;

/// One enclosing conversion loop while the post-walk scan runs. The
/// frame mirrors the emission-time context the lowerer used to keep:
/// the plan's name sets, plus the guard-stability and shadowing facts
/// measured from THIS loop's header, which is where the old
/// register-identity match took its guard register.
#[derive(Clone)]
struct LaneFrame {
    loop_id: NodeId,
    guard: String,
    pre_header: BTreeSet<String>,
    nested: BTreeSet<String>,
    /// The guard name was assigned somewhere since this loop's header;
    /// assignments persist past every enclosing block's end.
    guard_assigned: bool,
    /// The guard name was shadowed by a declaration inside the current
    /// block; shadows lift when the block ends.
    guard_shadow: bool,
    /// Names whose current binding differs from the binding this loop's
    /// header saw; block-scoped, like `guard_shadow`.
    shadowed: BTreeSet<String>,
    /// The guard's compile-time entry value at this loop's header, from
    /// the constant environment; offset keys need it to prove their
    /// first key lands at or after zero.
    entry_const: Option<i64>,
    /// The plan's minted lower bound on the same entry (an
    /// under-approximation through Var chains): the gate reads the
    /// exact value when known, this bound when not.
    entry_lb: Option<i64>,
}

impl LaneFrame {
    fn guard_live(&self) -> bool {
        !self.guard_assigned && !self.guard_shadow
    }
}

/// The per-frame state a block entry snapshots and its exit restores:
/// shadow effects lift at the block's end, assignment kills never do.
type LaneSnapshot = Vec<(bool, bool, BTreeSet<String>)>;

fn snapshot(frames: &[LaneFrame]) -> LaneSnapshot {
    frames
        .iter()
        .map(|f| (f.guard_assigned, f.guard_shadow, f.shadowed.clone()))
        .collect()
}

fn restore(frames: &mut [LaneFrame], saved: &LaneSnapshot) {
    for (f, s) in frames.iter_mut().zip(saved) {
        f.guard_shadow = s.1;
        f.shadowed = s.2.clone();
    }
}

/// Compile-time integer knowledge of names, mirroring the binding
/// semantics the lowerer's registers carry: every visible binding holds
/// a constant or a kill, an assignment kills the innermost visible
/// binding wherever it was declared (kills persist past block ends),
/// and a declaration shadows for the current block only — at the
/// block's end the shadow lifts and the outer binding resurfaces with
/// its own pre-block state, which assignments under the shadow never
/// touched.
#[derive(Clone)]
struct ConstEnv {
    /// Every visible binding: `Some(v)` = the binding's value is the
    /// literal `v`, `None` = the binding exists but its value is not a
    /// known constant. Absent = no binding by that name.
    bindings: BTreeMap<String, Option<i64>>,
    /// One shadow record per open block: the names declared in it,
    /// each mapped to the outer binding's state to restore at the
    /// block's end (`None` = the name had no binding before it).
    shadows: Vec<BTreeMap<String, Option<Option<i64>>>>,
}

impl ConstEnv {
    fn new() -> Self {
        ConstEnv {
            bindings: BTreeMap::new(),
            shadows: vec![BTreeMap::new()],
        }
    }

    fn get(&self, name: &str) -> Option<i64> {
        self.bindings.get(name).copied().flatten()
    }

    fn declare(&mut self, name: &str, init: Option<i64>) {
        let prev = self.bindings.get(name).copied();
        self.shadows
            .last_mut()
            .expect("the root block never closes")
            .insert(name.to_string(), prev);
        self.bindings.insert(name.to_string(), init);
    }

    fn assign(&mut self, name: &str) {
        self.bindings.insert(name.to_string(), None);
    }

    fn enter_block(&mut self) {
        self.shadows.push(BTreeMap::new());
    }

    fn exit_block(&mut self) {
        let Some(lifted) = self.shadows.pop() else {
            return;
        };
        for (name, prev) in lifted {
            match prev {
                Some(state) => {
                    self.bindings.insert(name, state);
                }
                None => {
                    self.bindings.remove(&name);
                }
            }
        }
    }
}

/// One plan's entry facts for the lane: the pre-header and nested
/// name sets plus the minted lower bound on the loop entry.
type PlanSets = (BTreeSet<String>, BTreeSet<String>, Option<i64>);

struct LaneSink<'a> {
    plans: &'a BTreeMap<NodeId, PlanSets>,
    /// The walk's per-statement row-kind facts: a store whose value
    /// inferred table-typed, ctor spelling or not. The lane's row laws
    /// (the row-stored decline and the row_stored marking) key on this
    /// union with the syntactic TableCtor check.
    row_values: &'a BTreeSet<NodeId>,
    fast: BTreeMap<NodeId, FastStoreElig>,
    ctor: BTreeMap<NodeId, BTreeSet<NodeId>>,
    /// [index-base] The surface index base the walk ran under;
    /// `GuardOffset` shapes arrive pre-folded from recognition, and a
    /// bare `Guard`'s physical offset `-index_base` is derived at its
    /// consumers here.
    index_base: i64,
    /// The claim groups: one per (loop, base). A group's first sighting
    /// of a KeyShape rides the lane; a later sighting of the same shape
    /// is a same-slot repeat (the P21 law) and declines, while a
    /// distinct shape collapses the group. With more than one key shape
    /// on the same (loop, base), the store windows overlap across trips:
    /// at trip i the guard store writes slot i and the offset store
    /// writes slot i + k, and the next trip's guard store clobbers the
    /// offset row of trip i - 1 with no runtime face in between — not
    /// even the first sighting is guaranteed a fresh slot then, so the
    /// whole group falls to the checked face (its replace-reclaim speaks
    /// the displacement law) and widens nothing.
    claims: BTreeMap<(NodeId, String), LaneClaims>,
    /// Every base that took a row kind store earlier in the walk. The
    /// table the name binds holds rows at those slots: a later loop's
    /// first sighting on the same base is not proven a fresh slot, so it
    /// keeps the checked face too (the sequential-fill twin of the group
    /// law). Scalar-only fills never enter the set — the cells-hold-one-
    /// kind law forbids a row-and-scalar mix on one table binding —
    /// so plain integer conversion loops stay claimed across fills.
    row_stored: BTreeSet<String>,
    /// Runtime loop nesting at the scan: incremented entering every
    /// while body (planned or not), decremented leaving it. A claim
    /// whose own loop is the only enclosing loop owns the whole trip
    /// dimension over its body; deeper claims re-run their store
    /// domain once per enclosing trip, and the slots the claim touches
    /// are the enclosing trips' rows — nothing to prove fresh there.
    loop_depth: u32,
    /// The runtime loop ids enclosing the scan right now, one entry
    /// per open body (the id-side twin of `loop_depth`).
    active_loops: Vec<NodeId>,
    /// Every plan loop the scan has completed, as (guard, loop id,
    /// the runtime loops that enclosed it when it ran). A loop's entry
    /// facts describe its first entry only; this registry is what the
    /// late-assignment law reads to decide whether a later store can
    /// change a re-entry.
    completed: Vec<(String, NodeId, BTreeSet<NodeId>)>,
    /// Plan loops whose guard took an assignment after the loop while
    /// a shared enclosing runtime loop was still active: their entry
    /// facts are stale for re-entries, so every claim of the loop is
    /// dead (unclaimed in place) and later sightings decline.
    late_assigned: BTreeSet<NodeId>,
}

/// One (loop, base) group. `shapes` carries every resolvable key shape
/// the walk saw; `minted` pairs the facts' statement ids with their
/// physical offsets (the plan's reserve widening reads only survivors);
/// `poisoned` is the group-wide decline once a distinct shape or an
/// unanalyzable store reached it.
#[derive(Default)]
struct LaneClaims {
    shapes: BTreeSet<KeyShape>,
    minted: Vec<(NodeId, i64)>,
    poisoned: bool,
}

impl Analyzer {
    /// [fast-lane] Mint the fast-store facts over the whole program now
    /// that every conversion loop's reserve plan is final: store
    /// eligibility depends on inner loops' plans too, so it cannot ride
    /// the walk itself. This is the one mint of `fast_stores` —
    /// presence in the map is the whole lane decision (the P4 facts
    /// half; the lowerer's `choose_store_lane` consumption is L7's).
    pub(super) fn mint_fast_lane(&mut self, stmts: &[Stmt]) {
        let sets: BTreeMap<NodeId, PlanSets> = self
            .layout
            .reserve_plans
            .iter()
            .map(|(&id, p)| {
                (
                    id,
                    (
                        p.pre_header.iter().cloned().collect(),
                        p.nested.iter().cloned().collect(),
                        p.entry_lb,
                    ),
                )
            })
            .collect();
        let mut sink = LaneSink {
            plans: &sets,
            row_values: &self.own.row_value_stores,
            fast: BTreeMap::new(),
            ctor: BTreeMap::new(),
            claims: BTreeMap::new(),
            row_stored: BTreeSet::new(),
            loop_depth: 0,
            active_loops: Vec::new(),
            completed: Vec::new(),
            late_assigned: BTreeSet::new(),
            // [index-base] the one seam the scan reads the surface's
            // law at (the P5 boundary: the facts stay base-free).
            index_base: self.surface.index_base(),
        };
        scan_stmts(stmts, &mut Vec::new(), &mut ConstEnv::new(), &mut sink);
        for (loop_id, hits) in sink.ctor {
            if let Some(plan) = self.layout.reserve_plans.get_mut(&loop_id) {
                plan.ctor_reserves = hits;
            }
        }
        // The plan's widest offset comes from the surviving mints only:
        // a collapsed group's facts were unclaimed (its stores ride the
        // checked face), and a never-minted sighting contributes
        // nothing, so the reserves keep the raw bound when nothing was
        // proven.
        let mut key_offsets: BTreeMap<NodeId, Option<i64>> = BTreeMap::new();
        for ((loop_id, _), rec) in &sink.claims {
            if rec.poisoned {
                continue;
            }
            for (_, k) in &rec.minted {
                let entry = key_offsets.entry(*loop_id).or_insert(None);
                if entry.is_none_or(|current| *k > current) {
                    *entry = Some(*k);
                }
            }
        }
        for (loop_id, max_k) in key_offsets {
            if let Some(plan) = self.layout.reserve_plans.get_mut(&loop_id) {
                plan.key_offset = max_k;
            }
        }
        self.layout.fast_stores = sink.fast;
    }
}

/// One resolvable sighting's group verdict: `FallThrough` continues
/// the mint flow, `Decline` stops the frame walk, and `Collapse` has
/// already unclaimed the group's minted facts in place.
enum Sighting {
    FallThrough,
    Decline,
    Collapse,
}

impl LaneSink<'_> {
    /// The group decline for one (loop, base): every minted fact
    /// unclaims (its store compiles to the checked face) and the group
    /// declines every later sighting — same-shape repeats included,
    /// whose checked stores keep set_core's replace-reclaim. A
    /// poisoned group stays dead even when the poison arrived at a
    /// sighting that minted nothing: a later same-shape sighting gets
    /// no claim from it either.
    fn poison(&mut self, loop_id: NodeId, base: &str) {
        let rec = self.claims.entry((loop_id, base.to_string())).or_default();
        if rec.poisoned {
            return;
        }
        let dead = std::mem::take(&mut rec.minted);
        rec.poisoned = true;
        for (stmt_id, _) in dead {
            self.fast.remove(&stmt_id);
        }
    }

    /// Book one sighting into its (loop, base) group. The poisoned
    /// group declines. A same-shape repeat is the P21 law: the first
    /// sighting of a slot keeps the claim (its slot is fresh), the
    /// repeats ride the checked face. A distinct new shape collapses
    /// the group even when no earlier sighting minted: a mintless
    /// sighting still runs on the checked face and populates slots
    /// across trips, and the new shape's fresh-slot proof cannot see
    /// those checked writes — when the new shape's offset is the
    /// smaller one, its fast window lands on slots the checked shape
    /// already filled, with no reclaim face in between. So any two
    /// distinct shapes on one (loop, base) poison the group.
    fn book_sighting(&mut self, loop_id: NodeId, base: &str, shape: KeyShape) -> Sighting {
        let rec = self.claims.entry((loop_id, base.to_string())).or_default();
        if rec.poisoned {
            return Sighting::Decline;
        }
        if !rec.shapes.insert(shape) {
            return Sighting::Decline;
        }
        if rec.shapes.len() > 1 {
            let dead = std::mem::take(&mut rec.minted);
            rec.poisoned = true;
            for (stmt_id, _) in dead {
                self.fast.remove(&stmt_id);
            }
            return Sighting::Collapse;
        }
        Sighting::FallThrough
    }

    /// The late-assignment law: a completed plan loop's entry facts
    /// describe its first entry only (the walk minted them before the
    /// enclosing body's tail was recorded, and the scan's frame is
    /// gone). An assignment to the guard after the loop, while any
    /// runtime loop that already enclosed the loop is still active,
    /// changes the loop's re-entries — the shared back edge re-runs
    /// the enclosing body and reaches the loop again with the new
    /// value, before which the admission gate cannot prove the first
    /// key lands at or after zero. Every claim of the loop dies (its
    /// minted facts unclaimed in place, the poison service's move) and
    /// later sightings decline. With no shared enclosing loop the loop
    /// cannot run again after this assignment, and nothing dies: the
    /// first entry's facts stay the only facts.
    fn note_late_assignment(&mut self, name: &str) {
        let victims: Vec<NodeId> = self
            .completed
            .iter()
            .filter(|(guard, loop_id, enclosing)| {
                guard == name
                    && !self.late_assigned.contains(loop_id)
                    && enclosing.iter().any(|e| self.active_loops.contains(e))
            })
            .map(|(_, loop_id, _)| *loop_id)
            .collect();
        for loop_id in victims {
            self.late_assigned.insert(loop_id);
            let bases: Vec<String> = self
                .claims
                .keys()
                .filter(|(l, _)| *l == loop_id)
                .map(|(_, b)| b.clone())
                .collect();
            for base in bases {
                self.poison(loop_id, &base);
            }
        }
    }
}

fn scan_stmts(
    stmts: &[Stmt],
    frames: &mut Vec<LaneFrame>,
    env: &mut ConstEnv,
    sink: &mut LaneSink,
) {
    for stmt in stmts {
        scan_stmt(stmt, frames, env, sink);
    }
}

fn scan_stmt(stmt: &Stmt, frames: &mut Vec<LaneFrame>, env: &mut ConstEnv, sink: &mut LaneSink) {
    match stmt {
        Stmt::LocalDecl { names, exprs, .. } => {
            for expr in exprs {
                scan_expr(expr, sink);
            }
            for (idx, name) in names.iter().enumerate() {
                let init = match exprs.get(idx) {
                    Some(Expr::Integer { value, .. }) => Some(*value),
                    _ => None,
                };
                // The decl-side twin of the store-side marking: an init
                // that is not a provably empty fresh table may house
                // rows at construction (`local t = { {} }`, a moved-in
                // binding, a call's answer), and no IndexAssign ever
                // announces them — so the base marks fail-closed and
                // later row stores keep the fresh-slot proof honest.
                // An empty ctor stays unmarked (the canonical fill
                // target), and scalar inits mark harmlessly: a scalar
                // base never takes a row store, and a re-declared name
                // inherits the walk-wide decline by design.
                if !matches!(exprs.get(idx), Some(Expr::TableCtor { entries, .. }) if entries.is_empty())
                {
                    sink.row_stored.insert(name.clone());
                }
                env.declare(name, init);
                for frame in frames.iter_mut() {
                    if frame.guard == *name {
                        frame.guard_shadow = true;
                    }
                    frame.shadowed.insert(name.clone());
                }
            }
        }
        Stmt::Assignment { name, expr, .. } => {
            scan_expr(expr, sink);
            // Same decl-side law for a re-binding: only a fresh empty
            // table is provably row-free; anything else marks.
            if !matches!(expr, Expr::TableCtor { entries, .. } if entries.is_empty()) {
                sink.row_stored.insert(name.clone());
            }
            env.assign(name);
            for frame in frames.iter_mut() {
                if frame.guard == *name {
                    frame.guard_assigned = true;
                }
            }
            sink.note_late_assignment(name);
        }
        Stmt::IndexAssign {
            obj, key, value, ..
        } => {
            scan_expr(obj, sink);
            scan_expr(key, sink);
            scan_expr(value, sink);
            // The row kind is the walk's Tbl-value fact (ctor spelling
            // or not — `t[i] = r` with r a row infers Tbl too) plus the
            // syntactic ctor as a belt for any arm the walk declined.
            // The ctor reserve bookkeeping below stays syntactic: the
            // lowerer mints the row's own reserve under a TableCtor
            // check, so a fact-only row kind would reserve nothing.
            let is_ctor = matches!(value, Expr::TableCtor { .. });
            let row_kind = is_ctor || sink.row_values.contains(&stmt.id());
            claim_store(stmt.id(), obj, key, row_kind, frames, sink);
            if is_ctor && let Some(base) = get_base_identifier(obj) {
                for frame in frames.iter().rev() {
                    if frame.nested.contains(base) {
                        sink.ctor
                            .entry(frame.loop_id)
                            .or_default()
                            .insert(stmt.id());
                        break;
                    }
                }
            }
        }
        Stmt::While {
            condition, body, ..
        } => {
            scan_expr(condition, sink);
            // The runtime loops enclosing this one, snapshotted before
            // it goes active: what a completed plan loop's
            // late-assignment verdict is measured against.
            let enclosing: BTreeSet<NodeId> = sink.active_loops.iter().copied().collect();
            let plan_guard = extract_guard(condition)
                .filter(|_| sink.plans.contains_key(&stmt.id()))
                .map(|(g, _)| g.to_string());
            let mut pushed = false;
            if let Some(guard) = plan_guard.as_deref()
                && let Some((pre_header, nested, entry_lb)) = sink.plans.get(&stmt.id())
            {
                frames.push(LaneFrame {
                    loop_id: stmt.id(),
                    guard: guard.to_string(),
                    pre_header: pre_header.clone(),
                    nested: nested.clone(),
                    guard_assigned: false,
                    guard_shadow: false,
                    shadowed: BTreeSet::new(),
                    entry_const: env.get(guard),
                    entry_lb: *entry_lb,
                });
                pushed = true;
            }
            sink.loop_depth += 1;
            sink.active_loops.push(stmt.id());
            scan_block(body, frames, env, sink);
            sink.active_loops.pop();
            sink.loop_depth -= 1;
            if pushed {
                frames.pop();
                sink.completed.push((
                    plan_guard.expect("pushed implies a guard"),
                    stmt.id(),
                    enclosing,
                ));
            }
        }
        Stmt::Do { body, .. } => {
            scan_block(body, frames, env, sink);
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            scan_expr(condition, sink);
            let saved = snapshot(frames);
            let saved_env = env.clone();
            let mut then_frames = frames.clone();
            let mut then_env = env.clone();
            scan_stmts(then_body, &mut then_frames, &mut then_env, sink);
            let mut else_frames = frames.clone();
            let mut else_env = env.clone();
            scan_stmts(else_body, &mut else_frames, &mut else_env, sink);
            for (i, frame) in frames.iter_mut().enumerate() {
                frame.guard_assigned =
                    saved[i].0 || then_frames[i].guard_assigned || else_frames[i].guard_assigned;
            }
            restore(frames, &saved);
            // A binding's constant survives the join only when both
            // arms left it at the same known constant — a name neither
            // arm touched trivially does, a name either arm killed or
            // changed does not, and nothing either arm declared leaks
            // (the arms scanned on clones). Spending a stale constant
            // here is the F2 corruption: the entry the loop actually
            // takes can be the smaller arm's value.
            *env = saved_env;
            let names: Vec<String> = env.bindings.keys().cloned().collect();
            for name in names {
                let t = then_env.bindings.get(&name).copied().flatten();
                let e = else_env.bindings.get(&name).copied().flatten();
                if t != e || t.is_none() {
                    env.assign(&name);
                }
            }
        }
        Stmt::Print { exprs, .. } => {
            for e in exprs {
                scan_expr(e, sink);
            }
        }
        Stmt::Expr { expr, .. } => scan_expr(expr, sink),
        Stmt::Return { value, .. } => {
            if let Some(e) = value {
                scan_expr(e, sink);
            }
        }
        Stmt::Break { .. } => {}
    }
}

/// A nested block's statements run in sequence, and whatever they
/// assigned to a binding declared outside the block leaks out past the
/// block's end (the lowerer updates the visible binding in place),
/// while the block's own declarations lift at the end and the outer
/// bindings resurface with their pre-block state.
fn scan_block(
    stmts: &[Stmt],
    frames: &mut Vec<LaneFrame>,
    env: &mut ConstEnv,
    sink: &mut LaneSink,
) {
    let saved = snapshot(frames);
    env.enter_block();
    scan_stmts(stmts, frames, env, sink);
    for (frame, s) in frames.iter_mut().zip(&saved) {
        frame.guard_assigned = frame.guard_assigned || s.0;
    }
    restore(frames, &saved);
    env.exit_block();
}

/// One store site's lane laws. Pass one is the poison service (an
/// unanalyzable writer collapses the groups it reaches); pass two
/// books the sighting and, when every gate admits, mints the fast
/// fact. A row-kind value marks the base afterwards.
fn claim_store(
    stmt_id: NodeId,
    obj: &Expr,
    key: &Expr,
    row_kind: bool,
    frames: &[LaneFrame],
    sink: &mut LaneSink,
) {
    let Some(base) = get_base_identifier(obj) else {
        return;
    };
    // Pass one, the poison service: a plain-host store whose key
    // resolves under no live frame ("t[expr] = v") is a runtime writer
    // of unprovable slots, so every (loop, base) group it reaches
    // collapses — including a group minted earlier in this walk, whose
    // fresh-slot proof the unanalyzable writer undoes — and stays
    // dead for sightings that come later in the walk. A compound host
    // (`t[i][k] = v`) writes inside a row's cells, never `t`'s own
    // slots, so it poisons nothing.
    if matches!(obj, Expr::Identifier { .. }) {
        for frame in frames.iter().rev() {
            if guard_key_shape(key, &frame.guard, sink.index_base).is_none() {
                sink.poison(frame.loop_id, base);
            }
        }
    }
    for frame in frames.iter().rev() {
        if !frame.guard_live() {
            continue;
        }
        // The late-assignment law killed this loop's entry facts: no
        // admission from them again, whatever shape the key carries.
        if sink.late_assigned.contains(&frame.loop_id) {
            continue;
        }
        let Some(shape) = guard_key_shape(key, &frame.guard, sink.index_base) else {
            continue;
        };
        // [index-base] The key's physical offset: `GuardOffset` arrived
        // pre-folded at recognition; a bare `Guard` sits at
        // `-index_base`.
        let k_phys = match shape {
            KeyShape::Guard => -sink.index_base,
            KeyShape::GuardOffset(k) => k,
        };
        match sink.book_sighting(frame.loop_id, base, shape) {
            Sighting::Decline | Sighting::Collapse => continue,
            Sighting::FallThrough => {}
        }
        // One admission law for every key shape: the entry's exact
        // constant when known, the plan's minted lower bound when not,
        // and `first + k_phys >= 0` on the checked sum. A minted plan
        // passed `guard_provably_nonneg`, and a provably nonnegative
        // entry under-approximates to a bound `>= 0` — so a base-0
        // bare guard (offset 0) admits through the same formula
        // without an unconditional arm. An entry with neither a
        // constant nor a bound declines: the fast path must never
        // turn a negative key into a negative getelementptr.
        let first = frame.entry_const.or(frame.entry_lb);
        let admitted = matches!(first, Some(c) if c.checked_add(k_phys).is_some_and(|v| v >= 0));
        if !admitted {
            continue;
        }
        // The row-stored law (the sequential twin of the group law): a
        // row store into a base whose rows the walk already populated
        // is not proven a fresh slot, so it keeps the checked face,
        // whose replace-reclaim frees the displaced child. Scalar
        // values stay eligible: replacing a scalar needs no reclaim,
        // and the cells-hold-one-kind law forbids a row-and-scalar mix
        // on one table binding — so plain integer fills keep riding
        // the lane across fills.
        if row_kind && sink.row_stored.contains(base) {
            continue;
        }
        // The depth law: a claim whose own loop is the only enclosing
        // loop owns the whole trip dimension over it; a deeper claim
        // re-runs its store domain once per enclosing trip, and the
        // slots it touches are the enclosing trips' rows — reclaim
        // territory, so a row-kind claim keeps the checked face. A
        // scalar claim re-runs safely once per enclosing trip: it
        // replaces a scalar word wherever it lands, and the
        // cells-hold-one-kind law forbids rows on a scalar binding, so
        // there is nothing to reclaim at any depth (the staircase's
        // inner fill rides the lane).
        if row_kind && sink.loop_depth != 1 {
            continue;
        }
        // A plain-name store on a pre-header-reserved table rides the
        // existing reserve when the name still names the binding the
        // loop's header saw; anything the plan holds as a nested row
        // reserves its own row at the store.
        if matches!(obj, Expr::Identifier { .. })
            && frame.pre_header.contains(base)
            && !frame.shadowed.contains(base)
        {
            sink.fast.insert(
                stmt_id,
                FastStoreElig {
                    loop_id: frame.loop_id,
                    table: base.clone(),
                    key: shape,
                    row_reserve: false,
                },
            );
            if let Some(rec) = sink.claims.get_mut(&(frame.loop_id, base.clone())) {
                rec.minted.push((stmt_id, k_phys));
            }
            if row_kind {
                sink.row_stored.insert(base.clone());
            }
            return;
        }
        if frame.nested.contains(base) && matches!(obj, Expr::Identifier { .. }) {
            // A nested claim's host liveness is only a binding fact: a
            // plain-name host names the binding the plan reserved, so
            // the fast store's host register is the live table object
            // every trip. A compound host reads a runtime slot at store
            // time (`alm_tbl_get` of `t[k]`), and the slot's liveness is
            // a claim the nested plan never minted: a refusable writer
            // elsewhere in the body leaves that slot's zero word as the
            // read's answer, and the fast lane's header deref would
            // SIGSEGV on the null host with no runtime face in between.
            // Those stores ride the checked face, whose null arm speaks
            // the null-row-store guard — the faithful "attempt to index
            // a nil value" — instead of a bare fault.
            sink.fast.insert(
                stmt_id,
                FastStoreElig {
                    loop_id: frame.loop_id,
                    table: base.clone(),
                    key: shape,
                    row_reserve: true,
                },
            );
            if let Some(rec) = sink.claims.get_mut(&(frame.loop_id, base.clone())) {
                rec.minted.push((stmt_id, k_phys));
            }
            if row_kind {
                sink.row_stored.insert(base.clone());
            }
            return;
        }
    }
    // The mint-less path (a declined sighting, a collapsed group, an
    // unclaimable host, a shapeless base) still records a row store:
    // the base the name binds holds rows from here on, fail-closed,
    // name reuse included. A compound host writes inside a row's
    // cells and marks nothing.
    if row_kind && matches!(obj, Expr::Identifier { .. }) {
        sink.row_stored.insert(base.clone());
    }
}

/// Function bodies ride their own emission contexts, never the lanes
/// or the constants around their literals (a conversion loop's body
/// admits no calls), so both stacks start empty inside them. The
/// function's own stores face the function's trip counters only: the
/// depth counter and the active-loop registry reset for the body's
/// scan and restore after (an outer loop cannot re-enter the body; a
/// later call replays it with caller-controlled entries, which the
/// params-as-killed constants keep out of every admission). Parameters
/// enter as killed bindings — their values are the caller's, not any
/// outer same-named literal's. `row_stored` stays walk-wide — name
/// reuse across a call boundary keeps the fail-closed decline.
fn scan_expr(expr: &Expr, sink: &mut LaneSink) {
    match expr {
        Expr::Function { params, body, .. } => {
            let saved_depth = sink.loop_depth;
            let saved_loops = std::mem::take(&mut sink.active_loops);
            sink.loop_depth = 0;
            let mut fresh = Vec::new();
            let mut env = ConstEnv::new();
            for p in params {
                env.declare(p, None);
            }
            scan_stmts(body, &mut fresh, &mut env, sink);
            sink.loop_depth = saved_depth;
            sink.active_loops = saved_loops;
        }
        Expr::TableCtor { entries, .. } => {
            for (k, v) in entries {
                if let CtorKey::Expr(ke) = k {
                    scan_expr(ke, sink);
                }
                scan_expr(v, sink);
            }
        }
        Expr::Index { obj, key, .. } => {
            scan_expr(obj, sink);
            scan_expr(key, sink);
        }
        Expr::BinaryOp { left, right, .. } => {
            scan_expr(left, sink);
            scan_expr(right, sink);
        }
        Expr::UnaryOp { expr, .. } => scan_expr(expr, sink),
        Expr::Field { obj, .. } => scan_expr(obj, sink),
        Expr::Call { callee, args, .. } => {
            scan_expr(callee, sink);
            for a in args {
                scan_expr(a, sink);
            }
        }
        // leaves and module faces admit nothing to any lane
        Expr::Integer { .. }
        | Expr::Float { .. }
        | Expr::Boolean { .. }
        | Expr::String { .. }
        | Expr::Nil { .. }
        | Expr::Identifier { .. }
        | Expr::SysAllocCount { .. }
        | Expr::SysExecCount { .. }
        | Expr::FfiModule { .. }
        | Expr::AsyncModule { .. } => {}
    }
}
