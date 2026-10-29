//! The walk-side use-site pinning discipline. At the sites where a
//! value's USE forces its kind — conditions (Bool), arithmetic operands
//! (the pair discipline), index keys (Int) — a nominal unknown is pinned
//! to a scalar in the lattice's constraint store. The WALK lands those
//! pins itself, at the very sites it already visits, alongside the
//! checking half.
//!
//! Equivalence discipline: the walk pins ONLY what its own view can
//! prove the checker would pin identically — a SUBSET by construction.
//! The walk derives, per expression, a *node view* (which shared unknown
//! node — the boundary seed, a still-Pending site id, a function return
//! node — the checker's resolved type of
//! that expression rides) and a *scalar view* (unresolved node / decided
//! scalar / other). Everything the walk cannot see (chained scalar
//! aliases through checker unifications, per-call parameter instances,
//! nested pending reads) stays walk-blind: the checker's own pin still
//! lands there, unchanged. A walk pin and the checker pin it preempts
//! bind the same resolved head to the same scalar — the final store,
//! and every fact derived from it, is identical.
//!
//! Pins fire ONLY in the recorded pass (`rec.on()`) and ONLY at the
//! TOP LEVEL (`fn_walk` empty): the fixpoint never pins and never
//! consults the store for its lattice decisions — the recorded pass's
//! walk may read earlier statements' pins, but only through `resolve`,
//! which is order-independent for
//! these value pins. Walk pins never feed back into
//! `site_elem`/scope shapes, so the recorded pass keeps reproducing the
//! fixpoint's lattice state exactly. Inside function bodies the
//! checker's call-time inlining keeps the pin monopoly: a called body
//! gets identical pins there, and a never-called body must stay
//! pin-free — a body-local pin would leak module-global facts the
//! checker never made (the seed's `boundary_elem`, row-read sites in
//! `check_row_reads`).
//!
//! The subset discipline is pinned differentially: with the lever off
//! (`analyze_with(ctx, false)`), the checker's pins alone must
//! reproduce the byte-identical pipeline output —
//! `walk_pins_are_a_pure_subset_over_the_corpus`.

use super::*;

/// What the walk can prove about the checker's resolved type of one
/// expression at a use site.
#[derive(Clone)]
enum ScalarView {
    /// it rides this still-unresolved unknown (already resolved to the
    /// chain head — the node a pin must bind)
    Unknown(usize),
    /// it is this decided scalar (a literal, or a node pinned earlier)
    Scalar(Ty),
    /// anything else — tables, Any, or walk-blind: no pin is derivable
    Other,
}

impl Analyzer {
    // ---- the views ----

    /// The shared unknown node the checker's resolved type of `expr`
    /// rides, when the walk's own state can name it. Structural — no
    /// resolution; `scalar_view` resolves.
    fn node_view(&self, expr: &Expr) -> Option<usize> {
        match expr {
            Expr::Identifier { name, .. } => self.name_node(name),
            // a cell read: the base's elem rides the seed, a pending
            // site, or a pending-table function return
            Expr::Index { obj, .. } | Expr::Field { obj, .. } => match obj.as_ref() {
                Expr::Identifier { .. } => self.read_elem_node(obj),
                Expr::Call { .. } => self.call_read_node(obj),
                _ => None,
            },
            // a call value: the function's return node when the walk's
            // return shape is still a scalar Pending
            Expr::Call { .. } => self.call_value_node(expr),
            _ => None,
        }
    }

    fn name_node(&self, name: &str) -> Option<usize> {
        self.walk
            .scalar_nodes
            .iter()
            .rev()
            .find_map(|s| s.get(name).copied())
    }

    fn single_pending_head(&self, sites: impl Iterator<Item = usize>) -> Option<usize> {
        let mut heads: BTreeSet<usize> = BTreeSet::new();
        for s in sites {
            if self.lattice.site_elem[s] != Pending {
                // a decided site joins the elem — the checker's view is
                // decided (or adoption's Any), not a scalar unknown
                return None;
            }
            match self.lattice.unknowns.resolve(&Ty::Unknown(s)) {
                Ty::Unknown(head) => {
                    heads.insert(head);
                }
                _ => return None,
            }
        }
        match heads.len() {
            1 => heads.iter().next().copied(),
            _ => None,
        }
    }

    /// The elem unknown of a read off a named base — the exact node the
    /// checker's scope entry for that name carries.
    fn read_elem_node(&self, base: &Expr) -> Option<usize> {
        let Expr::Identifier { name, .. } = base else {
            return None;
        };
        let Ok((_, bind)) = self.resolve(None, name) else {
            return None;
        };
        if bind.aliases.contains(&NULL_ROOT) || bind.aliases.contains(&MOVED_ROOT) {
            return None;
        }
        if bind.aliases.contains(&BOUNDARY_ROOT) {
            return Some(self.lattice.unknowns.boundary_seed());
        }
        if !matches!(bind.ty, Tbl(_)) {
            return None;
        }
        let real = bind
            .aliases
            .iter()
            .copied()
            .filter(|s| !is_root(s) && !is_ghost(s));
        self.single_pending_head(real)
    }

    /// The scalar unknown a call's VALUE rides: the function's return
    /// node, when the walk's return shape is still a plain Pending.
    fn call_value_node(&self, expr: &Expr) -> Option<usize> {
        let (fn_ptr, shape) = self.call_shape(expr)?;
        if matches!(shape.ty, Pending) {
            self.lattice.unknowns.fn_ret_node(fn_ptr)
        } else {
            None
        }
    }

    /// The elem unknown of a read off a call base: the pending site of
    /// a still-Pending table return.
    fn call_read_node(&self, call: &Expr) -> Option<usize> {
        let (_, shape) = self.call_shape(call)?;
        match &shape.ty {
            Tbl(inner) if matches!(**inner, Pending) => {
                let real = shape
                    .aliases
                    .iter()
                    .copied()
                    .filter(|s| !is_root(s) && !is_ghost(s));
                self.single_pending_head(real)
            }
            _ => None,
        }
    }

    fn call_shape(&self, expr: &Expr) -> Option<(NodeId, &TableShape)> {
        let Expr::Call { callee, .. } = expr else {
            return None;
        };
        let Expr::Identifier { name, .. } = callee.as_ref() else {
            return None;
        };
        let fn_ptr = self.resolve_fn(name)?;
        let shape = self.fn_ret_shapes.get(&fn_ptr)?;
        Some((fn_ptr, shape))
    }

    fn scalar_view(&self, expr: &Expr, walk_ty: &Ty) -> ScalarView {
        if let Some(node) = self.node_view(expr) {
            return match self.lattice.unknowns.resolve(&Ty::Unknown(node)) {
                Ty::Unknown(head) => ScalarView::Unknown(head),
                t if pinned_scalar(&t) => ScalarView::Scalar(t),
                _ => ScalarView::Other,
            };
        }
        match walk_ty {
            t if pinned_scalar(t) => ScalarView::Scalar(t.clone()),
            _ => ScalarView::Other,
        }
    }

    // ---- the pins (recorded pass only; each mirrors the checker's
    // discipline at the same site, binding the resolved head) ----

    /// Walk-side pins are a TOP-LEVEL discipline. Inside function
    /// bodies the checking half's call-time inlining owns every pin: a
    /// called body's pins land there with identical values, and a
    /// NEVER-CALLED body must stay pin-free — its pins would leak
    /// module-global facts the checker never made (the boundary seed's
    /// elem kind through `boundary_elem`, row-read sites through
    /// `check_row_reads`).
    fn pins_armed(&self, rec: Gate) -> bool {
        rec.on() && self.walk_pins && self.fn_walk.is_empty()
    }

    // ---- the computed-scalar discipline (recorded pass, top level) ----

    /// After an operator's use-site pins have landed, an operand whose
    /// node the pins closed answers its scalar — and where the checking
    /// half's own discipline at the same operator would return a type
    /// WITHOUT error, the walk binds that type directly, so the walk's
    /// binding is the value view (`local x = arg[0] + 1` binds Int) and
    /// the name→type view reproduces it with no held `top` entry. Where
    /// the walk stays blind (chained checker unifications, per-call
    /// instances) or the checker would refuse (mixed numeric kinds on
    /// the narrowing operators), these return None: the walk's binding
    /// stays Pending and the checker carries or rejects it, exactly as
    /// before — the subset discipline, one level up.
    ///
    /// A same-kind numeric pair resolves to the arithmetic result kind
    /// (`infer_numeric_pair` + the checker's result table).
    pub(super) fn computed_arith_scalar(
        &self,
        rec: Gate,
        l: &Expr,
        lt: &Ty,
        r: &Expr,
        rt: &Ty,
    ) -> Option<Ty> {
        if !self.pins_armed(rec) {
            return None;
        }
        let num = |e: &Expr, t: &Ty| match self.scalar_view(e, t) {
            ScalarView::Scalar(k) if matches!(k, Int | Flt) => Some(k),
            _ => None,
        };
        match (num(l, lt), num(r, rt)) {
            (Some(a), Some(b)) if a == b => Some(a),
            _ => None,
        }
    }

    /// Division widens: any two resolved numerics (a mix included — the
    /// checker's '/' accepts it) answer Float.
    pub(super) fn computed_div_scalar(
        &self,
        rec: Gate,
        l: &Expr,
        lt: &Ty,
        r: &Expr,
        rt: &Ty,
    ) -> Option<Ty> {
        if !self.pins_armed(rec) {
            return None;
        }
        let num = |e: &Expr, t: &Ty| matches!(self.scalar_view(e, t), ScalarView::Scalar(k) if matches!(k, Int | Flt));
        (num(l, lt) && num(r, rt)).then_some(Flt)
    }

    /// Unary '-' preserves its operand's resolved numeric kind.
    pub(super) fn computed_neg_scalar(&self, rec: Gate, e: &Expr, t: &Ty) -> Option<Ty> {
        if !self.pins_armed(rec) {
            return None;
        }
        match self.scalar_view(e, t) {
            ScalarView::Scalar(k) if matches!(k, Int | Flt) => Some(k),
            _ => None,
        }
    }

    /// The condition/not/and/or discipline (`pin_bool`): an unresolved
    /// operand is pinned to Boolean.
    pub(super) fn pin_bool_use(&mut self, rec: Gate, expr: &Expr, walk_ty: &Ty) {
        if !self.pins_armed(rec) {
            return;
        }
        if let ScalarView::Unknown(head) = self.scalar_view(expr, walk_ty) {
            let _ = self.lattice.unknowns.bind(head, Bool);
        }
    }

    /// The index-key and unary-minus discipline: an unresolved operand
    /// is pinned to Integer.
    pub(super) fn pin_int_use(&mut self, rec: Gate, expr: &Expr, walk_ty: &Ty) {
        if !self.pins_armed(rec) {
            return;
        }
        if let ScalarView::Unknown(head) = self.scalar_view(expr, walk_ty) {
            let _ = self.lattice.unknowns.bind(head, Int);
        }
    }

    /// The arithmetic-pair discipline (`infer_numeric_pair`): a numeric
    /// beside an unknown pins it to the numeric; two unknowns pin both
    /// to Integer.
    pub(super) fn pin_numeric_pair(&mut self, rec: Gate, l: &Expr, lt: &Ty, r: &Expr, rt: &Ty) {
        if !self.pins_armed(rec) {
            return;
        }
        let lv = self.scalar_view(l, lt);
        let rv = self.scalar_view(r, rt);
        let num = |v: &ScalarView| matches!(v, ScalarView::Scalar(t) if matches!(*t, Int | Flt));
        match (&lv, &rv) {
            (a, b) if num(a) && num(b) => {}
            (ScalarView::Scalar(t), ScalarView::Unknown(head)) if num(&lv) => {
                let _ = self.lattice.unknowns.bind(*head, t.clone());
            }
            (ScalarView::Unknown(head), ScalarView::Scalar(t)) if num(&rv) => {
                let _ = self.lattice.unknowns.bind(*head, t.clone());
            }
            (ScalarView::Unknown(a), ScalarView::Unknown(b)) => {
                let _ = self.lattice.unknowns.bind(*a, Int);
                let _ = self.lattice.unknowns.bind(*b, Int);
            }
            _ => {}
        }
    }

    /// The equality-pair discipline (`pin_scalar_pair`): a scalar beside
    /// an unknown pins it to the scalar; two unknowns pin nothing.
    pub(super) fn pin_scalar_pair(&mut self, rec: Gate, l: &Expr, lt: &Ty, r: &Expr, rt: &Ty) {
        if !self.pins_armed(rec) {
            return;
        }
        let lv = self.scalar_view(l, lt);
        let rv = self.scalar_view(r, rt);
        let scalar = |v: &ScalarView| matches!(v, ScalarView::Scalar(t) if pinned_scalar(t));
        match (&lv, &rv) {
            (ScalarView::Scalar(t), ScalarView::Unknown(head)) if scalar(&lv) => {
                let _ = self.lattice.unknowns.bind(*head, t.clone());
            }
            (ScalarView::Unknown(head), ScalarView::Scalar(t)) if scalar(&rv) => {
                let _ = self.lattice.unknowns.bind(*head, t.clone());
            }
            _ => {}
        }
    }

    // ---- the binding bookkeeping (fixpoint too: structural, no pins) ----

    /// Records (or clears) a declaration's scalar node from its RHS —
    /// mirroring the checker's scope entry: `local mode = arg[0]` binds
    /// mode to the seed node exactly as the checker's scope does.
    pub(super) fn note_decl_scalar_node(&mut self, name: &str, rhs: &Expr) {
        let entry = self.node_view(rhs);
        let scope = self.walk.scalar_nodes.last_mut().unwrap();
        match entry {
            Some(id) => {
                scope.insert(name.to_string(), id);
            }
            None => {
                scope.remove(name);
            }
        }
    }

    /// The assignment counterpart, writing at the depth that holds the
    /// name (mirroring the scope update).
    pub(super) fn note_assign_scalar_node(&mut self, name: &str, rhs: &Expr) {
        let entry = self.node_view(rhs);
        let depth = self
            .walk
            .scalar_nodes
            .iter()
            .rposition(|s| s.contains_key(name))
            .unwrap_or(self.walk.scalar_nodes.len() - 1);
        match entry {
            Some(id) => {
                self.walk.scalar_nodes[depth].insert(name.to_string(), id);
            }
            None => {
                self.walk.scalar_nodes[depth].remove(name);
            }
        }
    }
}
