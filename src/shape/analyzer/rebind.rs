use super::*;
pub(super) enum MixedPlan {
    NotMixed,
    Suppress,
    Fire {
        keeps: Vec<String>,
    },
    ArmSplit {
        tag: super::facts::TagSrc,
        nothing_on: bool,
        keeps: Vec<String>,
    },
}

impl Analyzer {
    pub(super) fn poison_moved(&mut self, depth: usize, name: &str) {
        self.walk.scopes[depth].insert(
            name.to_string(),
            TableShape {
                ty: Pending,
                layout: LayoutVerdict::default(),
                aliases: BTreeSet::from([MOVED_ROOT]),
                lineage: BTreeMap::new(),
            },
        );
        if let Some(scope) = self.walk.prov.get_mut(depth) {
            scope.remove(name);
        }
    }

    pub(super) fn arm_defers(&self, name: &str, depth: usize, arm: &TableShape) -> bool {
        arm.aliases.iter().any(is_ghost)
            && arm.lineage.keys().any(|o| {
                origin_housed(
                    &self.walk.scopes,
                    &self.lattice,
                    &self.own,
                    &self.reads,
                    *o,
                    depth,
                    name,
                )
            })
    }

    pub(super) fn arm_keeps(&self, name: &str, depth: usize, arm: &TableShape) -> Vec<String> {
        let mut release: BTreeSet<usize> = BTreeSet::new();
        for &r in arm.aliases.iter().filter(|s| !is_root(s)) {
            release.extend(release_set(&self.lattice, &self.own, &self.reads, r));
        }
        borrowers_of(
            &self.walk.scopes,
            &release,
            self.walk.scopes.len(),
            depth,
            name,
        )
    }

    pub(super) fn plan_arm(&self, name: &str, depth: usize, arm: &TableShape) -> bool {
        self.arm_defers(name, depth, arm)
    }

    pub(super) fn plan_mixed(&mut self, name: &str, depth: usize, shape: &TableShape) -> MixedPlan {
        use super::facts::TagSrc;
        let ghosts: Vec<usize> = shape.aliases.iter().copied().filter(is_ghost).collect();
        let sites: Vec<usize> = shape
            .aliases
            .iter()
            .copied()
            .filter(|s| !is_root(s) && !is_ghost(s))
            .collect();
        if ghosts.is_empty() || sites.is_empty() {
            return MixedPlan::NotMixed;
        }
        let union_housed = shape.lineage.keys().any(|o| {
            origin_housed(
                &self.walk.scopes,
                &self.lattice,
                &self.own,
                &self.reads,
                *o,
                depth,
                name,
            )
        });
        let fallback = |an: &Analyzer| -> MixedPlan {
            if union_housed {
                MixedPlan::Suppress
            } else {
                MixedPlan::Fire {
                    keeps: an.arm_keeps_union(name, depth, shape),
                }
            }
        };
        let Some(prov) = self
            .walk
            .prov
            .get(depth)
            .and_then(|s| s.get(name))
            .copied()
            .flatten()
        else {
            return fallback(self);
        };
        let arms: Vec<TableShape> = match prov {
            Prov::If(stmt) => self
                .join_arm_shapes
                .get(&(stmt, name.to_string()))
                .map(|(t, e)| vec![t.clone(), e.clone()]),
            Prov::Call(expr) => self.fn_ret_edge_shapes.get(&expr).cloned(),
        }
        .unwrap_or_default();
        let union: BTreeSet<usize> = arms
            .iter()
            .flat_map(|a| a.aliases.iter().copied())
            .filter(|s| !is_root(s))
            .collect();
        let mine: BTreeSet<usize> = shape
            .aliases
            .iter()
            .copied()
            .filter(|s| !is_root(s))
            .collect();
        if arms.is_empty() || union != mine {
            return fallback(self);
        }
        let defer: Vec<bool> = arms.iter().map(|a| self.plan_arm(name, depth, a)).collect();
        if defer.iter().all(|&d| d) {
            return MixedPlan::Suppress;
        }
        let keeps: Vec<String> = arms
            .iter()
            .zip(defer.iter())
            .filter(|(_, d)| !**d)
            .flat_map(|(a, _)| self.arm_keeps(name, depth, a))
            .collect();
        if defer.iter().all(|&d| !d) {
            return MixedPlan::Fire { keeps };
        }
        match prov {
            Prov::If(stmt) => {
                self.join_tags.insert(stmt, defer[0]);
                MixedPlan::ArmSplit {
                    tag: TagSrc::If(stmt),
                    nothing_on: defer[0],
                    keeps,
                }
            }
            Prov::Call(expr) => {
                self.call_tags.insert(expr, defer.clone());
                MixedPlan::ArmSplit {
                    tag: TagSrc::Call(expr),
                    nothing_on: true,
                    keeps,
                }
            }
        }
    }

    pub(super) fn arm_keeps_union(
        &self,
        name: &str,
        depth: usize,
        shape: &TableShape,
    ) -> Vec<String> {
        let mut release: BTreeSet<usize> = BTreeSet::new();
        for &r in shape.aliases.iter().filter(|s| !is_root(s)) {
            release.extend(release_set(&self.lattice, &self.own, &self.reads, r));
        }
        borrowers_of(
            &self.walk.scopes,
            &release,
            self.walk.scopes.len(),
            depth,
            name,
        )
    }

    pub(super) fn drop_reference(
        &mut self,
        rec: Gate,
        name: &str,
        stmt: &Stmt,
    ) -> Result<(), ShapeError> {
        let (depth, bind) = self.resolve(rec, name)?;
        let roots: Vec<usize> = bind
            .aliases
            .iter()
            .copied()
            .filter(|r| !is_root(r))
            .collect();
        if !roots.is_empty() && rec.on() {
            let mixed_ghost = roots.iter().any(is_ghost);
            let mixed_site = roots.iter().any(|s| !is_ghost(s));
            if mixed_ghost && mixed_site {
                match self.plan_mixed(name, depth, &bind) {
                    MixedPlan::NotMixed => {}
                    MixedPlan::Suppress => {
                        signal!(rec.on(), trace::TRACE_ROW_GHOST_DEFER);
                    }
                    MixedPlan::Fire { keeps } => {
                        signal!(rec.on(), trace::TRACE_ROW_GHOST_FIRE);
                        self.own.free_sites.insert(stmt as *const Stmt);
                        if !keeps.is_empty() {
                            signal!(rec.on(), trace::TRACE_ROW_KEEP_FREE);
                            self.own.free_keeps.insert(
                                stmt as *const Stmt,
                                keeps.into_iter().map(super::facts::Keep::Name).collect(),
                            );
                        }
                        signal!(rec.on(), trace::TRACE_SHAPE_DROP);
                    }
                    MixedPlan::ArmSplit {
                        tag,
                        nothing_on,
                        keeps,
                    } => {
                        signal!(rec.on(), trace::TRACE_JOIN_ARM_SPLIT);
                        self.own
                            .arm_free_sites
                            .entry(stmt as *const Stmt)
                            .or_default()
                            .push(super::facts::ArmFreeEntry {
                                carrier: name.to_string(),
                                tag,
                                nothing_on,
                                keeps: keeps.into_iter().map(super::facts::Keep::Name).collect(),
                            });
                        signal!(rec.on(), trace::TRACE_SHAPE_DROP);
                    }
                }
                self.walk.scopes[depth].insert(
                    name.to_string(),
                    TableShape {
                        ty: Pending,
                        layout: LayoutVerdict::default(),
                        aliases: BTreeSet::from([NULL_ROOT]),
                        lineage: BTreeMap::new(),
                    },
                );
                if let Some(scope) = self.walk.prov.get_mut(depth) {
                    scope.remove(name);
                }
                return Ok(());
            }
            let has_ghost = mixed_ghost;
            let origins_housed = bind.lineage.keys().any(|o| {
                origin_housed(
                    &self.walk.scopes,
                    &self.lattice,
                    &self.own,
                    &self.reads,
                    *o,
                    depth,
                    name,
                )
            });
            if has_ghost {
                if origins_housed {
                    signal!(rec.on(), trace::TRACE_ROW_GHOST_DEFER);
                } else {
                    signal!(rec.on(), trace::TRACE_ROW_GHOST_FIRE);
                }
            }
            if !origins_housed {
                let mut release: BTreeSet<usize> = BTreeSet::new();
                let mut keeps: Vec<super::facts::Keep> = Vec::new();
                for &r in &roots {
                    release.extend(self.node_release(r));
                }
                let mut harm = release.clone();
                for &r in &roots {
                    let h = self.harm_set(r);
                    harm.extend(h);
                }
                keeps.extend(
                    borrowers_of(
                        &self.walk.scopes,
                        &harm,
                        self.walk.scopes.len(),
                        depth,
                        name,
                    )
                    .into_iter()
                    .map(super::facts::Keep::Name),
                );
                for &r in &roots {
                    let (spare, _) = self.housed_in_release(r);
                    if !spare.is_empty() {
                        signal!(rec.on(), trace::TRACE_ROW_GHOST_KEEP);
                        keeps.extend(spare.iter().map(|&g| super::facts::Keep::Ghost(g)));
                    }
                }
                if keeps
                    .iter()
                    .any(|k| !matches!(k, super::facts::Keep::Ghost(_)))
                {
                    signal!(rec.on(), trace::TRACE_ROW_KEEP_FREE);
                }
                self.own.free_sites.insert(stmt as *const Stmt);
                if !keeps.is_empty() {
                    self.own
                        .free_keeps
                        .insert(stmt as *const Stmt, keeps.clone());
                }
                for &r in &roots {
                    self.mark_claimed(r, &keeps);
                }
                signal!(rec.on(), trace::TRACE_SHAPE_DROP);
            }
        }
        self.walk.scopes[depth].insert(
            name.to_string(),
            TableShape {
                ty: Pending,
                layout: LayoutVerdict::default(),
                aliases: BTreeSet::from([NULL_ROOT]),
                lineage: BTreeMap::new(),
            },
        );
        if let Some(scope) = self.walk.prov.get_mut(depth) {
            scope.remove(name);
        }
        Ok(())
    }

    pub(super) fn rebind_death(
        &mut self,
        rec: Gate,
        name: &str,
        _depth: usize,
        stmt: &Stmt,
        old: &TableShape,
        incoming: &BTreeSet<usize>,
    ) -> Result<(), ShapeError> {
        let died: Vec<usize> = old
            .aliases
            .iter()
            .copied()
            .filter(|&s| !is_root(&s) && !incoming.contains(&s))
            .collect();
        if died.is_empty() {
            return Ok(());
        }
        if !rec.on() {
            return Ok(());
        }
        let m_ghost = died.iter().any(is_ghost);
        let m_site = died.iter().any(|s| !is_ghost(s));
        if m_ghost && m_site {
            match self.plan_mixed(name, _depth, old) {
                MixedPlan::NotMixed => {}
                MixedPlan::Suppress => {
                    signal!(rec.on(), trace::TRACE_ROW_GHOST_DEFER);
                    return Ok(());
                }
                MixedPlan::Fire { keeps } => {
                    signal!(rec.on(), trace::TRACE_ROW_GHOST_FIRE);
                    self.own
                        .rebind_grants
                        .entry(stmt as *const Stmt)
                        .or_default()
                        .insert(
                            name.to_string(),
                            keeps.into_iter().map(super::facts::Keep::Name).collect(),
                        );
                    signal!(rec.on(), trace::TRACE_SHAPE_REBIND_DROP);
                    return Ok(());
                }
                MixedPlan::ArmSplit {
                    tag,
                    nothing_on,
                    keeps,
                } => {
                    signal!(rec.on(), trace::TRACE_JOIN_ARM_SPLIT);
                    self.own
                        .arm_rebind_frees
                        .entry(stmt as *const Stmt)
                        .or_default()
                        .push(super::facts::ArmFreeEntry {
                            carrier: name.to_string(),
                            tag,
                            nothing_on,
                            keeps: keeps.into_iter().map(super::facts::Keep::Name).collect(),
                        });
                    signal!(rec.on(), trace::TRACE_SHAPE_REBIND_DROP);
                    return Ok(());
                }
            }
        }
        let has_ghost = m_ghost;
        let housed = old.lineage.keys().any(|o| {
            origin_housed(
                &self.walk.scopes,
                &self.lattice,
                &self.own,
                &self.reads,
                *o,
                _depth,
                name,
            )
        });
        if has_ghost {
            if housed {
                signal!(rec.on(), trace::TRACE_ROW_GHOST_DEFER);
                return Ok(());
            }
            signal!(rec.on(), trace::TRACE_ROW_GHOST_FIRE);
        }
        let mut harm: BTreeSet<usize> = BTreeSet::new();
        let mut keeps: Vec<super::facts::Keep> = Vec::new();
        for &d in &died {
            harm.extend(self.node_release(d));
            harm.extend(self.harm_set(d));
        }
        keeps.extend(
            borrowers_of(
                &self.walk.scopes,
                &harm,
                self.walk.scopes.len(),
                _depth,
                name,
            )
            .into_iter()
            .map(super::facts::Keep::Name),
        );
        for &d in &died {
            let (spare, _) = self.housed_in_release(d);
            if !spare.is_empty() {
                signal!(rec.on(), trace::TRACE_ROW_GHOST_KEEP);
                keeps.extend(spare.iter().map(|&g| super::facts::Keep::Ghost(g)));
            }
        }
        if keeps
            .iter()
            .any(|k| !matches!(k, super::facts::Keep::Ghost(_)))
        {
            signal!(rec.on(), trace::TRACE_ROW_KEEP_FREE);
        }
        signal!(rec.on(), trace::TRACE_SHAPE_REBIND_DROP);
        for &d in &died {
            self.mark_claimed(d, &keeps);
        }
        self.own
            .rebind_grants
            .entry(stmt as *const Stmt)
            .or_default()
            .insert(name.to_string(), keeps);
        Ok(())
    }
}
