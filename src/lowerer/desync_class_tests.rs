
/// H11: the desync protocol is a VARIANT — `Diagnostic::desync` mints
/// it, `is_desync` matches the kind, and the rendered tail ("… — the
/// halves disagree") stays the protocol's observable face (H12's 7c
/// deletes both with the class). These tests are the substring era's
/// successor: the old `contains("disagree")` classifier pinned the
/// TEXT; the variant pins the MINT.
#[cfg(test)]
mod desync_class_tests {
    use super::LowerError;
    use crate::diag::Diagnostic;

    /// The real desync message texts, minted as the protocol demands —
    /// each classifies structurally, and each still renders its tail
    /// (the disagreeing halves are message content, not format).
    #[test]
    fn desync_mints_classify_and_render_the_tail() {
        for msg in [
            Diagnostic::desync(
                "Lower Error: a table operand position received a non-table — \
             the checker and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: a housed row's keep register was never \
             captured — the analyzer and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: IR emitter label desync: a br/phi names block 'b3', \
             which the module never emits — the emitters and the block \
             model disagree (see SeamPlan in backend.rs)",
            ),
            Diagnostic::desync(
                "Lower Error: a dotted call site carries no resolved verb — \
             the checker and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: an index key carries no recorded lane — \
             the checker and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: a table access carries no recorded elem face — \
             the checker and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: a string operand position received a different repr — \
             the checker and the lowerer disagree",
            ),
        ] {
            assert!(LowerError(msg.clone()).is_desync(), "{msg}");
            assert!(msg.render().contains("disagree"), "{msg}");
        }
    }

    /// The substring era's false-positive class is unrepresentable: a
    /// message whose TEXT merely contains "disagree" is not a desync
    /// unless minted as one — script errors never are.
    #[test]
    fn desync_is_the_mint_not_the_bytes() {
        for msg in [
            Diagnostic::lower("Undeclared variable"),
            Diagnostic::lower("the operands disagree with the repr table"),
        ] {
            assert!(!LowerError(msg.clone()).is_desync(), "{msg}");
        }
        assert!(!LowerError(Diagnostic::lower("plain")).is_desync());
        assert!(LowerError(Diagnostic::desync("any bespoke bug text")).is_desync());
    }
}
