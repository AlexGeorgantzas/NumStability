# Prove the frozen audited statement

Your `Candidate.lean` statement has compiled and passed a blind faithfulness
audit against the paper. Now replace its sole target `sorry` with a complete
Lean proof. Continue in this same conversation. The proof stage is timed.

Do not change the target proposition or any definition it depends on. You may
add honest helper lemmas and imports available in your condition. The checker
will reject a changed semantic hash, any `sorry` or `admit`, new axioms,
unsafe/trust escapes, compilation failure, or a vacuous workaround. Use the
library when genuinely helpful, but do not weaken the theorem to fit it.

Before submitting, compile `Candidate.lean` using the command in
`ENVIRONMENT.md`. If you cannot complete the proof, leave your best honest
attempt; the outcome will be recorded as an incomplete proof, not silently
excluded.
