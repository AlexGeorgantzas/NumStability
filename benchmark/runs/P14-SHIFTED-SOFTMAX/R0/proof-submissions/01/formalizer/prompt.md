# Prove the frozen audited statement — complete proofs only

The target statement and its supporting definitions have compiled and passed
the paper-faithfulness audit. That audit did **not** prove the theorem. The
single `sorry` currently in `Candidate.lean` is a proof hole, not a proof.

Continue in this same timed conversation. Replace the target `sorry` with a
complete Lean proof of the **unchanged** audited statement. You may add honest
helper lemmas and imports available to your condition. Do not weaken the
statement, alter a defining dependency, add an axiom, use `sorry` or `admit`
anywhere, or use unsafe/trust escapes. The checker requires a zero-hole Lean
file that compiles and preserves the audited semantic hash. A Lean file that
merely compiles with a `sorry` is **not** a successful proof.

There are at most four total proof submissions (initial plus three repairs)
within the cumulative contestant budget. Each submission is frozen before
off-clock validation. If one is rejected, including for a remaining `sorry`,
the same conversation receives diagnostics and may use its remaining attempts.

Before declaring success, run the documented Lean compilation command on
`Candidate.lean`, inspect the diagnostics, and verify that the entire file
contains no proof hole. Do not call a partial derivation a completed proof.

If you determine that you cannot finish within the remaining budget, or find
a counterexample to the frozen statement, say `NO_COMPLETE_PROOF` in your final
message and explain the obstruction. Do not fabricate a proof or claim that
the file is proved. The controller must record this as proof failure or
abstention, preserving the file and all time/token usage as evidence; it must
not count a file containing `sorry` as a valid proof submission.
