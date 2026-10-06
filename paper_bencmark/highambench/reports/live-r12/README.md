# Live N/L measurement charts

Generated 2026-09-22 14:13 UTC from **25 fully sealed pairs**: 25 with two accepted proofs, 0 with at least one scored failure, and 0 affected by infrastructure. **8/38 tasks** have three accepted N/L repetitions and a plotted mean.

Each diagram has T1, T2, and T3 sections. A task gets adjacent N/L bars only when all three repetitions in both conditions have accepted proofs and all metric values are present. Bars show separate arithmetic means of those three runs, not L-minus-N differences; incomplete, failed, and infrastructure-affected tasks show why no mean is plotted. Each task panel has its own scale. See [task averages](task_averages.csv) and [raw completed pairs](completed_pairs.csv) for absolute values.

- [Elapsed time](time.svg)
- [Observed tokens](tokens.svg)
- [Final source lines](physical_loc.svg)
- [Proof-region LOC](proof_loc.svg)

Observed token totals are incomplete for 0 sealed attempts; any mean containing one is a lower bound, not exact total spending. Time is from prompt release to the authenticated final submission; post-submission hidden validation is excluded. Physical and proof-region LOC are independently recomputed from the authenticated submitted `accepted_proof.lean` bytes and checked against the attempt record: an import command counts as one submitted line, while no internal line from an imported Mathlib or NumStability module or declaration is included. Infrastructure incidents and scored failures are not averaged.

Task-validity and library-use caveats are tracked separately in [measurement progress](../../MEASUREMENT_PROGRESS.md).
