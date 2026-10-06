# Combined N/L measurement charts

Generated 2026-09-22 15:37 UTC from **117 fully sealed pairs**: 114 with two accepted proofs, 3 with at least one scored failure, and 0 affected by infrastructure. **38/39 tasks** have three accepted N/L repetitions and a plotted mean.

Each diagram has T1, T2, and T3 sections. A task gets adjacent N/L bars only when all three repetitions in both conditions have accepted proofs and all metric values are present. Each section also has a tier-average panel: it gives every completed task equal weight and averages their three-run task means. Bars show N and L performance separately, not L-minus-N differences; incomplete, failed, and infrastructure-affected tasks are excluded from tier averages. Each panel has its own scale. See [task averages](task_averages.csv), [tier averages](tier_averages.csv), and [raw completed pairs](completed_pairs.csv) for absolute values.

- [Elapsed time](time.svg)
- [Observed tokens](tokens.svg)
- [Final source lines](physical_loc.svg)
- [Proof-region LOC](proof_loc.svg)
- [T1/T2 NumStability dependency audit](library_dependency_audit.md)

Observed token totals are incomplete for 226 sealed attempts; any mean containing one is a lower bound, not exact total spending. Time is from prompt release to the authenticated final submission; post-submission hidden validation is excluded. Physical and proof-region LOC are independently recomputed from the authenticated submitted `accepted_proof.lean` bytes and checked against the attempt record: an import command counts as one submitted line, while no internal line from an imported Mathlib or NumStability module or declaration is included. Infrastructure incidents and scored failures are not averaged.

The plotted `P12-T1` and `P17-T1` values measure superseded targets from the frozen r09 campaign: respectively, the full-Theorem-2 FastTwoSum task and the complete Theorem 4.3 variance-plus-bias task. The current corpus replaces them with the papers' equation-(8) exact-subtraction task and equation-(4.12) centered-error task. Neither redesign has been measured; do not apply the historical values to the current tasks.

Campaign composition (later `--results-root` values replace matching complete pair IDs):

- `highambench-b7592c196609712a1d9c`: 87 selected pairs from `<data-drive>/tmp/highambench-new-repo-20260915/results-r09`
- `highambench-9495d00eabc74c6e675f`: 30 selected pairs from `<data-drive>/tmp/highambench-new-repo-20260915/results-r10`

Scored-failure pairs: `P16-T3-rep-01`, `P16-T3-rep-02`, `P16-T3-rep-03`.

`P16-T3` has a documented false target. Its failed attempts remain in the raw pair CSV and are not interpreted as ordinary proof performance or averaged.

The dependency audit shows that all T2 repetitions used their intended substantial declarations, while several T1 repetitions used a substantial alternative or no NumStability declaration. Other task-validity caveats are tracked in [measurement progress](../../MEASUREMENT_PROGRESS.md).
