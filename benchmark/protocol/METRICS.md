# Metrics for the ten archived N/L pairs

This describes the fields used in
`benchmark/results/source_task_ledger.json` and
`benchmark/results/summary.json`. All percent gains use `100 * (N - L) / N`; positive means L used less.

| Metric | Archive rule |
| --- | --- |
| Formalization time | Sum of contestant-active statement turns through the first frozen faithful statement, including ordinary library search and repairs; `formalization_seconds_inclusive`. |
| Proof time | Contestant-active proof turns after that statement is frozen, including rejected submissions; `proof_seconds_inclusive`. |
| Total active time | Formalization plus proof; `total_seconds_inclusive`. It is not parallel campaign makespan or audit time. |
| Net-new tokens | Input minus cached input plus output, summed by phase; `formalization_tokens_net_new`, `proof_tokens_net_new`, and `total_tokens_net_new`. Full provider usage remains in the condition reports. |
| One-time orientation | L's scout cost is in `benchmark/evidence/warm-root.json` and `summary.json`; charge it once in aggregate, or divide by ten only for per-task display. It was not repeated per task. |
| Audit/validation overhead | Off-clock audit calls, compilation, semantic dossiers, and proof validation are recorded separately; do not subtract them from contestant-active fields a second time. |
| Code size | Nonblank, noncomment final statement and proof lines. Proof-line pairing requires both conditions to have complete zero-hole proofs. |
| Direct use | The elaborated L statement and kernel-accepted proof-term NumStability names are separate arrays in the ledger and declaration scan. Imports and text mentions do not count. |
| Reuse score | An outcome-annotated 0--3 ordinal breadth score from task-relevant foundation, computation/interface, and analysis witnesses in `benchmark/results/realized_reuse.json`. It is observed uptake, not pre-measured mathematical coverage. |
| Hardware | Per-turn sampled peak CPU cores/RAM plus pre/post snapshots in run records. Brief unsampled spikes may be missed. |

The private report uses the ten paired records in their archived order.
It reports token regressions and other unfavorable metrics alongside
improvements.
