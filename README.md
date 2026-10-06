# NumStability ten-task working archive

This private workspace archives a ten-task N/L formalization-and-proof benchmark. All reported timings, tokens, code sizes, and verdicts come from the preserved task runs under `benchmark/runs/`. Tasks were chosen for expected library coverage. The report in `Documentation/` describes the protocol and the limitations.

The `NumStability/` tree is the frozen library snapshot used for condition L. Condition N had Lean and Mathlib but no NumStability access. The Lean toolchain and dependency manifest are pinned at the repository root. The ten source-task packets are under `benchmark/tasks/`; the observed prompts, submissions, audit outputs, final candidates, proof validations, and hardware records are under `benchmark/runs/`.

`benchmark/results/summary.json` gives aggregate metrics, `source_task_ledger.json` gives the ten task-level records, and `declaration_scan.json` records direct elaborated names. `phase_usage_points.json` separates direct statement (DS), direct proof (DP), and their union (DU); `usage_metric_points.json` preserves secondary usage diagnostics. The figures in `benchmark/figures/` are descriptive visualizations of the ten tasks. Positive gain means `(N - L) / N`.

The task folders preserve original per-run reports and hashes. The run folders omit private Codex checkpoint databases, sandbox identity files, and rebuildable `.olean` files; these are not needed to interpret the recorded submissions and audits. Third-party paper PDFs and authentication state are not redistributed. Supply authorized paper copies matching the hashes in the task packets for any fresh audit or rerun. A fresh model run is stochastic and is not a bit-for-bit replay of these records.

The private ten-task report, its LaTeX source, the figure/table
generators, and build instructions are in `Documentation/`; the compiled PDF
is `Documentation/numstability_ten_task_report.pdf`. `benchmark/protocol/`
describes the archived execution and
metric interpretation. Run `python3 benchmark/verify.py` to check the task
folders and candidate hashes without launching a model.

The report's source-reference diagnostics and their reproducible scripts are
also archived under `sources/01-current-ten-task-report/`. A separate
historical fixed-target, 30-task proof analysis is kept on this repository's
`tiered_benchmark_30` branch; it must not be pooled with these ten runs.
