# Thirty-task HighamBench proof-only report bundle

This folder supplies the tables and figures included by
`../../06-full-report-30-tasks.tex`. It derives a report from archived
results; it does not rerun contestant agents or hidden validators.

Inputs are archived in this repository's `tiered_benchmark_30` branch:

- `paper_bencmark/highambench/reports/library-usage-analysis/task_usage.csv`
- `paper_bencmark/highambench/reports/library-usage-analysis/attempt_usage.csv`
- `paper_bencmark/highambench/reports/scope-sensitivity-30/retained_tasks.csv`

The accepted proof files and attempt records are under `measurements/runs/`
in this same branch, at the SHA-256-verified paths listed in
`attempt_usage.csv`.

`rescan_historical_dp.py` generated `historical_dp_manifest_v2.json` from
the pinned CSVs, accepted proof and attempt hashes, and each historical
campaign's common-definition source hash. On Titan's data drive, it rebuilt
the exact NumStability commit `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`
under Lean `v4.29.0-rc3` and Mathlib commit
`e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`. It then recompiled all
90 accepted L proof sources and applied the exact
`design33_proof_dependencies.lean` proof-term/local-helper scanner used in
the ten-task report. The final 90-entry result is
`historical_direct_proof_scan.json`, with source hashes, target names, exact
library declaration names, counts, and scanner identity. This is a post-run
diagnostic, not a contestant or benchmark rerun. A first diagnostic pass is
preserved separately as `historical_direct_proof_scan_initial.json` with
`historical_dp_manifest.json`; it used a
later P09 convenience definition containing placeholders and does *not*
feed the report. The final pass used the original shared P09 definition
verified against its archived campaign manifest, with one Lean job at a time.

`make_extended_assets.py` verifies the pinned SHA-256 hashes of those three
CSVs and the final proof-term scan, then regenerates the primary direct-use
scatter figure and coefficients,
the tier/direct-use and 30-task tables, secondary-use correlations, paired
N/L figures for each task's elapsed time, observed tokens, and submitted
nonblank/noncomment code lines, an absolute N/L task-mean figure, the
proof-region LOC table,
the direct-proof declaration table, the P01-T1 repetition table, and
`extended_stats.json`. Per-task outcome figures now use the same paired-value
presentation as the ten-task report; usage-vs-gain plots still express their
outcome axis as percentage gain. The old cumulative-gain panels are not
included in this edition. The script verifies all 180 accepted proof-file
hashes, applies the ten-task controller's same Lean-token-line rule, and
records each count in `accepted_code_line_scan.json`. Historical physical
LOC remains in an appendix. The primary
count is the three-run mean of distinct NumStability declarations in the
accepted proof term and its proof-local helpers: the same direct-proof (DP)
definition as in the ten-task report. The earlier distance-one target count
is retained as an appendix diagnostic and is not silently substituted for DP.
P15-T3 has direct helper use despite zero distance-one target reach.

To repeat the Lean scan, use this branch's
`historical-library-snapshot/` as the library source. Its files
were archived from the pinned historical Git commit, including the Lean
toolchain and Mathlib manifest. Build
the NumStability modules imported by the accepted L sources. Stage the
accepted L files under their manifest-relative paths and the
`HighamBench/*Definitions.lean` files from the historical `shared/` corpus,
verifying their hashes against `historical_dp_manifest_v2.json`; P09 in
particular must be the original shared file, not a later convenience copy.
The command below then compiles each accepted proof and emits the full DP
ledger (adjust absolute paths to the local staging locations):

```sh
python3 rescan_historical_dp.py scan \
  --manifest historical_dp_manifest_v2.json \
  --task-root /absolute/path/to/staged-highambench \
  --library-root /absolute/path/to/pinned-numstability \
  --scratch /absolute/path/to/data-drive-scratch \
  --scanner design33_proof_dependencies.lean \
  --lean /absolute/path/to/lean-v4.29.0-rc3 \
  --lake /absolute/path/to/lake-v4.29.0-rc3 \
  --jobs 1 --output historical_direct_proof_scan.json
```

The scanner does not rerun contestant agents or change accepted files. It
rejects any proof or common-definition hash mismatch and retains individual
proof checkpoints for recovery from a diagnostic compiler incident.
The figure generator needs Python 3 and Matplotlib 3.11.2. From this
report directory, it reads the evidence in the repository root by default:

```sh
python3 make_extended_assets.py
```

The other existing tables and three historical usage plots came from
`build_data.py` in this directory;
its own README describes how to regenerate them from the source archive.
Compile this bundle's `report.tex` from this directory so its relative
`tables/` and `figures/` references resolve:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

This is a post-run, outcome-aware thirty-task scope analysis of historical
fixed-target proof runs, **not** a new prospective pilot. All thirty retained
tasks, including losses, are in the report. Token records are incomplete
lower bounds. This benchmark cannot split formalization and proof time
because contestants were given a fixed Lean statement to prove.
