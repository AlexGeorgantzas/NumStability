# Observed-use report without tier grouping

This report re-presents the same 38 accepted fixed-target proof tasks analyzed in
../library-usage-analysis/. It leaves that earlier report unchanged and does
not rerun contestants. Historical task IDs are preserved, but no expected-use
tier is used for grouping or plot colors.

Outputs:

- report.tex: editable nine-page report.
- report.pdf: compiled report.
- make_figures.py: standard-library reproducer for four SVG figures and four
  LaTeX tables; it reads ../library-usage-analysis/task_usage.csv,
  ../library-usage-analysis/pair_usage.csv, and ../../metadata/manifest.json.
- figures/: SVG sources and PNG versions used by LaTeX.
- tables/: derived LaTeX rows.

From the repository root:

    python3 paper_bencmark/highambench/reports/usage-without-tiers/make_figures.py

On macOS, from this report directory:

    sips -s format png figures/*.svg --out figures
    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The side-by-side independent-benchmark comparison cites the separate
NumStability repository's ten_task_benchmark branch, specifically
Documentation/numstability_ten_task_report.pdf (SHA-256
8b2cd10787487cb42d26bc0abe0de7781771802b9a6e8c238840d5cfd9d32c41)
and benchmark/results/summary.json (SHA-256
02a5451409519335445f76f8d3984fbfd6e743f082d9d63de668bedb885c984b).
Those external files are cited, not copied into this branch.
