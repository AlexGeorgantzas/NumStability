# Private ten-task report

This folder holds the ten-task report and everything needed to rebuild it:

| File | Contents |
| --- | --- |
| `numstability_ten_task_report.pdf` | Compiled report |
| `report.tex` | LaTeX source |
| `make_figures.py` | General outcome figure and table generator |
| `make_usage_metric_plots.py` | Direct-use and secondary usage measures with paired gains and Spearman plots |
| `make_phase_cumulative_figures.py` | Phase-aligned usage and cumulative time/token figures |
| `../sources/01-current-ten-task-report/Documentation/` | Hash-checked source-reference scans, scripts, and generated tables |
| `generated/` | LaTeX tables written by the generator |
| `requirements.txt` | Pinned Python requirements for the generator |

The report describes the ten paired runs under `benchmark/runs/`. The PDF
and its figures do not change any measured submission. All numeric plots
and tables are regenerated from the ten-task files in `benchmark/results/`
and the ten task packets and paired reports. The generator reads only files
in this repository.

From the repository root:

```sh
python3 benchmark/verify.py
python3 -m pip install -r Documentation/requirements.txt
python3 Documentation/make_figures.py
python3 Documentation/make_usage_metric_plots.py
python3 Documentation/make_phase_cumulative_figures.py
cd Documentation
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -jobname=numstability_ten_task_report report.tex
```

The first generator writes the general LaTeX tables to
`Documentation/generated/` and regenerates its original 20 figure PDFs
under `benchmark/figures/`. Its legacy score diagnostics remain archived
there but are no longer included in the compiled report. The usage-metric
generator adds seven
three-panel usage/gain figures, two uncolored gain/gain diagnostics, a
seven-metric task table, a correlation table, and
`benchmark/results/usage_metric_points.json` with exact counts, gains,
Spearman coefficients, and accepted-artifact hashes. It distinguishes
explicit qualified source names, direct elaborated statement/proof names,
and recursive statement-dossier dependencies. The scripts check task
packet hashes, paired success, metric sums, source-file hashes, and direct
declaration names before reporting success. The smaller
`benchmark/verify.py` independently checks archived task and candidate
files; neither script reruns the model or repeats a paper-faithfulness audit.
LaTeX build byproducts in this folder are ignored by git.

The report bibliography uses paths relative to this private repository's
`ten_task_benchmark` branch; the separately identified 30-task source lives
on its `tiered_benchmark_30` branch. Source-paper PDFs are not redistributed. Their
SHA-256 values and descriptions are in the task packets and source registry.
The original controller and complete campaign journals are not included,
so this repository is an evidence-and-report archive, not a standalone
execution deployment.
