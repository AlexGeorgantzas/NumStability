#!/usr/bin/env python3
"""Rebuild a disclosed 30-task post-run scope sensitivity PDF.

The archived 38-task report and all its evidence remain untouched. This script
filters whole papers named in scope_manifest.json, then regenerates every plot.
"""

from __future__ import annotations

import csv
import hashlib
import json
import statistics
import subprocess
import sys
from collections import Counter
from pathlib import Path

from reportlab.lib import colors
from reportlab.lib.pagesizes import A4, landscape
from reportlab.lib.utils import ImageReader
from reportlab.pdfgen import canvas


HERE = Path(__file__).resolve().parent
BASE_DIR = HERE.parent / "metric-comparison"
sys.path.insert(0, str(BASE_DIR))
import make_tier_report as base  # noqa: E402


FIGURES = HERE / "figures"
PDF = HERE / "scope_sensitivity_30.pdf"
MANIFEST = HERE / "scope_manifest.json"


def read_scope() -> tuple[list[dict[str, object]], list[dict[str, object]], dict]:
    scope = json.loads(MANIFEST.read_text())
    base_pdf = BASE_DIR / "tier_metric_comparison.pdf"
    if hashlib.sha256(base_pdf.read_bytes()).hexdigest() != scope["base_pdf_sha256"]:
        raise ValueError("The preserved 38-task PDF differs from the pinned original")
    original, _, _ = base.load_data()
    excluded_papers = set(scope["excluded_paper_ids"])
    retained = [row for row in original if str(row["task_id"]).split("-")[0] not in excluded_papers]
    excluded = [row for row in original if str(row["task_id"]).split("-")[0] in excluded_papers]
    assert len(original) == 38 and len(retained) == 30 and len(excluded) == 8
    assert {str(row["task_id"]) for row in excluded} == set(scope["expected_excluded_task_ids"])
    assert {str(row["task_id"]).split("-")[0] for row in excluded} == excluded_papers
    assert Counter(str(row["tier"]) for row in retained) == {"T1": 9, "T2": 3, "T3": 18}
    assert scope["retained_exception"] in {row["task_id"] for row in retained}
    return original, retained, scope


def make_data(original: list[dict[str, object]], retained: list[dict[str, object]]) -> list[dict[str, str]]:
    fields = ["metric", "outcome", "full_rho", "retained_rho", "delta_rho"]
    rows: list[dict[str, str]] = []
    for metric in base.METRICS:
        for outcome_key, _, _ in base.OUTCOMES:
            rho_full = base.spearman([base.f(row, metric.key) for row in original],
                                     [base.f(row, outcome_key) for row in original])
            rho_retained = base.spearman([base.f(row, metric.key) for row in retained],
                                         [base.f(row, outcome_key) for row in retained])
            rows.append({"metric": metric.key, "outcome": outcome_key,
                         "full_rho": f"{rho_full:.6f}",
                         "retained_rho": f"{rho_retained:.6f}",
                         "delta_rho": f"{rho_retained-rho_full:+.6f}"})
    with (HERE / "association_change.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    with (HERE / "retained_tasks.csv").open("w", newline="") as stream:
        fields = ["task_id", "tier"] + [metric.key for metric in base.METRICS] + [key for key, _, _ in base.OUTCOMES]
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(retained)
    return rows


def generate_figures(retained: list[dict[str, object]]) -> None:
    FIGURES.mkdir(exist_ok=True)
    for metric in base.METRICS:
        svg = base.tier_svg(retained, metric)
        # The original plotting function is intentionally left unchanged so
        # rerunning its 38-task report remains byte-for-byte reproducible.
        assert "n=38" in svg and "tier-exception watchlist" in svg
        svg = svg.replace("n=38", "n=30").replace("tier-exception watchlist", "retained exception: P15-T3")
        path = FIGURES / f"{metric.key}.svg"
        path.write_text(svg)
        subprocess.run(["sips", "-s", "format", "png", str(path), "--out", str(path.with_suffix(".png"))],
                       check=True, stdout=subprocess.DEVNULL)


def draw_cover(pdf: canvas.Canvas, original: list[dict[str, object]],
               retained: list[dict[str, object]], scope: dict) -> None:
    page_w, page_h = landscape(A4)
    base.header(pdf, 1, "Scope sensitivity: 30 retained tasks")
    base.draw_lines(pdf, "A separate copy of the tier-colored metric report after removing every task from six papers. The underlying runs are unchanged. This exclusion was chosen after observing tier fit, so this is an exploratory sensitivity analysis, not an independent or prospectively selected benchmark.",
                    43, page_h-83, page_w-86, 10.7, 16)
    y = page_h-153
    for i, tier in enumerate(("T1", "T2", "T3")):
        x = 50 + 260*i
        pdf.setFillColor(colors.HexColor(base.TIER_COLORS[tier]))
        pdf.circle(x, y+3, 6, fill=1, stroke=0)
        base.draw_lines(pdf, base.TIER_LABELS[tier], x+16, y, 238, 10, 14)
    pdf.setFillColor(colors.HexColor("#f2f6f9"))
    pdf.roundRect(42, 232, page_w-84, 174, 8, fill=1, stroke=0)
    pdf.setFillColor(colors.HexColor("#172b42"))
    pdf.setFont("Helvetica-Bold", 11)
    pdf.drawString(55, 384, "Task-level medians in the retained cohort")
    widths = [105, 78, 102, 100, 95, 95]
    base.row_line(pdf, 54, 360, widths,
                  ["Tier", "Tasks", "Distinct names", "Occurrences", "Audited deps", "Time gain"], 9, True)
    for j, tier in enumerate(("T1", "T2", "T3")):
        subset = [row for row in retained if row["tier"] == tier]
        values = [tier, str(len(subset)),
                  f'{statistics.median(base.f(row,"qualified_distinct") for row in subset):.1f}',
                  f'{statistics.median(base.f(row,"qualified_occurrences") for row in subset):.1f}',
                  f'{statistics.median(base.f(row,"transitive") for row in subset):.1f}',
                  f'{statistics.median(base.f(row,"time_gain_pct") for row in subset):+.1f}%']
        base.row_line(pdf, 54, 331-j*34, widths, values, 9, height=30)
    pdf.setFillColor(colors.HexColor("#fff1e5"))
    pdf.roundRect(42, 118, page_w-84, 93, 7, fill=1, stroke=0)
    base.draw_lines(pdf, "Interpretation limit: the excluded papers were selected after results were inspected; the apparent association can improve or deteriorate simply because of selection. T1/T2 and T3 also came from different runner campaigns. P15-T3, the strongest low-expected-use exception, remains in this cohort.",
                    56, 188, page_w-112, 10, 15, "Helvetica-Bold")
    base.draw_lines(pdf, "Retained: 30 of 38 tasks, 90 of 114 paired runs. Excluded papers: " + ", ".join(scope["excluded_paper_ids"]) + ". The original 38-task report and all raw evidence remain preserved. Positive gain means L used less than N.",
                    43, 91, page_w-86, 9, 13)
    pdf.showPage()


def draw_comparison(pdf: canvas.Canvas, original: list[dict[str, object]],
                    retained: list[dict[str, object]], scope: dict,
                    changes: list[dict[str, str]]) -> None:
    page_w, page_h = landscape(A4)
    base.header(pdf, 2, "What changed when six papers were removed")
    base.draw_lines(pdf, "The eight removed tasks are listed below by paper. All three P15 tasks, including P15-T3, remain. No formalization or proof was rerun for this comparison.",
                    43, page_h-80, page_w-86, 10, 15)
    excluded_by_paper = {paper: [task for task in scope["expected_excluded_task_ids"] if task.startswith(paper+"-")]
                         for paper in scope["excluded_paper_ids"]}
    y = page_h-128
    for index, (paper, ids) in enumerate(excluded_by_paper.items()):
        x = 48 + (index % 3)*260
        yy = y - (index // 3)*30
        pdf.setFillColor(colors.HexColor("#dbe7ef"))
        pdf.roundRect(x, yy-11, 240, 25, 4, fill=1, stroke=0)
        base.draw_lines(pdf, f"{paper}: " + ", ".join(ids), x+7, yy-3, 225, 9.5, 13)
    median_parts = []
    for key, label in (("time_gain_pct", "time"), ("loc_gain_pct", "lines"),
                       ("token_gain_pct", "tokens")):
        full_median = statistics.median(base.f(row, key) for row in original)
        retained_median = statistics.median(base.f(row, key) for row in retained)
        median_parts.append(f"{label} {full_median:+.1f}% to {retained_median:+.1f}%")
    base.draw_lines(pdf, "Overall median gain, full to retained: " + "; ".join(median_parts) + ".",
                    45, 397, page_w-90, 9.2, 13, "Helvetica-Bold")
    pdf.setFont("Helvetica-Bold", 11)
    pdf.setFillColor(colors.HexColor("#172b42"))
    pdf.drawString(45, 367, "Pooled Spearman rho: full 38 versus retained 30")
    widths = [206, 113, 110, 108, 111]
    base.row_line(pdf, 45, 343, widths, ["Usage measure", "Gain", "Full", "Retained", "Change"], 9, True)
    labels = {"qualified_distinct": "Distinct qualified names",
              "qualified_occurrences": "Qualified-name occurrences",
              "transitive": "Audited transitive deps"}
    outcome_labels = {"time_gain_pct": "Time", "loc_gain_pct": "Lines", "token_gain_pct": "Tokens"}
    selected = [row for row in changes if row["metric"] in labels]
    for j, row in enumerate(selected):
        base.row_line(pdf, 45, 317-j*24, widths,
                      [labels[row["metric"]], outcome_labels[row["outcome"]],
                       f'{float(row["full_rho"]):+.2f}', f'{float(row["retained_rho"]):+.2f}',
                       f'{float(row["delta_rho"]):+.2f}'], 8.8, height=23)
    base.draw_lines(pdf, "These coefficients are descriptive. A larger rho after filtering does not validate the post-run exclusion or establish that the excluded mathematics was out of scope. The full 12-measure comparison is in association_change.csv.",
                    45, 78, page_w-90, 8.8, 13)
    pdf.showPage()


def draw_metric_pages(pdf: canvas.Canvas, retained: list[dict[str, object]]) -> None:
    page_w, page_h = landscape(A4)
    for index, metric in enumerate(base.METRICS, start=1):
        base.header(pdf, index+2, f"Metric {index}/12: {metric.title}")
        img = ImageReader(str(FIGURES / f"{metric.key}.png"))
        width = page_w-70
        pdf.drawImage(img, 35, 168, width=width, height=width*520/1320,
                      preserveAspectRatio=True, mask="auto")
        base.draw_lines(pdf, "Definition: " + metric.definition + ".",
                        43, 145, page_w-86, 9.5, 14, "Helvetica-Bold")
        if metric.key in ("candidates", "direct_candidates", "substantial_hits", "substantial_explicit"):
            caveat = "Task-specific candidate classifications enter this measure. T3 has no predesignated substantial result, so substantial-hit zeros there are partly by construction."
        else:
            caveat = "This plot uses a post-run filtered cohort. Tier and runner campaign remain confounded; the pooled correlation is descriptive, not causal."
        base.draw_lines(pdf, caveat, 43, 101, page_w-86, 8.8, 13)
        pdf.showPage()


def draw_sources(pdf: canvas.Canvas, scope: dict) -> None:
    page_w, page_h = landscape(A4)
    base.header(pdf, len(base.METRICS)+3, "Source and scope notes")
    paragraphs = [
        "Original evidence: paper_bencmark/highambench/reports/library-usage-analysis/attempt_usage.csv, task_usage.csv, pair_usage.csv, analyze.py and semantic_catalog.json; paper_bencmark/highambench/metadata/manifest.json. The original tier-colored PDF remains at reports/metric-comparison/tier_metric_comparison.pdf, pinned by SHA-256 in scope_manifest.json.",
        "Scope rule: remove every task whose paper ID is one of " + ", ".join(scope["excluded_paper_ids"]) + ". The script asserts the exact eight excluded task IDs and retains P15-T3. There is no task-level outcome filter beyond that paper rule. Every retained task contributes all three original paired runs.",
        "This filtering decision was made after the tier-fit analysis. It changes the analyzed cohort and cannot be presented as the original benchmark corpus or as held-out confirmation. Unexpected tier fit is a diagnostic signal, not by itself proof that a paper is mathematically outside NumStability's aims.",
        "Aggregation and metrics match the preserved report: L-side usage is averaged across three accepted runs per task; gains compare N and L three-run means. Qualified names are lexical; audited dependencies come from the accepted theorem's recorded Lean dependency closure. Transitive counts can include indirect and compiler-generated declarations. Token counts are provider-observed.",
        "Rebuild: run python3 make_report.py from this directory. It regenerates 12 tier-colored SVG/PNG figures, retained_tasks.csv, association_change.csv and this PDF. The script hash-checks the preserved 38-task PDF and imports the source-CSV hash-checked analysis functions.",
    ]
    y = page_h-83
    for paragraph in paragraphs:
        y = base.draw_lines(pdf, paragraph, 43, y, page_w-86, 9.5, 15)
        y -= 18
    pdf.showPage()


def make_pdf(original: list[dict[str, object]], retained: list[dict[str, object]],
             scope: dict, changes: list[dict[str, str]]) -> None:
    pdf = canvas.Canvas(str(PDF), pagesize=landscape(A4), pageCompression=1)
    pdf.setTitle("NumStability post-run 30-task scope sensitivity")
    pdf.setAuthor("HighamBench analysis")
    draw_cover(pdf, original, retained, scope)
    draw_comparison(pdf, original, retained, scope, changes)
    draw_metric_pages(pdf, retained)
    draw_sources(pdf, scope)
    pdf.save()


def main() -> None:
    original, retained, scope = read_scope()
    changes = make_data(original, retained)
    generate_figures(retained)
    make_pdf(original, retained, scope, changes)
    print(f"Generated {PDF.name}: {len(retained)} tasks, {len(scope['excluded_paper_ids'])} excluded papers, {len(base.METRICS)} plots")


if __name__ == "__main__":
    main()
