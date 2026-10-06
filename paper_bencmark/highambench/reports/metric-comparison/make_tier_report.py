#!/usr/bin/env python3
"""Build tier-colored usage plots and a PDF diagnostic from archived evidence."""

from __future__ import annotations

import csv
import hashlib
import html
import json
import math
import statistics
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

from reportlab.lib import colors
from reportlab.lib.pagesizes import A4, landscape
from reportlab.lib.utils import ImageReader
from reportlab.pdfbase.pdfmetrics import stringWidth
from reportlab.pdfgen import canvas

from make_plots import METRICS, OUTCOMES, SOURCE, esc, f, jitter, read_rows, rounded_axis, spearman


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MANIFEST = ROOT / "paper_bencmark/highambench/metadata/manifest.json"
MANIFEST_SHA256 = "5d76d68d9b6d15f81b23bcd1c7fe8ac046e5aec21dbcdeeccc7b33d248b2a5e4"
FIGURES = HERE / "tier_figures"
PDF = HERE / "tier_metric_comparison.pdf"
EXCEPTIONS_CSV = HERE / "tier_exceptions.csv"
TIER_COLORS = {"T1": "#087e87", "T2": "#7c4fa3", "T3": "#ce792e"}
TIER_LABELS = {"T1": "T1 (expected moderate use)",
               "T2": "T2 (expected strongest use)",
               "T3": "T3 (expected little/no use)"}
FLAG_EXPLANATIONS = {
    "P15-T3": ("Clear", "All three runs use many qualified names and audited dependencies."),
    "P17-T1": ("Clear", "Two runs have no audited use; no run uses a prelisted substantial result."),
    "P02-T3": ("Episodic", "One of three runs uses 10 qualified names and 22 audited dependencies."),
    "P40-T3": ("Episodic", "Two runs use library names; one has five direct audited dependencies."),
    "P33-T1": ("Partial", "Audited use in all runs, but prelisted substantial use in only one."),
    "P20-T3": ("Trace", "One run has four qualified names and four audited dependencies."),
    "P35-T3": ("Trace", "Two runs show only a single qualified name and small dependency closures."),
}


def load_data() -> tuple[list[dict[str, object]], list[dict[str, str]], list[dict[str, str]]]:
    tasks = read_rows("task_usage.csv")
    attempts = read_rows("attempt_usage.csv")
    pairs = read_rows("pair_usage.csv")
    assert len(tasks) == 38 and len(attempts) == 228 and len(pairs) == 114
    assert Counter(t["tier"] for t in tasks) == {"T1": 12, "T2": 3, "T3": 23}
    occurrences: dict[str, list[float]] = defaultdict(list)
    for attempt in attempts:
        if attempt["condition"] == "L":
            occurrences[attempt["task_id"]].append(f(attempt, "qualified_occurrences"))
    merged: list[dict[str, object]] = []
    for task in tasks:
        task_id = task["task_id"]
        assert len(occurrences[task_id]) == 3
        row: dict[str, object] = {"task_id": task_id, "tier": task["tier"]}
        for metric in METRICS:
            row[metric.key] = (statistics.mean(occurrences[task_id]) if metric.key == "qualified_occurrences"
                               else f(task, metric.input_column or ""))
        for key, _, _ in OUTCOMES:
            row[key] = f(task, key)
        merged.append(row)
    return merged, tasks, attempts


def tier_svg(tasks: list[dict[str, object]], metric) -> str:
    width, height = 1320, 520
    panel_width, gap = 400, 24
    start_x, plot_top, plot_height = 25, 110, 315
    plot_left_offset, plot_width = 65, 300
    x_max, ticks = rounded_axis(max(f(task, metric.key) for task in tasks))
    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        f'<rect width="{width}" height="{height}" fill="#fff"/>',
        f'<text x="{width/2}" y="31" text-anchor="middle" font-family="Arial,sans-serif" font-weight="bold" font-size="21" fill="#172b42">{esc(metric.title)}</text>',
        '<text x="660" y="55" text-anchor="middle" font-family="Arial,sans-serif" font-size="12" fill="#536579">Task means across three paired runs - n=38 - positive gain favors L</text>',
    ]
    legend_x = 55
    for tier in ("T1", "T2", "T3"):
        color = TIER_COLORS[tier]
        lines.append(f'<circle cx="{legend_x}" cy="80" r="5.4" fill="{color}"/>')
        lines.append(f'<text x="{legend_x+12}" y="84" font-family="Arial,sans-serif" font-size="12" fill="#384b60">{tier}</text>')
        legend_x += 74
    lines.append('<circle cx="287" cy="80" r="6" fill="white" stroke="#142330" stroke-width="1.8"/>')
    lines.append('<text x="300" y="84" font-family="Arial,sans-serif" font-size="12" fill="#384b60">tier-exception watchlist</text>')
    y_limits = {"time_gain_pct": (-90, 100), "loc_gain_pct": (-130, 100), "token_gain_pct": (-420, 100)}
    for index, (outcome_key, outcome_title, accent) in enumerate(OUTCOMES):
        panel_x = start_x + index * (panel_width + gap)
        left = panel_x + plot_left_offset
        right = left + plot_width
        lo, hi = y_limits[outcome_key]
        lines.append(f'<text x="{panel_x+panel_width/2:.1f}" y="105" text-anchor="middle" font-family="Arial,sans-serif" font-weight="bold" font-size="14" fill="{accent}">{esc(outcome_title)}</text>')
        for tick in ticks:
            xx = left + tick / x_max * plot_width
            lines.append(f'<line x1="{xx:.1f}" y1="{plot_top}" x2="{xx:.1f}" y2="{plot_top+plot_height}" stroke="#e8edf0"/>')
            lines.append(f'<text x="{xx:.1f}" y="{plot_top+plot_height+20}" text-anchor="middle" font-family="Arial,sans-serif" font-size="10" fill="#526174">{tick:g}</text>')
        for tick in (-400, -300, -200, -100, -50, 0, 50, 100):
            if lo <= tick <= hi:
                yy = plot_top + (hi-tick)/(hi-lo)*plot_height
                stroke = "#8a98a8" if tick == 0 else "#e8edf0"
                lines.append(f'<line x1="{left}" y1="{yy:.1f}" x2="{right}" y2="{yy:.1f}" stroke="{stroke}"/>')
                lines.append(f'<text x="{left-8}" y="{yy+4:.1f}" text-anchor="end" font-family="Arial,sans-serif" font-size="10" fill="#526174">{tick:+d}%</text>')
        for task in tasks:
            xx = left + f(task, metric.key)/x_max*plot_width + jitter(str(task["task_id"]), metric.key)
            yy = plot_top + (hi-f(task, outcome_key))/(hi-lo)*plot_height
            yy = min(plot_top+plot_height, max(plot_top, yy))
            tier = str(task["tier"])
            flagged = task["task_id"] in FLAG_EXPLANATIONS
            lines.append(f'<circle cx="{xx:.1f}" cy="{yy:.1f}" r="{5.4 if flagged else 4.8}" fill="{TIER_COLORS[tier]}" fill-opacity="0.83" stroke="{("#142330" if flagged else "#fff")}" stroke-width="{(1.8 if flagged else 0.8)}"><title>{esc(task["task_id"])} ({tier}): {metric.title}={f(task, metric.key):.2f}; {outcome_title}={f(task, outcome_key):+.2f}%</title></circle>')
        rho = spearman([f(task, metric.key) for task in tasks],
                       [f(task, outcome_key) for task in tasks])
        lines.append(f'<text x="{panel_x+panel_width/2:.1f}" y="{height-59}" text-anchor="middle" font-family="Arial,sans-serif" font-size="12" fill="#394b61">Pooled Spearman rho = {rho:+.2f}</text>')
        lines.append(f'<text x="{panel_x+panel_width/2:.1f}" y="{height-35}" text-anchor="middle" font-family="Arial,sans-serif" font-size="11" fill="#526174">Mean L count per task (0-{x_max:g})</text>')
    lines.append('<text x="660" y="512" text-anchor="middle" font-family="Arial,sans-serif" font-size="10" fill="#667588">Dots with identical counts are jittered slightly for visibility. T1/T2 and T3 came from different runner campaigns.</text>')
    lines.append('</svg>')
    return "\n".join(lines) + "\n"


def wrap(text: str, font: str, size: float, max_width: float) -> list[str]:
    result: list[str] = []
    line = ""
    for word in text.split():
        proposed = word if not line else line + " " + word
        if stringWidth(proposed, font, size) > max_width and line:
            result.append(line)
            line = word
        else:
            line = proposed
    if line:
        result.append(line)
    return result


def draw_lines(pdf: canvas.Canvas, text: str, x: float, y: float, width: float,
               size: float = 10, leading: float = 15, font: str = "Helvetica",
               color=colors.HexColor("#243449")) -> float:
    pdf.setFillColor(color)
    pdf.setFont(font, size)
    for line in wrap(text, font, size, width):
        pdf.drawString(x, y, line)
        y -= leading
    return y


def header(pdf: canvas.Canvas, page: int, title: str) -> None:
    width, height = landscape(A4)
    pdf.setFillColor(colors.HexColor("#172b42"))
    pdf.setFont("Helvetica-Bold", 19)
    pdf.drawString(38, height-43, title)
    pdf.setStrokeColor(colors.HexColor("#d4dfe7"))
    pdf.line(38, height-51, width-38, height-51)
    pdf.setFont("Helvetica", 8)
    pdf.setFillColor(colors.HexColor("#63768b"))
    pdf.drawString(38, 25, "HighamBench | alternative observed-use measures | archival analysis")
    pdf.drawRightString(width-38, 25, str(page))


def row_line(pdf: canvas.Canvas, x: float, y: float, widths: list[float], values: list[str],
             size: float = 8.7, bold: bool = False, height: float = 25) -> None:
    pdf.setFillColor(colors.HexColor("#172b42" if bold else "#314258"))
    pdf.setFont("Helvetica-Bold" if bold else "Helvetica", size)
    xpos = x
    for width, value in zip(widths, values):
        lines = wrap(value, "Helvetica-Bold" if bold else "Helvetica", size, width-8)
        for offset, line in enumerate(lines[:3]):
            pdf.drawString(xpos+4, y-offset*10.5, line)
        xpos += width
    pdf.setStrokeColor(colors.HexColor("#e3eaf0"))
    pdf.line(x, y-height+6, xpos, y-height+6)


def exception_rows(tasks: list[dict[str, str]], merged: list[dict[str, object]]) -> list[dict[str, str]]:
    task_by_id = {t["task_id"]: t for t in tasks}
    merged_by_id = {str(t["task_id"]): t for t in merged}
    if hashlib.sha256(MANIFEST.read_bytes()).hexdigest() != MANIFEST_SHA256:
        raise ValueError("Manifest input hash mismatch")
    manifest = json.loads(MANIFEST.read_text())
    known = {t["task_id"] for t in tasks}
    by_paper = {p["paper_id"]: p["targets"] for p in manifest["papers"]}
    rows = []
    for task_id, (severity, reason) in FLAG_EXPLANATIONS.items():
        task = task_by_id[task_id]
        metric = merged_by_id[task_id]
        assert task["tier"] in ("T1", "T3")
        assert (int(task["substantial_use_runs"]) <= 1 if task["tier"] == "T1"
                else int(task["any_use_runs"]) > 0)
        paper = task_id.split("-")[0]
        peers = [f'{target["task_id"]} ({target["tier"]}; {"measured" if target["task_id"] in known else "manifest only"})'
                 for target in by_paper[paper] if target["tier"] != task["tier"]]
        rows.append({"task_id": task_id, "tier": task["tier"], "severity": severity,
                     "any_use_runs": task["any_use_runs"],
                     "substantial_use_runs": task["substantial_use_runs"],
                     "mean_qualified_distinct": f'{f(metric, "qualified_distinct"):.2f}',
                     "mean_transitive": f'{f(metric, "transitive"):.2f}',
                     "reason": reason, "other_tier_same_paper": "; ".join(peers) if peers else "None"})
    return rows


def make_pdf(merged: list[dict[str, object]], exceptions: list[dict[str, str]]) -> None:
    page_w, page_h = landscape(A4)
    pdf = canvas.Canvas(str(PDF), pagesize=(page_w, page_h), pageCompression=1)
    pdf.setTitle("NumStability observed-use measures, tier-colored")
    pdf.setAuthor("HighamBench analysis")

    # Summary page.
    header(pdf, 1, "Observed NumStability use by expected tier")
    draw_lines(pdf, "Twelve alternative measures of realized library use, with identical time, source-line, and observed-token gain outcomes. Every point is a task mean over three N/L pairs (38 tasks; 114 pairs). The archive's 0-3 score is not an axis in this report.",
               42, page_h-80, page_w-84, 11, 17)
    y = page_h-148
    for index, tier in enumerate(("T1", "T2", "T3")):
        x = 50 + index*260
        pdf.setFillColor(colors.HexColor(TIER_COLORS[tier]))
        pdf.circle(x, y+3, 6, fill=1, stroke=0)
        draw_lines(pdf, TIER_LABELS[tier], x+16, y, 238, 10, 14)
    pdf.setFillColor(colors.HexColor("#f2f6f9"))
    pdf.roundRect(42, 226, page_w-84, 200, 8, fill=1, stroke=0)
    pdf.setFillColor(colors.HexColor("#172b42"))
    pdf.setFont("Helvetica-Bold", 11)
    pdf.drawString(55, 407, "Task-level medians")
    widths = [105, 78, 102, 100, 95, 95]
    row_line(pdf, 54, 382, widths, ["Tier", "Tasks", "Distinct names", "Occurrences", "Audited deps", "Time gain"], 9, True)
    for j, tier in enumerate(("T1", "T2", "T3")):
        subset = [t for t in merged if t["tier"] == tier]
        values = [tier, str(len(subset)),
                  f'{statistics.median(f(t,"qualified_distinct") for t in subset):.1f}',
                  f'{statistics.median(f(t,"qualified_occurrences") for t in subset):.1f}',
                  f'{statistics.median(f(t,"transitive") for t in subset):.1f}',
                  f'{statistics.median(f(t,"time_gain_pct") for t in subset):+.1f}%']
        row_line(pdf, 54, 352-j*35, widths, values, 9, height=30)
    pdf.setFillColor(colors.HexColor("#fff1e5"))
    pdf.roundRect(42, 124, page_w-84, 84, 7, fill=1, stroke=0)
    draw_lines(pdf, "Critical limitation: tier and runner campaign are perfectly confounded in this cohort. T1/T2 came from r11; T3 came from r09/r10. The plotted pooled correlations are descriptive and cannot isolate tier, library use, task difficulty, or runner effects.",
               56, 185, page_w-112, 10, 15, "Helvetica-Bold")
    draw_lines(pdf, "Positive gain = (mean N - mean L) / mean N. Qualified names count source text; audited dependencies count the accepted theorem's recorded Lean dependency closure. Token totals are provider-observed. Sources: archived attempt_usage.csv, task_usage.csv, pair_usage.csv and metadata/manifest.json. No task is excluded from this 38-task analysis cohort.",
               42, 96, page_w-84, 8.7, 13)
    pdf.showPage()

    # Deviations page.
    header(pdf, 2, "Tasks that challenge their expected tier")
    draw_lines(pdf, "Diagnostic rule: flag T1 when at most one of three L runs uses a prelisted substantial result; flag T2 if fewer than three do; flag T3 when any L run has audited library use. This intentionally sensitive rule has seven flags, separated by materiality below. It is a post-run diagnostic, not a change to the task corpus.",
               42, page_h-77, page_w-84, 9.3, 14)
    widths = [76, 66, 87, 135, 333]
    row_line(pdf, 43, page_h-146, widths,
             ["Task", "Signal", "Use runs", "Same-paper other tier", "What does not fit"], 8.6, True, 29)
    y = page_h-182
    order = ["P15-T3", "P17-T1", "P02-T3", "P40-T3", "P33-T1", "P20-T3", "P35-T3"]
    for task_id in order:
        e = next(row for row in exceptions if row["task_id"] == task_id)
        peer = e["other_tier_same_paper"].replace(" (T1; measured)", "").replace(" (T2; measured)", "").replace(" (T3; measured)", "")
        use = e["any_use_runs"] + "/3 audited"
        if e["tier"] == "T1":
            use += "; " + e["substantial_use_runs"] + "/3 substantive"
        note = e["reason"]
        row_line(pdf, 43, y, widths, [task_id, e["severity"], use, peer, note], 8.15, height=43)
        y -= 44
    draw_lines(pdf, "The strongest departures are P15-T3 and P17-T1. P20-T3 and P35-T3 are trace-level departures, not evidence of broad reusable coverage. P28-T1 and P29-T1 have zero task-listed candidate hits but substantial audited use in all three runs; this is a candidate-list limitation, not a tier failure.",
               43, 77, page_w-86, 8.5, 12)
    pdf.showPage()

    # One metric per page, preserving readable 3-panel figures.
    for index, metric in enumerate(METRICS, start=1):
        header(pdf, index+2, f"Metric {index}/12: {metric.title}")
        image = ImageReader(str(FIGURES / f"{metric.key}.png"))
        img_w = page_w-70
        img_h = img_w*520/1320
        pdf.drawImage(image, 35, 168, width=img_w, height=img_h, preserveAspectRatio=True, mask="auto")
        draw_lines(pdf, "Definition: " + metric.definition + ".", 43, 145, page_w-86, 9.5, 14, "Helvetica-Bold")
        if metric.key in ("candidates", "direct_candidates", "substantial_hits", "substantial_explicit"):
            caveat = "This measure uses task-specific candidate or substantial-result classifications. T3 has no predesignated substantial result, so substantial-hit zeros there are partly by construction."
        elif metric.key == "public_transitive":
            caveat = "The limited filter omits some generated-name patterns but does not certify that every remaining dependency belongs to a public API."
        elif metric.key == "imports":
            caveat = "An import provides access; it does not establish that a declaration was used in the accepted theorem."
        else:
            caveat = "The pooled relationship mixes expected tier with runner campaign. See the source CSV for task means and all within-campaign correlations."
        draw_lines(pdf, caveat, 43, 102, page_w-86, 8.8, 13)
        pdf.showPage()

    # Provenance and interpretation page.
    header(pdf, len(METRICS)+3, "Source and interpretation notes")
    paragraphs = [
        "Inputs: paper_bencmark/highambench/reports/library-usage-analysis/attempt_usage.csv, task_usage.csv, pair_usage.csv, analyze.py and semantic_catalog.json; paper_bencmark/highambench/metadata/manifest.json. The accepted-proof hashes and dependency records are preserved in the attempt-level CSV. The source CSV byte hashes are checked by make_plots.py, which this builder imports.",
        "Aggregation: each L-side usage count is averaged over three accepted runs per task. Each gain is computed from the three-run condition means, not the mean of three per-pair percentage gains. The full 38-task analysis cohort is retained; P16-T3 had already been excluded from the source cohort because its target was documented false.",
        "Qualified occurrences count repeated textual NumStability.* references outside imports, comments and strings. Distinct qualified names count each such spelling once. Live qualified names additionally match a dependency name. Audited transitive declarations include indirect dependencies and can contain implementation-generated names. Distance-one declarations are the direct graph neighbors of the accepted theorem.",
        "Interpretation: a nonzero lexical or dependency count is evidence of observed use, not an independent measurement of how much helpful mathematics was available. Candidate and substantial counts depend on task-specific catalogs. Counts and performance may co-vary because of problem difficulty, tier design, runner changes, or other factors. These plots do not establish a causal library speedup.",
        "Rebuild: run python3 make_tier_report.py from this report directory. The script regenerates the tier-colored SVG/PNG figures, tier_exceptions.csv and this PDF. Earlier campaign-colored figures remain separate and are not used in this PDF.",
    ]
    y = page_h-83
    for paragraph in paragraphs:
        y = draw_lines(pdf, paragraph, 43, y, page_w-86, 9.5, 15)
        y -= 18
    pdf.save()


def main() -> None:
    FIGURES.mkdir(exist_ok=True)
    merged, tasks, attempts = load_data()
    exceptions = exception_rows(tasks, merged)
    assert {row["task_id"] for row in exceptions} == set(FLAG_EXPLANATIONS)
    with EXCEPTIONS_CSV.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(exceptions[0]))
        writer.writeheader()
        writer.writerows(exceptions)
    for metric in METRICS:
        svg = FIGURES / f"{metric.key}.svg"
        svg.write_text(tier_svg(merged, metric))
        subprocess.run(["sips", "-s", "format", "png", str(svg), "--out", str(svg.with_suffix(".png"))],
                       check=True, stdout=subprocess.DEVNULL)
    make_pdf(merged, exceptions)
    print(f"Generated {PDF.name}: 12 tier-colored plots, {len(exceptions)} flagged tasks, {len(attempts)} attempts")


if __name__ == "__main__":
    main()
