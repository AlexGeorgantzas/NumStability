#!/usr/bin/env python3
"""Compare archived NumStability-use measures without collapsing them to a score.

Every dot is one of the 38 archived tasks, averaged over its three L/N pairs.
This script consumes, but never changes, the frozen usage-analysis CSVs.
"""

from __future__ import annotations

import csv
import hashlib
import html
import math
import statistics
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "library-usage-analysis"
FIGURES = HERE / "figures"
SOURCE_SHA256 = {
    "attempt_usage.csv": "bd536d94b2c5e98eebc68d8e3e81a96b879498278317f21eee5bc2dc9712a43a",
    "pair_usage.csv": "cdd8a6934f80d395d82577a3794ad3a16cc33a860268b40781984a386cad2445",
    "task_usage.csv": "b0951d1b11d238cace641b2a99d55044e4aeee79bc2d75920165cd0944700b04",
}


@dataclass(frozen=True)
class Metric:
    key: str
    title: str
    definition: str
    input_column: str | None = None


METRICS = [
    Metric("qualified_distinct", "Distinct qualified names", "Distinct NumStability.* names written outside imports, comments and strings", "mean_L_qualified_distinct"),
    Metric("qualified_occurrences", "Qualified-name occurrences", "Every NumStability.* occurrence written outside imports, comments and strings"),
    Metric("transitive", "Audited transitive declarations", "All NumStability dependencies in the accepted theorem's audited dependency closure", "mean_L_transitive"),
    Metric("qualified_live_distinct", "Distinct qualified live names", "Written qualified names also matched to a name in the audited closure", "mean_L_qualified_live_distinct"),
    Metric("distance1", "Direct audited dependencies", "NumStability declarations at dependency-graph distance one from the accepted theorem", "mean_L_distance1"),
    Metric("public_transitive", "Filtered transitive declarations", "Transitive declarations after the archive's limited generated-name filter", "mean_L_public_transitive"),
    Metric("imports", "NumStability imports", "Distinct NumStability import lines in the accepted source", "mean_L_imports"),
    Metric("modules", "Dependency modules", "Distinct NumStability modules owning audited dependency declarations", "mean_L_modules"),
    Metric("candidates", "Task-listed candidate hits", "Task-specific candidate names present anywhere in the audited dependency closure", "mean_L_candidates"),
    Metric("direct_candidates", "Direct candidate hits", "Task-specific candidate names at dependency-graph distance one", "mean_L_direct_candidates"),
    Metric("substantial_hits", "Substantial audited hits", "Task-relevant substantial declarations in the audited closure", "mean_L_substantial_hits"),
    Metric("substantial_explicit", "Explicit substantial hits", "Task-relevant substantial declarations named directly in source", "mean_L_substantial_explicit"),
]

OUTCOMES = [
    ("time_gain_pct", "Elapsed-time gain", "#0b6990"),
    ("loc_gain_pct", "Submitted-source-line gain", "#22856c"),
    ("token_gain_pct", "Observed-token gain", "#bd7536"),
]


def read_rows(name: str) -> list[dict[str, str]]:
    actual_hash = hashlib.sha256((SOURCE / name).read_bytes()).hexdigest()
    if actual_hash != SOURCE_SHA256[name]:
        raise ValueError(f"Input hash mismatch: {name}")
    with (SOURCE / name).open(newline="") as stream:
        return list(csv.DictReader(stream))


def f(row: dict[str, str], key: str) -> float:
    return float(row[key])


def esc(s: object) -> str:
    return html.escape(str(s), quote=True)


def ranks(values: list[float]) -> list[float]:
    ordered = sorted(enumerate(values), key=lambda x: x[1])
    result = [0.0] * len(values)
    start = 0
    while start < len(values):
        end = start + 1
        while end < len(values) and ordered[end][1] == ordered[start][1]:
            end += 1
        average_rank = (start + 1 + end) / 2
        for original_index, _ in ordered[start:end]:
            result[original_index] = average_rank
        start = end
    return result


def pearson(xs: list[float], ys: list[float]) -> float:
    if len(xs) < 3:
        return math.nan
    mx, my = statistics.mean(xs), statistics.mean(ys)
    numerator = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    dx = sum((x - mx) ** 2 for x in xs)
    dy = sum((y - my) ** 2 for y in ys)
    return numerator / math.sqrt(dx * dy) if dx and dy else math.nan


def spearman(xs: list[float], ys: list[float]) -> float:
    return pearson(ranks(xs), ranks(ys))


def rounded_axis(maximum: float) -> tuple[float, list[float]]:
    if maximum <= 2:
        top = 2.0
        return top, [0, 0.5, 1, 1.5, 2]
    if maximum <= 5:
        top = math.ceil(maximum)
        return top, list(range(0, int(top) + 1))
    interval = 2 if maximum <= 16 else 5 if maximum <= 40 else 20 if maximum <= 160 else 50
    top = math.ceil(maximum / interval) * interval
    return top, list(range(0, int(top) + 1, interval))


def jitter(task_id: str, salt: str) -> float:
    value = hashlib.sha256(f"{task_id}:{salt}".encode()).digest()[0]
    return (value / 255 - 0.5) * 10


def svg_plot(tasks: list[dict[str, object]], metric: Metric, selected_outcomes: list[tuple[str, str, str]] = OUTCOMES) -> str:
    width = 1320 if len(selected_outcomes) == 3 else 520
    height = 520
    panel_width = 400 if len(selected_outcomes) == 3 else 475
    gap = 24
    start_x, plot_top, plot_height = 25, 110, 315
    plot_left_offset = 65
    plot_width = panel_width - 100
    x_max, ticks = rounded_axis(max(f(task, metric.key) for task in tasks))
    campaign_colors = {"r11": "#146fa3", "r09/r10": "#d27c34"}
    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        f'<rect width="{width}" height="{height}" fill="#fff"/>',
        f'<text x="{width/2:.1f}" y="31" text-anchor="middle" font-family="Arial,sans-serif" font-weight="bold" font-size="21" fill="#172b42">{esc(metric.title)}</text>',
        f'<text x="{width/2:.1f}" y="55" text-anchor="middle" font-family="Arial,sans-serif" font-size="12" fill="#536579">Task means across three paired runs · n=38 · positive gain favors L</text>',
        '<circle cx="55" cy="80" r="5.3" fill="#146fa3"/><text x="67" y="84" font-family="Arial,sans-serif" font-size="12" fill="#384b60">r11</text>',
        '<circle cx="125" cy="80" r="5.3" fill="#d27c34"/><text x="137" y="84" font-family="Arial,sans-serif" font-size="12" fill="#384b60">r09/r10</text>',
    ]
    # Fixed y-limits across every usage metric make the alternative plots comparable.
    y_limits = {"time_gain_pct": (-90, 100), "loc_gain_pct": (-130, 100), "token_gain_pct": (-420, 100)}
    for index, (outcome_key, outcome_title, accent) in enumerate(selected_outcomes):
        panel_x = start_x + index * (panel_width + gap)
        left = panel_x + plot_left_offset
        right = left + plot_width
        lo, hi = y_limits[outcome_key]
        lines.append(f'<text x="{panel_x+panel_width/2:.1f}" y="105" text-anchor="middle" font-family="Arial,sans-serif" font-weight="bold" font-size="14" fill="{accent}">{esc(outcome_title)}</text>')
        for tick in ticks:
            xx = left + tick / x_max * plot_width
            lines.append(f'<line x1="{xx:.1f}" y1="{plot_top}" x2="{xx:.1f}" y2="{plot_top+plot_height}" stroke="#e8edf0"/>')
            lines.append(f'<text x="{xx:.1f}" y="{plot_top+plot_height+20}" text-anchor="middle" font-family="Arial,sans-serif" font-size="10" fill="#526174">{tick:g}</text>')
        for tick in [-400, -300, -200, -100, -50, 0, 50, 100]:
            if not lo <= tick <= hi:
                continue
            yy = plot_top + (hi - tick) / (hi - lo) * plot_height
            stroke = "#8a98a8" if tick == 0 else "#e8edf0"
            lines.append(f'<line x1="{left}" y1="{yy:.1f}" x2="{right}" y2="{yy:.1f}" stroke="{stroke}"/>')
            lines.append(f'<text x="{left-8}" y="{yy+4:.1f}" text-anchor="end" font-family="Arial,sans-serif" font-size="10" fill="#526174">{tick:+d}%</text>')
        for task in tasks:
            x, y = f(task, metric.key), f(task, outcome_key)
            xx = left + x / x_max * plot_width + jitter(str(task["task_id"]), metric.key)
            yy = plot_top + (hi - y) / (hi - lo) * plot_height
            yy = min(plot_top + plot_height, max(plot_top, yy))
            color = campaign_colors[str(task["campaign"])]
            highlight = task["task_id"] == "P15-T2"
            radius = 6.2 if highlight else 4.7
            outline = "#151b23" if highlight else "#ffffff"
            lines.append(f'<circle cx="{xx:.1f}" cy="{yy:.1f}" r="{radius}" fill="{color}" fill-opacity="0.80" stroke="{outline}" stroke-width="{1.7 if highlight else 0.8}"><title>{esc(task["task_id"])}: {metric.title}={x:.2f}; {outcome_title}={y:+.2f}%</title></circle>')
        rho = spearman([f(task, metric.key) for task in tasks], [f(task, outcome_key) for task in tasks])
        lines.append(f'<text x="{panel_x+panel_width/2:.1f}" y="{height-59}" text-anchor="middle" font-family="Arial,sans-serif" font-size="12" fill="#394b61">Spearman ρ = {rho:+.2f}</text>')
        lines.append(f'<text x="{panel_x+panel_width/2:.1f}" y="{height-35}" text-anchor="middle" font-family="Arial,sans-serif" font-size="11" fill="#526174">Mean L count per task (0–{x_max:g})</text>')
    lines.append(f'<text x="{width/2:.1f}" y="{height-8}" text-anchor="middle" font-family="Arial,sans-serif" font-size="10" fill="#667588">Outlined dot: P15-T2 · dots with identical integer x are slightly jittered visually</text>')
    lines.append('</svg>')
    return "\n".join(lines) + "\n"


def main() -> None:
    FIGURES.mkdir(exist_ok=True)
    tasks = read_rows("task_usage.csv")
    attempts = read_rows("attempt_usage.csv")
    pairs = read_rows("pair_usage.csv")
    assert len(tasks) == 38 and len(attempts) == 228 and len(pairs) == 114
    assert Counter(a["task_id"] for a in attempts if a["condition"] == "L") == Counter({t["task_id"]: 3 for t in tasks})
    occurrences: dict[str, list[float]] = defaultdict(list)
    campaigns: dict[str, set[str]] = defaultdict(set)
    for attempt in attempts:
        if attempt["condition"] == "L":
            occurrences[attempt["task_id"]].append(f(attempt, "qualified_occurrences"))
            campaigns[attempt["task_id"]].add(attempt["source_run"])
    merged: list[dict[str, object]] = []
    for task in tasks:
        task_id = task["task_id"]
        row: dict[str, object] = {"task_id": task_id,
                                 "campaign": "r11" if campaigns[task_id] == {"results-r11"} else "r09/r10"}
        for metric in METRICS:
            row[metric.key] = (statistics.mean(occurrences[task_id]) if metric.key == "qualified_occurrences"
                               else f(task, metric.input_column or ""))
        for outcome_key, _, _ in OUTCOMES:
            row[outcome_key] = f(task, outcome_key)
        merged.append(row)
    assert Counter(str(row["campaign"]) for row in merged) == {"r11": 15, "r09/r10": 23}
    assert next(row for row in merged if row["task_id"] == "P15-T2")["qualified_occurrences"] == statistics.mean([30, 26, 17])

    with (HERE / "task_metrics.csv").open("w", newline="") as stream:
        columns = ["task_id", "campaign"] + [metric.key for metric in METRICS] + [key for key, _, _ in OUTCOMES]
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        writer.writerows(merged)

    associations = []
    for metric in METRICS:
        x = [f(row, metric.key) for row in merged]
        selected = [("all", merged), ("r11", [row for row in merged if row["campaign"] == "r11"]),
                    ("r09/r10", [row for row in merged if row["campaign"] == "r09/r10"])]
        for campaign, subset in selected:
            for outcome_key, _, _ in OUTCOMES:
                rho = spearman([f(row, metric.key) for row in subset], [f(row, outcome_key) for row in subset])
                associations.append({"metric": metric.key, "campaign": campaign,
                                     "outcome": outcome_key, "n": len(subset),
                                     "nonzero_tasks": sum(f(row, metric.key) > 0 for row in subset),
                                     "spearman_rho": f"{rho:.6f}"})
        (FIGURES / f"{metric.key}.svg").write_text(svg_plot(merged, metric))
    with (HERE / "associations.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["metric", "campaign", "outcome", "n", "nonzero_tasks", "spearman_rho"])
        writer.writeheader()
        writer.writerows(associations)
    print(f"Generated {len(METRICS)} SVGs, {len(merged)} task rows, {len(associations)} associations")


if __name__ == "__main__":
    main()
