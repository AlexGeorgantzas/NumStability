#!/usr/bin/env python3
"""Rebuild the category-free figures and tables from archived task/pair CSVs.

No task is filtered by a historical expected-benefit label.  The six measures
shown here are outcomes and audited use observed after the runs.
"""

from __future__ import annotations

import csv
import hashlib
import html
import json
import statistics
from collections import Counter, defaultdict
from pathlib import Path


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "library-usage-analysis"
FIGURES = HERE / "figures"
TABLES = HERE / "tables"


def rows(name: str) -> list[dict[str, str]]:
    with (SOURCE / name).open(newline="") as stream:
        return list(csv.DictReader(stream))


def number(value: str) -> float:
    return float(value)


def avg(items: list[dict[str, str]], key: str) -> float:
    return statistics.mean(number(item[key]) for item in items)


def latex_escape(value: str) -> str:
    value = value.replace("–", "-").replace("—", "--")
    return value.replace("\\", r"\textbackslash{}").replace("&", r"\&").replace("_", r"\_").replace("%", r"\%").replace("#", r"\#")


def grouped_table(tasks: list[dict[str, str]]) -> None:
    grouped: dict[int, list[dict[str, str]]] = defaultdict(list)
    for task in tasks:
        grouped[int(task["any_use_runs"])].append(task)
    result = []
    for count in range(4):
        group = grouped[count]
        result.append(
            f"{count}/3 & {len(group)} & "
            f"{avg(group, 'time_gain_pct'):+.1f}\\% & "
            f"{avg(group, 'loc_gain_pct'):+.1f}\\% & "
            f"{avg(group, 'token_gain_pct'):+.1f}\\% & "
            f"{sum(number(x['time_gain_pct']) > 0 for x in group)}/{len(group)} & "
            f"{sum(number(x['loc_gain_pct']) > 0 for x in group)}/{len(group)} \\\\"
        )
    (TABLES / "grouped_usage.tex").write_text("\n".join(result) + "\n\\bottomrule\n")


def task_table(tasks: list[dict[str, str]]) -> None:
    result = []
    for task in tasks:
        result.append(
            f"{latex_escape(task['task_id'])} & "
            f"{task['any_use_runs']}/3 & {task['candidate_use_runs']}/3 & "
            f"{number(task['mean_N_time']):.0f} & {number(task['mean_L_time']):.0f} & "
            f"{number(task['time_gain_pct']):+.1f}\\% & "
            f"{number(task['mean_N_loc']):.0f} & {number(task['mean_L_loc']):.0f} & "
            f"{number(task['loc_gain_pct']):+.1f}\\% & "
            f"{number(task['token_gain_pct']):+.1f}\\% \\\\"
        )
    (TABLES / "all_tasks.tex").write_text("\n".join(result) + "\n\\bottomrule\n")


def campaign_table(tasks: list[dict[str, str]], pairs: list[dict[str, str]]) -> None:
    sources: dict[str, set[str]] = defaultdict(set)
    for pair in pairs:
        sources[pair["task_id"]].add(pair["source_run"])
    task_by_id = {task["task_id"]: task for task in tasks}
    older = [task_by_id[task_id] for task_id, labels in sources.items()
             if "results-r11" not in labels]
    later = [task_by_id[task_id] for task_id, labels in sources.items()
             if labels == {"results-r11"}]
    assert len(older) == 23 and len(later) == 15
    result = []
    for name, selected in (("Combined r09/r10", older), ("r11", later)):
        counts = Counter(int(task["any_use_runs"]) for task in selected)
        result.append(f"{name} & {len(selected)} & " + " & ".join(str(counts[i]) for i in range(4)) + " \\\\")
    (TABLES / "campaign_usage.tex").write_text("\n".join(result) + "\n\\bottomrule\n")


def paper_table(tasks: list[dict[str, str]]) -> None:
    manifest = HERE.parent.parent / "metadata" / "manifest.json"
    papers = {item["paper_id"]: item for item in json.loads(manifest.read_text())["papers"]}
    selected: dict[str, list[str]] = defaultdict(list)
    for task in tasks:
        selected[task["task_id"].split("-")[0]].append(task["task_id"])
    assert len(selected) == 31
    result = []
    for paper_id in sorted(selected):
        citation = papers[paper_id]["citation"]
        task_ids = ", ".join(selected[paper_id])
        result.append(
            f"{paper_id} & {latex_escape(task_ids)} & "
            f"{latex_escape(citation['title'])} ({citation.get('date', '')[:4]}) \\\\"
        )
    (TABLES / "paper_index.tex").write_text("\n".join(result) + "\n\\bottomrule\n")


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def deterministic_jitter(task_id: str) -> float:
    byte = hashlib.sha256(task_id.encode()).digest()[0]
    return (byte / 255 - 0.5) * 0.25


def svg_scatter(tasks: list[dict[str, str]], key: str, label: str, filename: str,
                lo: float, hi: float) -> None:
    width, height = 900, 500
    x0, y0, pw, ph = 95, 64, 740, 355
    colors = {0: "#687a8c", 1: "#719dba", 2: "#2480a7", 3: "#0b5578"}
    lines = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
             f'<rect x="0" y="0" width="{width}" height="{height}" fill="#ffffff"/>',
             f'<text x="{width/2}" y="29" text-anchor="middle" font-family="Arial,sans-serif" font-weight="bold" font-size="18" fill="#172334">{esc(label)}</text>']
    for use_count in range(4):
        x = x0 + use_count * pw / 3
        lines.append(f'<line x1="{x:.1f}" y1="{y0}" x2="{x:.1f}" y2="{y0+ph}" stroke="#e1e6eb"/>')
        lines.append(f'<text x="{x:.1f}" y="{y0+ph+27}" text-anchor="middle" font-family="Arial,sans-serif" font-size="14">{use_count}/3</text>')
    step = 25 if hi - lo <= 120 else 50
    for tick in range(int(lo // step * step), int(hi) + 1, step):
        if not lo <= tick <= hi:
            continue
        y = y0 + (hi - tick) / (hi - lo) * ph
        stroke = "#899baa" if tick == 0 else "#e1e6eb"
        lines.append(f'<line x1="{x0}" y1="{y:.1f}" x2="{x0+pw}" y2="{y:.1f}" stroke="{stroke}"/>')
        lines.append(f'<text x="{x0-12}" y="{y+4:.1f}" text-anchor="end" font-family="Arial,sans-serif" font-size="12">{tick:+d}%</text>')
    for task in tasks:
        count = int(task["any_use_runs"])
        value = number(task[key])
        x = x0 + (count + deterministic_jitter(task["task_id"])) * pw / 3
        y = y0 + (hi - value) / (hi - lo) * ph
        lines.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="5.3" fill="{colors[count]}" fill-opacity="0.81" stroke="white" stroke-width="1"><title>{esc(task["task_id"])}: {count}/3 uses, {value:+.1f}% gain</title></circle>')
    lines.append(f'<text x="{width/2}" y="{height-33}" text-anchor="middle" font-family="Arial,sans-serif" font-size="14">Accepted L proofs with audited NumStability use (out of three)</text>')
    lines.append('</svg>')
    (FIGURES / filename).write_text("\n".join(lines) + "\n")


def svg_grouped(tasks: list[dict[str, str]]) -> None:
    width, height = 900, 510
    x0, y0, pw, ph = 105, 67, 735, 335
    lo, hi = -10, 65
    metrics = [("time_gain_pct", "Elapsed time", "#155e80"),
               ("loc_gain_pct", "Source lines", "#45a394"),
               ("token_gain_pct", "Observed tokens", "#d88837")]
    grouped = {i: [t for t in tasks if int(t["any_use_runs"]) == i] for i in range(4)}
    lines = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
             f'<rect x="0" y="0" width="{width}" height="{height}" fill="#ffffff"/>',
             f'<text x="{width/2}" y="29" text-anchor="middle" font-family="Arial,sans-serif" font-weight="bold" font-size="18" fill="#172334">Task-mean gain by observed library-use frequency</text>']
    for tick in range(-10, 66, 10):
        y = y0 + (hi-tick)/(hi-lo)*ph
        lines.append(f'<line x1="{x0}" y1="{y:.1f}" x2="{x0+pw}" y2="{y:.1f}" stroke="{("#899baa" if tick == 0 else "#e1e6eb")}"/>')
        lines.append(f'<text x="{x0-13}" y="{y+4:.1f}" text-anchor="end" font-family="Arial,sans-serif" font-size="12">{tick:+d}%</text>')
    zero = y0 + hi/(hi-lo)*ph
    for i in range(4):
        center = x0 + (i+0.5)*pw/4
        for j,(key,_,color) in enumerate(metrics):
            v = avg(grouped[i],key)
            y = y0 + (hi-v)/(hi-lo)*ph
            x = center - 51 + j*36
            lines.append(f'<rect x="{x:.1f}" y="{min(y,zero):.1f}" width="28" height="{abs(zero-y):.1f}" fill="{color}"/>')
        lines.append(f'<text x="{center:.1f}" y="{y0+ph+26}" text-anchor="middle" font-family="Arial,sans-serif" font-size="14">{i}/3</text>')
        lines.append(f'<text x="{center:.1f}" y="{y0+ph+45}" text-anchor="middle" font-family="Arial,sans-serif" font-size="12" fill="#526172">n={len(grouped[i])}</text>')
    for j,(_,name,color) in enumerate(metrics):
        x=width/2-205+j*145
        lines.append(f'<rect x="{x:.1f}" y="{height-27}" width="13" height="13" fill="{color}"/><text x="{x+19:.1f}" y="{height-16}" font-family="Arial,sans-serif" font-size="12">{esc(name)}</text>')
    lines.append('</svg>')
    (FIGURES / "grouped_gain.svg").write_text("\n".join(lines) + "\n")


def main() -> None:
    FIGURES.mkdir(exist_ok=True)
    TABLES.mkdir(exist_ok=True)
    tasks = rows("task_usage.csv")
    pairs = rows("pair_usage.csv")
    assert len(tasks) == 38 and len(pairs) == 114
    assert len({x["task_id"] for x in tasks}) == 38
    assert Counter(x["task_id"] for x in pairs) == Counter({x["task_id"]: 3 for x in tasks})
    assert sum(int(x["any_use_runs"]) for x in tasks) == sum(int(x["L_any_use"]) for x in pairs)
    grouped_table(tasks)
    task_table(tasks)
    campaign_table(tasks, pairs)
    paper_table(tasks)
    svg_scatter(tasks, "time_gain_pct", "Elapsed-time gain versus realized use", "time_gain.svg", -35, 85)
    svg_scatter(tasks, "loc_gain_pct", "Submitted-source-line gain versus realized use", "loc_gain.svg", -35, 85)
    svg_scatter(tasks, "token_gain_pct", "Observed-token gain versus realized use", "token_gain.svg", -225, 85)
    svg_grouped(tasks)
    print("Generated four tables and four figures from all 38 tasks / 114 pairs")


if __name__ == "__main__":
    main()
