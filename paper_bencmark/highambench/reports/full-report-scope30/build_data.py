#!/usr/bin/env python3
"""Generate tables, figures and checks for the disclosed 30-task full report."""

from __future__ import annotations

import csv
import hashlib
import json
import statistics
import sys
from collections import Counter, defaultdict
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPORTS = HERE.parent
ROOT = HERE.parents[3]
ANALYSIS = REPORTS / "library-usage-analysis"
SCOPE = REPORTS / "scope-sensitivity-30"
BASE = REPORTS / "usage-without-tiers"
TABLES = HERE / "tables"
FIGURES = HERE / "figures"
sys.path.insert(0, str(REPORTS / "metric-comparison"))
from make_plots import read_rows  # noqa: E402 - verifies frozen source CSV hashes
from token_measurement import apply_net_new_tokens


BASE_PDF_SHA256 = "27a18f8e9826d5a78b3855faad1b5a6f908b1ada6ff79214c4b0eddef9bf08f9"
SCOPE_PAPERS = {"P02", "P17", "P20", "P33", "P35", "P40"}
ROW_END = " " + chr(92) * 2


def percent(value: float) -> str:
    return f"{value:+.1f}\\%"


def tex_escape(text: str) -> str:
    return (text.replace("–", "-").replace("—", "--").replace("\\", r"\textbackslash{}")
            .replace("&", r"\&").replace("_", r"\_").replace("%", r"\%").replace("#", r"\#"))


def mean(rows: list[dict[str, str]], key: str) -> float:
    return statistics.mean(float(row[key]) for row in rows)


def load() -> tuple[list[dict[str, str]], list[dict[str, str]], dict]:
    if hashlib.sha256((BASE / "report.pdf").read_bytes()).hexdigest() != BASE_PDF_SHA256:
        raise ValueError("Preserved full report PDF changed")
    scope = json.loads((SCOPE / "scope_manifest.json").read_text())
    if set(scope["excluded_paper_ids"]) != SCOPE_PAPERS:
        raise ValueError("Scope paper list changed")
    tasks = [row for row in read_rows("task_usage.csv")
             if row["task_id"].split("-")[0] not in SCOPE_PAPERS]
    pairs = [row for row in read_rows("pair_usage.csv")
             if row["task_id"].split("-")[0] not in SCOPE_PAPERS]
    attempts = [row for row in read_rows("attempt_usage.csv")
                if row["task_id"].split("-")[0] not in SCOPE_PAPERS]
    assert len(tasks) == 30 and len(pairs) == 90 and len(attempts) == 180
    assert len({row["task_id"].split("-")[0] for row in tasks}) == 25
    assert Counter(row["task_id"] for row in pairs) == Counter({row["task_id"]: 3 for row in tasks})
    assert {row["task_id"] for row in tasks} == {row["task_id"] for row in csv.DictReader((SCOPE / "retained_tasks.csv").open())}
    assert "P15-T3" in {row["task_id"] for row in tasks}
    apply_net_new_tokens(tasks, attempts, ROOT, HERE / "observed_net_new_tokens.json")
    return tasks, pairs, scope


def grouped_table(tasks: list[dict[str, str]]) -> None:
    lines = []
    for use in range(4):
        rows = [task for task in tasks if int(task["any_use_runs"]) == use]
        if not rows:
            lines.append(f"{use}/3 & 0 & -- & -- & -- & -- & --" + ROW_END)
            continue
        lines.append(f"{use}/3 & {len(rows)} & {percent(mean(rows, 'time_gain_pct'))} & "
                     f"{percent(mean(rows, 'loc_gain_pct'))} & {percent(mean(rows, 'token_gain_pct'))} & "
                     f"{sum(float(row['time_gain_pct']) > 0 for row in rows)}/{len(rows)} & "
                     f"{sum(float(row['loc_gain_pct']) > 0 for row in rows)}/{len(rows)}" + ROW_END)
    (TABLES / "grouped_usage.tex").write_text("\n".join(lines) + "\n\\bottomrule\n")


def task_table(tasks: list[dict[str, str]]) -> None:
    lines = []
    for row in sorted(tasks, key=lambda item: item["task_id"]):
        lines.append(
            f"{tex_escape(row['task_id'])} & {row['any_use_runs']}/3 & {row['candidate_use_runs']}/3 & "
            f"{float(row['mean_N_time']):.0f} & {float(row['mean_L_time']):.0f} & "
            f"{percent(float(row['time_gain_pct']))} & {float(row['mean_N_loc']):.0f} & "
            f"{float(row['mean_L_loc']):.0f} & {percent(float(row['loc_gain_pct']))} & "
            f"{percent(float(row['token_gain_pct']))}" + ROW_END)
    (TABLES / "all_tasks.tex").write_text("\n".join(lines) + "\n\\bottomrule\n")


def campaign_table(tasks: list[dict[str, str]], pairs: list[dict[str, str]]) -> None:
    source_by_task: dict[str, set[str]] = defaultdict(set)
    for pair in pairs:
        source_by_task[pair["task_id"]].add(pair["source_run"])
    groups = {"r09/r10": [], "r11": []}
    for task in tasks:
        label = "r11" if source_by_task[task["task_id"]] == {"results-r11"} else "r09/r10"
        groups[label].append(task)
    assert len(groups["r09/r10"]) == 18 and len(groups["r11"]) == 12
    lines = []
    for label in ("r09/r10", "r11"):
        counts = Counter(int(task["any_use_runs"]) for task in groups[label])
        lines.append(f"{label} & {len(groups[label])} & " + " & ".join(str(counts[i]) for i in range(4)) + ROW_END)
    (TABLES / "campaign_usage.tex").write_text("\n".join(lines) + "\n\\bottomrule\n")


def paper_table(tasks: list[dict[str, str]]) -> None:
    manifest = json.loads((ROOT / "paper_bencmark/highambench/metadata/manifest.json").read_text())
    titles = {paper["paper_id"]: paper["citation"] for paper in manifest["papers"]}
    selected: dict[str, list[str]] = defaultdict(list)
    for task in tasks:
        selected[task["task_id"].split("-")[0]].append(task["task_id"])
    assert len(selected) == 25 and not (set(selected) & SCOPE_PAPERS)
    lines = []
    for paper in sorted(selected):
        citation = titles[paper]
        title = f"{citation['title']} ({citation.get('date','')[:4]})"
        lines.append(f"{paper} & {tex_escape(', '.join(selected[paper]))} & {tex_escape(title)}" + ROW_END)
    (TABLES / "paper_index.tex").write_text("\n".join(lines) + "\n\\bottomrule\n")


def stats_file(tasks: list[dict[str, str]]) -> dict:
    use_groups = {i: [task for task in tasks if int(task["any_use_runs"]) == i] for i in range(4)}
    metrics = {}
    for name, nkey, lkey, gain in (("time", "mean_N_time", "mean_L_time", "time_gain_pct"),
                                   ("tokens", "mean_N_tokens", "mean_L_tokens", "token_gain_pct"),
                                   ("loc", "mean_N_loc", "mean_L_loc", "loc_gain_pct")):
        n, l = mean(tasks, nkey), mean(tasks, lkey)
        metrics[name] = {"N_mean": n, "L_mean": l, "gain_of_totals_pct": (n-l)/n*100,
                         "task_mean_gain_pct": mean(tasks, gain),
                         "tasks_L_better": sum(float(row[gain]) > 0 for row in tasks)}
    stats = {"tasks": len(tasks), "papers": 25, "pairs": 90, "attempts": 180,
             "source_campaign_tasks": {"r11": 12, "r09_r10": 18},
             "use_group_counts": {str(i): len(use_groups[i]) for i in range(4)},
             "metrics": metrics,
             "all_three_use_mean_time_gain_pct": mean(use_groups[3], "time_gain_pct"),
             "all_three_use_mean_loc_gain_pct": mean(use_groups[3], "loc_gain_pct"),
             "zero_use_mean_time_gain_pct": mean(use_groups[0], "time_gain_pct"),
             "zero_use_mean_loc_gain_pct": mean(use_groups[0], "loc_gain_pct"),
             "exclusion": "Six papers chosen after inspecting tier-fit outcomes; this is a sensitivity analysis.",
             "token_metric": "Observed net-new tokens = input - cached input + output; historical completed-response lower bound.",
             "token_ledger": "observed_net_new_tokens.json"}
    (HERE / "report_data.json").write_text(json.dumps(stats, indent=2) + "\n")
    commands = {
        "ReportTasks": "30", "ReportPapers": "25", "ReportPairs": "90", "ReportAttempts": "180",
        "ConsistentUseTasks": str(len(use_groups[3])), "ZeroUseTasks": str(len(use_groups[0])),
        "TimeGainTotals": percent(metrics["time"]["gain_of_totals_pct"]),
        "TokenGainTotals": percent(metrics["tokens"]["gain_of_totals_pct"]),
        "LocGainTotals": percent(metrics["loc"]["gain_of_totals_pct"]),
        "TimeBetterTasks": str(metrics["time"]["tasks_L_better"]),
        "TokenBetterTasks": str(metrics["tokens"]["tasks_L_better"]),
        "LocBetterTasks": str(metrics["loc"]["tasks_L_better"]),
        "ConsistentTimeMean": percent(stats["all_three_use_mean_time_gain_pct"]),
        "ConsistentLocMean": percent(stats["all_three_use_mean_loc_gain_pct"]),
        "ZeroTimeMean": percent(stats["zero_use_mean_time_gain_pct"]),
        "ZeroLocMean": percent(stats["zero_use_mean_loc_gain_pct"]),
    }
    (TABLES / "stats.tex").write_text("\n".join(
        f"\\newcommand{{\\{name}}}{{{value}}}" for name, value in commands.items()) + "\n")
    lines = [
        f"Elapsed time & {metrics['time']['N_mean']:.1f} & {metrics['time']['L_mean']:.1f} & {percent(metrics['time']['gain_of_totals_pct'])} & {metrics['time']['tasks_L_better']}/30 & seconds & mixed historical protocols" + ROW_END,
        f"Observed net-new tokens & {metrics['tokens']['N_mean']/1e6:.3f}M & {metrics['tokens']['L_mean']/1e6:.3f}M & {percent(metrics['tokens']['gain_of_totals_pct'])} & {metrics['tokens']['tasks_L_better']}/30 & tokens & incomplete lower bounds" + ROW_END,
        f"Submitted physical LOC & {metrics['loc']['N_mean']:.1f} & {metrics['loc']['L_mean']:.1f} & {percent(metrics['loc']['gain_of_totals_pct'])} & {metrics['loc']['tasks_L_better']}/30 & lines & excludes imported code" + ROW_END,
    ]
    (TABLES / "totals.tex").write_text("\n".join(lines) + "\n\\bottomrule\n")
    return stats


def main() -> None:
    TABLES.mkdir(exist_ok=True)
    FIGURES.mkdir(exist_ok=True)
    tasks, pairs, scope = load()
    grouped_table(tasks)
    task_table(tasks)
    campaign_table(tasks, pairs)
    paper_table(tasks)
    stats = stats_file(tasks)
    print(f"Built tables and figures for {stats['tasks']} tasks, {stats['papers']} papers, {stats['pairs']} pairs")


if __name__ == "__main__":
    main()
