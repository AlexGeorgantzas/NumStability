#!/usr/bin/env python3
"""Regenerate the private ten-task report from its archived paired ledger.

This script reads only files in this repository. It never reruns a contestant,
changes a candidate, or changes an audit verdict.
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.stats import spearmanr

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DATA = ROOT / "benchmark"
SOURCE = DATA / "results/source_task_ledger.json"
SUMMARY = DATA / "results/summary.json"
REUSE = DATA / "results/realized_reuse.json"
SCAN = DATA / "results/declaration_scan.json"
REGISTRY = DATA / "results/source_registry.json"
FIG = DATA / "figures"
GEN = HERE / "generated"
BLUE, ORANGE, RED, GRAY = "#24547a", "#d27834", "#b94b55", "#59636e"
SCORE_BY_TASK: dict[str, int] = {}
SHOW_SCORES_IN_GENERAL_FIGURES = False


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name: str) -> None:
    plt.savefig(FIG / (name + ".pdf"), bbox_inches="tight", pad_inches=.12)
    plt.close()


def score_line(tasks: list[dict], scores: dict[str, int]) -> str:
    counts = Counter(scores[t["task_id"]] for t in tasks)
    return "Reuse scores: " + ", ".join(f"{s}/3 x {counts[s]}" for s in (1, 2, 3))


def short(task_id: str, with_score: bool = True) -> str:
    label = task_id.replace("P14-SHIFTED-", "P14-S-")
    return (f"{label} (R={SCORE_BY_TASK[task_id]}/3)"
            if with_score and SHOW_SCORES_IN_GENERAL_FIGURES else label)


def add_task_score_key(fig) -> None:
    if not SHOW_SCORES_IN_GENERAL_FIGURES:
        return
    fig.text(.5, .012, "Task label (R=x/3): realized NumStability reuse score",
             ha="center", va="bottom", fontsize=8)


def phases(tasks: list[dict], unit: str, filename: str) -> None:
    labels = [short(t["task_id"]) for t in tasks]
    if unit == "seconds":
        components = (("formalization_seconds_inclusive", "Formalization"),
                      ("proof_seconds_inclusive", "Proof"))
        scale, xlabel = 1, "Contestant-active seconds"
    else:
        components = (("formalization_tokens_net_new", "Formalization"),
                      ("proof_tokens_net_new", "Proof"))
        scale, xlabel = 1000, "Net-new tokens (thousands)"
    fig, axes = plt.subplots(1, 2, figsize=(11.5, 7.3), sharey=True)
    y = np.arange(len(tasks))
    for ax, (key, title) in zip(axes, components):
        ax.barh(y-.19, [t["N"][key]/scale for t in tasks], .37, color=BLUE, label="N")
        ax.barh(y+.19, [t["L"][key]/scale for t in tasks], .37, color=ORANGE, label="L")
        ax.set_yticks(y, labels)
        ax.invert_yaxis()
        ax.set_xlabel(xlabel)
        ax.set_title(title, fontweight="bold")
        ax.grid(axis="x", alpha=.2)
        ax.set_axisbelow(True)
    axes[1].legend(frameon=False)
    add_task_score_key(fig)
    fig.tight_layout(rect=(0, .045, 1, 1))
    save(filename)


def hardware(tasks: list[dict]) -> None:
    labels = [short(t["task_id"]) for t in tasks]
    y = np.arange(len(tasks))
    fig, axes = plt.subplots(1, 2, figsize=(10.5, 7.2), sharey=True)
    for ax, key, label, limit in zip(
        axes, ("peak_cpu_cores_sampled", "peak_ram_gib_sampled"),
        ("Sampled peak CPU cores", "Sampled peak RAM (GiB)"), (8, 24)
    ):
        ax.barh(y-.19, [t["N"][key] for t in tasks], .37, color=BLUE, label="N")
        ax.barh(y+.19, [t["L"][key] for t in tasks], .37, color=ORANGE, label="L")
        ax.axvline(limit, color=RED, linestyle="--", linewidth=.8, label="Lane limit")
        ax.set_yticks(y, labels)
        ax.invert_yaxis()
        ax.set_xlabel(label)
        ax.grid(axis="x", alpha=.2)
    axes[1].legend(frameon=False, fontsize=8)
    add_task_score_key(fig)
    fig.tight_layout(rect=(0, .045, 1, 1))
    save("13_hardware_peaks")


def plot_pairbars(tasks: list[dict], key: str, title: str, xlabel: str,
                  name: str, warm_add: float = 0, scale: float = 1) -> None:
    labels = [short(t["task_id"]) for t in tasks]
    y = np.arange(len(tasks))
    fig, ax = plt.subplots(figsize=(9.1, 6.5))
    ax.barh(y-.19, [t["N"][key]/scale for t in tasks], .37,
            color=BLUE, label="N: Mathlib")
    ax.barh(y+.19, [t["L"][key]/scale+warm_add for t in tasks], .37,
            color=ORANGE, label="L: NumStability")
    ax.set_yticks(y, labels, fontsize=8.5)
    ax.invert_yaxis()
    ax.set_xlabel(xlabel)
    ax.set_title(title, loc="left", fontweight="bold")
    ax.grid(axis="x", alpha=.2)
    ax.set_axisbelow(True)
    fig.legend(loc="upper center", bbox_to_anchor=(.72, .985), ncol=2,
               frameon=False, fontsize=8)
    add_task_score_key(fig)
    fig.tight_layout(rect=(0, .04, 1, .91))
    save(name)


def plot_averages(tasks: list[dict], seconds: float, tokens: int,
                  scores: dict[str, int]) -> None:
    n = len(tasks)
    groups = [
        [("Formalization", "formalization_seconds_inclusive", 1, 0),
         ("Proof", "proof_seconds_inclusive", 1, 0),
         ("Total", "total_seconds_inclusive", 1, 0),
         ("Total + warm", "total_seconds_inclusive", 1, seconds/n)],
        [("Formalization", "formalization_tokens_net_new", 1000, 0),
         ("Proof", "proof_tokens_net_new", 1000, 0),
         ("Total", "total_tokens_net_new", 1000, 0),
         ("Total + warm", "total_tokens_net_new", 1000, tokens/(1000*n))],
        [("Statement", "statement_code_lines", 1, 0),
         ("Proof", "proof_code_lines", 1, 0)],
    ]
    fig, axes = plt.subplots(1, 3, figsize=(12.1, 5))
    for ax, group, title, unit in zip(axes, groups,
                                      ("Time", "Net-new tokens", "Code"),
                                      ("Seconds/task", "Thousands/task", "Lines/task")):
        y = np.arange(len(group))
        nv = [np.mean([t["N"][key]/scale for t in tasks]) for _, key, scale, _ in group]
        lv = [np.mean([t["L"][key]/scale for t in tasks])+warm
              for _, key, scale, warm in group]
        ax.barh(y-.18, nv, height=.35, color=BLUE, label="N")
        ax.barh(y+.18, lv, height=.35, color=ORANGE, label="L")
        ax.set_yticks(y, [row[0] for row in group], fontsize=8)
        ax.invert_yaxis()
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel(unit)
        ax.grid(axis="x", alpha=.2)
        ax.set_axisbelow(True)
    axes[0].legend(frameon=False)
    if SHOW_SCORES_IN_GENERAL_FIGURES:
        fig.text(.5, .015, score_line(tasks, scores), ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .05, 1, 1))
    save("07_averages")


def plot_code(tasks: list[dict]) -> None:
    labels = [short(t["task_id"]) for t in tasks]
    y = np.arange(len(tasks))
    fig, axes = plt.subplots(1, 2, figsize=(10.7, 6.2), sharey=True)
    for ax, metric, title in zip(axes, ("statement_code_lines", "proof_code_lines"),
                                  ("Audited statement", "Kernel-accepted proof")):
        ax.barh(y-.19, [t["N"][metric] for t in tasks], .37, color=BLUE, label="N")
        ax.barh(y+.19, [t["L"][metric] for t in tasks], .37, color=ORANGE, label="L")
        ax.set_yticks(y, labels, fontsize=8)
        ax.invert_yaxis()
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("Nonblank, noncomment Lean lines")
        ax.grid(axis="x", alpha=.2)
    axes[1].legend(frameon=False)
    add_task_score_key(fig)
    fig.tight_layout(rect=(0, .05, 1, 1))
    save("08_code_lines")


def plot_direct_count(rows: list[dict], scores: dict[str, int]) -> dict:
    x = np.array([r["proof_count"] for r in rows])
    panels = (("time_gain_pct", "Total-time gain (%)"),
              ("token_gain_pct", "Net-new-token gain (%)"),
              ("proof_line_gain_pct", "Proof-line gain (%)"),
              ("formal_gain_pct", "Formalization-time gain (%)"))
    fig, axes = plt.subplots(2, 2, figsize=(9.7, 7.1))
    stats = {}
    for ax, (key, title) in zip(axes.flat, panels):
        y = np.array([r[key] for r in rows])
        for i, r in enumerate(rows):
            ax.scatter(x[i], y[i], s=100, color=SCORE_COLORS[scores[r["task_id"]]],
                       edgecolor="white", linewidth=.6, zorder=3)
            ax.text(x[i], y[i], str(scores[r["task_id"]]), ha="center",
                    va="center", color="white", fontsize=6, fontweight="bold", zorder=4)
        rho, p = spearmanr(x, y)
        stats[key] = {"rho": float(rho), "p_exploratory": float(p), "n": len(rows)}
        ax.text(.02, .98, f"Rank rho={rho:+.2f}; n={len(rows)}",
                transform=ax.transAxes, ha="left", va="top", fontsize=8,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.8))
        ax.axhline(0, color=GRAY, linewidth=.8)
        ax.set_xlabel("Distinct direct proof-term declarations")
        ax.set_ylabel(title)
        ax.grid(alpha=.18)
    fig.text(.5, .01, score_line([{"task_id": r["task_id"]} for r in rows], scores),
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .04, 1, 1))
    save("10_direct_declaration_scatter")
    return stats


def plot_cumulative(tasks: list[dict], seconds: float, tokens: int,
                    scores: dict[str, int]) -> None:
    x = np.arange(1, len(tasks)+1)
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.5))
    for ax, key, warm, divisor, title in (
        (axes[0], "total_seconds_inclusive", seconds, 1, "Cumulative active seconds"),
        (axes[1], "total_tokens_net_new", tokens, 1000, "Cumulative net-new tokens (thousands)"),
    ):
        n = np.cumsum([t["N"][key] for t in tasks])/divisor
        l = np.cumsum([t["L"][key] for t in tasks])/divisor
        ax.plot(x, n, marker="o", ms=3, color=BLUE, label="N")
        ax.plot(x, l, marker="o", ms=3, color=ORANGE, label="L")
        ax.plot(x, l+warm/divisor, marker="o", ms=3, color=RED,
                label="L + one-time warm-up")
        ax.set_xticks(x)
        ax.set_xlabel("Task in scheduled sequence")
        ax.set_ylabel(title)
        ax.grid(alpha=.18)
    axes[0].legend(frameon=False, fontsize=8)
    if SHOW_SCORES_IN_GENERAL_FIGURES:
        fig.text(.5, .01, "Scores in sequence: " + ", ".join(
            str(scores[t["task_id"]]) + "/3" for t in tasks), ha="center", fontsize=7)
    fig.tight_layout(rect=(0, .05, 1, 1))
    save("12_cumulative_warm")


SCORE_COLORS = {1: "#9c4c59", 2: "#966a21", 3: BLUE}


def gain_limits(values: list[float]) -> tuple[float, float]:
    lower, upper = min(min(values), 0), max(max(values), 0)
    pad = max(5.0, .08 * (upper - lower))
    return lower - pad, upper + pad


def task_key(fig, scored: list[dict], x_key: str, y_key: str | None = None) -> None:
    fig.text(.675, .89, "Task key", fontsize=9, fontweight="bold")
    fig.text(.975, .89, "X / Y gain" if y_key else "Gain", fontsize=8,
             ha="right", fontweight="bold")
    for number, row in enumerate(scored, start=1):
        y = .84 - (number - 1) * .066
        fig.text(.675, y,
                 f"{number}. {short(row['task_id'], with_score=False)} (R{row['score']})",
                 fontsize=7.5, color=SCORE_COLORS[row["score"]])
        value = f"{row['gains'][x_key]:+.1f}"
        if y_key:
            value += f" / {row['gains'][y_key]:+.1f}"
        fig.text(.975, y, value, fontsize=7.5, ha="right")


def plot_score_gain_graph(scored: list[dict], key: str, label: str,
                          filename: str) -> dict:
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    fig.subplots_adjust(left=.105, right=.63, top=.86, bottom=.17)
    values = [row["gains"][key] for row in scored]
    display_x = {i: float(row["score"]) for i, row in enumerate(scored)}
    close_gain_threshold = max(8.0, .04 * (max(values) - min(values)))
    for score in (0, 1, 2, 3):
        peers = sorted((i for i, row in enumerate(scored) if row["score"] == score),
                       key=lambda i: values[i])
        clusters: list[list[int]] = []
        for i in peers:
            if not clusters or values[i] - values[clusters[-1][-1]] > close_gain_threshold:
                clusters.append([i])
            else:
                clusters[-1].append(i)
        for cluster in clusters:
            for rank, i in enumerate(cluster):
                display_x[i] = score + .18 * (rank - (len(cluster) - 1) / 2)
    points = []
    for number, row in enumerate(scored, start=1):
        score, value = row["score"], row["gains"][key]
        x = display_x[number - 1]
        ax.scatter(x, value, s=170, c=SCORE_COLORS[score],
                   edgecolors="white", linewidths=.8, zorder=3)
        ax.text(x, value, str(number), ha="center", va="center",
                color="white", fontsize=8, fontweight="bold", zorder=4)
        points.append({"number": number, "task_id": row["task_id"],
                       "reuse_score": score, "x_display_score": x,
                       "gain_pct": value})
    ax.axhline(0, color=GRAY, linewidth=1)
    ax.set_xticks((0, 1, 2, 3))
    ax.set_xlim(-.35, 3.4)
    ax.set_ylim(*gain_limits(values))
    ax.set_xlabel("Realized reuse score (0-3)")
    ax.set_ylabel(label + " gain (%)")
    short_titles = {
        "formalization_time_gain_pct": "Reuse vs. formalization-time gain",
        "proof_time_gain_pct": "Reuse vs. proof-time gain",
        "total_time_gain_pct": "Reuse vs. total-time gain",
        "total_tokens_gain_pct": "Reuse vs. token gain",
        "proof_lines_gain_pct": "Reuse vs. proof-line gain",
    }
    ax.set_title(short_titles[key], loc="left", fontweight="bold")
    ax.grid(alpha=.18)
    ax.set_axisbelow(True)
    task_key(fig, scored, key)
    fig.text(.5, .055,
             "Positive gain = L better. Small horizontal offsets separate equal-score tasks.",
             ha="center", fontsize=8)
    save(filename)
    return {"x_metric": "realized_reuse_score", "y_metric": key,
            "horizontal_offset_display_only": True, "points": points}


def plot_gain_pair_graph(scored: list[dict], x_key: str, x_label: str,
                         y_key: str, y_label: str, filename: str) -> dict:
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    fig.subplots_adjust(left=.105, right=.63, top=.86, bottom=.17)
    x_values = [row["gains"][x_key] for row in scored]
    y_values = [row["gains"][y_key] for row in scored]
    points = []
    for number, row in enumerate(scored, start=1):
        score = row["score"]
        x, y = row["gains"][x_key], row["gains"][y_key]
        ax.scatter(x, y, s=170, c=SCORE_COLORS[score], edgecolors="white",
                   linewidths=.8, zorder=3)
        ax.text(x, y, str(number), ha="center", va="center", color="white",
                fontsize=8, fontweight="bold", zorder=4)
        points.append({"number": number, "task_id": row["task_id"],
                       "reuse_score": score, "x_gain_pct": x, "y_gain_pct": y})
    ax.axhline(0, color=GRAY, linewidth=1)
    ax.axvline(0, color=GRAY, linewidth=1)
    ax.set_xlim(*gain_limits(x_values))
    ax.set_ylim(*gain_limits(y_values))
    ax.set_xlabel(x_label + " gain (%)")
    ax.set_ylabel(y_label + " gain (%)")
    short_title = ("Formalization vs. proof-time gain"
                   if x_key == "formalization_time_gain_pct"
                   else "Total-time vs. token gain")
    ax.set_title(short_title, loc="left", fontweight="bold")
    ax.grid(alpha=.18)
    ax.set_axisbelow(True)
    task_key(fig, scored, x_key, y_key)
    fig.text(.5, .055, "Positive gain = L better on that axis. Color follows reuse score.",
             ha="center", fontsize=8)
    save(filename)
    return {"x_metric": x_key, "y_metric": y_key, "points": points}


def plot_score_groups(tasks: list[dict], scores: dict[str, int]) -> None:
    fig, axes = plt.subplots(1, 3, figsize=(11.2, 4))
    for ax, key, title in zip(axes,
                              ("total_seconds_inclusive", "proof_code_lines", "total_tokens_net_new"),
                              ("Active time", "Proof code", "Net-new tokens")):
        values = []
        counts = []
        for score in (1, 2, 3):
            group = [t for t in tasks if scores[t["task_id"]] == score]
            n = sum(t["N"][key] for t in group)
            l = sum(t["L"][key] for t in group)
            values.append(100*(n-l)/n)
            counts.append(len(group))
        y = np.arange(3)
        ax.barh(y, values, color=["#267e67" if v >= 0 else RED for v in values])
        ax.set_yticks(y, [f"Score {s}/3 (n={n})" for s, n in zip((1, 2, 3), counts)], fontsize=8)
        ax.invert_yaxis()
        ax.set_xlim(-75, 75)
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("Aggregate gain for L (%)")
        ax.axvline(0, color=GRAY, linewidth=.8)
        for i, value in enumerate(values):
            ax.text(value+(1 if value >= 0 else -1), i, f"{value:+.1f}%",
                    ha="left" if value >= 0 else "right", va="center", fontsize=8)
        ax.grid(axis="x", alpha=.18)
    fig.tight_layout()
    save("15_reuse_score_groups")


def plot_attempts(tasks: list[dict]) -> None:
    labels = [short(t["task_id"]) for t in tasks]
    y = np.arange(len(tasks))
    fig, axes = plt.subplots(1, 2, figsize=(10.5, 6.1), sharey=True)
    for ax, key, title in zip(axes,
                              ("formalization_submissions", "proof_submissions"),
                              ("Faithfulness submissions", "Proof submissions")):
        ax.barh(y-.19, [t["N"][key] for t in tasks], .37, color=BLUE, label="N")
        ax.barh(y+.19, [t["L"][key] for t in tasks], .37, color=ORANGE, label="L")
        ax.set_yticks(y, labels, fontsize=8)
        ax.invert_yaxis()
        ax.set_xlim(0, 4.4)
        ax.set_xticks((0, 1, 2, 3, 4))
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("Frozen submissions (maximum four)")
        ax.grid(axis="x", alpha=.18)
    axes[1].legend(frameon=False)
    add_task_score_key(fig)
    fig.tight_layout(rect=(0, .05, 1, 1))
    save("16_attempts")


def write_tables(tasks: list[dict], scans: list[dict], reuse: list[dict]) -> None:
    with (GEN / "task_times_table.tex").open("w") as out:
        for t in tasks:
            n, l = t["N"], t["L"]
            values = [t["task_id"],
                      *(f'{v["formalization_seconds_inclusive"]:.0f}' for v in (n, l)),
                      *(f'{v["proof_seconds_inclusive"]:.0f}' for v in (n, l)),
                      *(f'{v["total_seconds_inclusive"]:.0f}' for v in (n, l)),
                      *(f'{v["total_tokens_net_new"]/1000:.0f}' for v in (n, l))]
            out.write(" & ".join(values) + r" \\" + "\n")
    with (GEN / "task_code_table.tex").open("w") as out:
        for t, scan in zip(tasks, scans):
            n, l = t["N"], t["L"]
            values = [t["task_id"], t["source_cluster"],
                      str(n["statement_code_lines"]), str(l["statement_code_lines"]),
                      str(n["proof_code_lines"]), str(l["proof_code_lines"]),
                      str(scan["substantive_statement_count"]),
                      str(scan["proof_count"]),
                      str(l["formalization_submissions"]), str(l["proof_submissions"])]
            out.write(" & ".join(values) + r" \\" + "\n")
    with (GEN / "reuse_table.tex").open("w") as out:
        for r in reuse:
            values = [r["task_id"], str(r["score"]),
                      *("yes" if r["roles"][role]["used"] else "--"
                        for role in ("foundation", "computation", "analysis")),
                      *(f'{r["gains"][key]:+.0f}' for key in
                        ("proof_lines_gain_pct", "proof_time_gain_pct",
                         "total_time_gain_pct", "total_tokens_gain_pct"))]
            out.write(" & ".join(values) + r" \\" + "\n")
    with (GEN / "declarations_table.tex").open("w") as out:
        for scan in scans:
            def family(names):
                rules = (("fl_recursiveSum", "recursive sum"), ("fl_dotProduct", "dot product"),
                         ("SumTree", "sum tree"), ("FloatingPointFormat", "finite FP format"),
                         ("LSNormwiseBackwardError", "least squares"),
                         ("gamma", "gamma bound"), ("prod_error_bound", "product error"),
                         ("infNormVec", "infinity norm"))
                labels = [label for pattern, label in rules if any(pattern in name for name in names)]
                return ", ".join(labels[:3]) if labels else ("other" if names else "none")
            stmt = scan["substantive_statement_names"]
            proof = scan["proof_names"]
            values = [scan["task_id"], family(stmt), str(len(stmt)), family(proof), str(len(proof))]
            out.write(" & ".join(values) + r" \\" + "\n")


def write_aggregate_table(summary: dict) -> None:
    measured = summary["groups"]["reported"]["metrics"]
    rows = [
        ("Formalization seconds", "formalization_seconds_inclusive", 0),
        ("Proof seconds", "proof_seconds_inclusive", 0),
        ("Total active seconds", "total_seconds_inclusive", 0),
        ("Total + warm seconds", "total_seconds_inclusive", summary["warm_seconds"]),
        ("Formalization net-new tokens", "formalization_tokens_net_new", 0),
        ("Proof net-new tokens", "proof_tokens_net_new", 0),
        ("Total net-new tokens", "total_tokens_net_new", 0),
        ("Total + warm net-new tokens", "total_tokens_net_new", summary["warm_net_new_tokens"]),
        ("Statement code lines", "statement_code_lines", 0),
        ("Proof code lines", "proof_code_lines", 0),
    ]
    with (GEN / "aggregate_table.tex").open("w") as out:
        for label, metric, warm in rows:
            n = measured[metric]["N"]
            l = measured[metric]["L"] + warm
            displayed = ((f"{n:,.1f}", f"{l:,.1f}") if "seconds" in label
                         else (f"{n:,.0f}", f"{l:,.0f}"))
            out.write(f"{label} & {displayed[0]} & {displayed[1]} & "
                      f"{l/n:.3f} & {100*(n-l)/n:+.1f}\\% \\\\\n")
        out.write("\\bottomrule\n")


def main() -> None:
    global SCORE_BY_TASK
    ledger = json.loads(SOURCE.read_text())
    summary = json.loads(SUMMARY.read_text())
    reuse_record = json.loads(REUSE.read_text())
    scans = json.loads(SCAN.read_text())
    registry = json.loads(REGISTRY.read_text())
    tasks = ledger["tasks"]
    ids = [t["task_id"] for t in tasks]
    assert len(tasks) == 10 and ids == summary["scheduled_task_ids"]
    assert set(ids) == set(registry["tasks"])
    assert ids == [r["task_id"] for r in scans]
    assert ids == [r["task_id"] for r in reuse_record["rows"]]
    assert all(t["paired_statement_eligible"] and t["paired_proof_eligible"] for t in tasks)
    assert all(t[condition]["proof_status"] == "PROVED_FROZEN_STATEMENT"
               for t in tasks for condition in ("N", "L"))
    for task in tasks:
        task_id = task["task_id"]
        packet = DATA / "tasks" / f"{task_id}.json"
        pair = json.loads((DATA / "runs" / task_id / "pair-report.json").read_text())
        assert digest(packet) == registry["tasks"][task_id]["source_packet_sha256"]
        assert pair["source_packet_sha256"] == digest(packet)
        assert pair["task_id"] == task_id
        assert pair["faithfulness_status"] == "BOTH_FAITHFUL"
        assert pair["proof_pair_status"] == "BOTH_PROVED_FROZEN_STATEMENTS"

    reuse = reuse_record["rows"]
    SCORE_BY_TASK = {r["task_id"]: r["score"] for r in reuse}
    for task, scan, row in zip(tasks, scans, reuse):
        task_id = task["task_id"]
        assert scan["task_id"] == row["task_id"] == task_id
        assert row["source_packet_sha256"] == digest(DATA / "tasks" / f"{task_id}.json")
        statement = set(scan["statement_names"])
        proof = set(scan["proof_names"])
        for role in ("foundation", "computation", "analysis"):
            witnesses = set(row["roles"][role]["witnesses"])
            assert witnesses <= statement | proof
            if role == "analysis":
                assert witnesses <= proof
        assert row["score"] == sum(bool(row["roles"][role]["witnesses"])
                                   for role in ("foundation", "computation", "analysis"))
        for gain_key, metric in (
            ("formalization_time_gain_pct", "formalization_seconds_inclusive"),
            ("proof_time_gain_pct", "proof_seconds_inclusive"),
            ("total_time_gain_pct", "total_seconds_inclusive"),
            ("total_tokens_gain_pct", "total_tokens_net_new"),
            ("proof_lines_gain_pct", "proof_code_lines"),
        ):
            n, l = task["N"][metric], task["L"][metric]
            assert abs(row["gains"][gain_key] - 100 * (n - l) / n) < 1e-9
    for metric in ("formalization_seconds_inclusive", "proof_seconds_inclusive",
                   "total_seconds_inclusive", "formalization_tokens_net_new",
                   "proof_tokens_net_new", "total_tokens_net_new",
                   "statement_code_lines", "proof_code_lines"):
        for condition in ("N", "L"):
            reported = summary["groups"]["reported"]["metrics"][metric][condition]
            observed = sum(t[condition][metric] for t in tasks)
            assert abs(reported - observed) < 1e-6

    FIG.mkdir(exist_ok=True)
    GEN.mkdir(exist_ok=True)
    seconds = summary["warm_seconds"]
    tokens = summary["warm_net_new_tokens"]
    plot_pairbars(tasks, "total_seconds_inclusive", "Total active time, excluding one-time warm-up",
                  "Contestant-active seconds", "01_total_time_ex_warm")
    plot_pairbars(tasks, "total_seconds_inclusive", "Total active time, warm-up allocated over ten tasks",
                  f"Contestant-active seconds + {seconds/10:.2f} s/task for L",
                  "02_total_time_in_warm", warm_add=seconds/10)
    phases(tasks, "seconds", "03_phase_times")
    plot_pairbars(tasks, "total_tokens_net_new", "Net-new tokens, excluding warm-up",
                  "Net-new tokens (thousands)", "04_total_tokens_ex_warm", scale=1000)
    plot_pairbars(tasks, "total_tokens_net_new", "Net-new tokens, warm-up allocated over ten tasks",
                  f"Net-new tokens (thousands) + {tokens/10000:.2f}k/task for L",
                  "05_total_tokens_in_warm", warm_add=tokens/10000, scale=1000)
    phases(tasks, "tokens", "06_phase_tokens")
    plot_averages(tasks, seconds, tokens, SCORE_BY_TASK)
    plot_code(tasks)
    graphs = {}
    for key, label, filename in (
        ("formalization_time_gain_pct", "Formalization time", "09a_reuse_formalization_scatter"),
        ("proof_time_gain_pct", "Proof time", "09b_reuse_proof_scatter"),
        ("total_time_gain_pct", "Total active time", "09c_reuse_total_scatter"),
        ("total_tokens_gain_pct", "Total net-new tokens", "09d_reuse_tokens_scatter"),
        ("proof_lines_gain_pct", "Proof-code lines", "09e_reuse_proof_lines_scatter"),
    ):
        graphs[filename] = plot_score_gain_graph(reuse, key, label, filename)
    plot_direct_count(scans, SCORE_BY_TASK)
    plot_cumulative(tasks, seconds, tokens, SCORE_BY_TASK)
    hardware(tasks)
    graphs["14a_formalization_vs_proof_scatter"] = plot_gain_pair_graph(
        reuse, "formalization_time_gain_pct", "Formalization time",
        "proof_time_gain_pct", "Proof time", "14a_formalization_vs_proof_scatter")
    graphs["14b_total_time_vs_tokens_scatter"] = plot_gain_pair_graph(
        reuse, "total_time_gain_pct", "Total active time",
        "total_tokens_gain_pct", "Total net-new tokens", "14b_total_time_vs_tokens_scatter")
    assert graphs == json.loads((DATA / "results/scatter_points.json").read_text())["graphs"]
    plot_score_groups(tasks, SCORE_BY_TASK)
    plot_attempts(tasks)
    write_tables(tasks, scans, reuse)
    write_aggregate_table(summary)
    expected = {p.stem for p in FIG.glob("*.pdf")}
    legacy = {
        "01_total_time_ex_warm", "02_total_time_in_warm", "03_phase_times",
        "04_total_tokens_ex_warm", "05_total_tokens_in_warm", "06_phase_tokens",
        "07_averages", "08_code_lines", "09a_reuse_formalization_scatter",
        "09b_reuse_proof_scatter", "09c_reuse_total_scatter",
        "09d_reuse_tokens_scatter", "09e_reuse_proof_lines_scatter",
        "10_direct_declaration_scatter", "12_cumulative_warm",
        "13_hardware_peaks", "14a_formalization_vs_proof_scatter",
        "14b_total_time_vs_tokens_scatter", "15_reuse_score_groups", "16_attempts",
    }
    assert legacy <= expected, legacy - expected
    print("PASS: ten archived pairs, exact task inputs, metric sums, reuse witnesses, "
          "tables, and 20 figures")


if __name__ == "__main__":
    main()
