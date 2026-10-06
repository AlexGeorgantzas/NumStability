#!/usr/bin/env python3
"""Regenerate supplementary proof-only tables and figures from archived CSVs.

No contestant or validator is rerun. The input SHA-256 values pin the source
analysis ledgers and retained-task identity used for this report edition.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import os
from collections import Counter, defaultdict
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "highambench-scope30-net-new"
import matplotlib.pyplot as plt
import numpy as np
from token_measurement import apply_net_new_tokens


HERE = Path(__file__).resolve().parent
ARCHIVE = HERE.parents[3]
SOURCE = Path(os.environ.get(
    "HIGHAMBENCH_USAGE_REPO",
    str(ARCHIVE),
))
PROOFS = Path(os.environ.get(
    "HIGHAMBENCH_PROOF_REPO",
    str(ARCHIVE),
))
REPORTS = SOURCE / "paper_bencmark/highambench/reports"
TASK_CSV = REPORTS / "library-usage-analysis/task_usage.csv"
ATTEMPT_CSV = REPORTS / "library-usage-analysis/attempt_usage.csv"
SCOPE_CSV = REPORTS / "scope-sensitivity-30/retained_tasks.csv"
DP_SCAN = HERE / "historical_direct_proof_scan.json"
DP_MANIFEST_SHA256 = "6d7d6a6bcd135c24b731baa0e27e83637ca5b5f74578396767be856dbc1098c0"
DP_SCANNER_SHA256 = "42c239528f4c51cecbb340c074d074e87377b5c0687d5dcde6d79d38196f11a5"
EXPECTED = {
    TASK_CSV: "b0951d1b11d238cace641b2a99d55044e4aeee79bc2d75920165cd0944700b04",
    ATTEMPT_CSV: "bd536d94b2c5e98eebc68d8e3e81a96b879498278317f21eee5bc2dc9712a43a",
    SCOPE_CSV: "28a38a3151d873a1c27c2f8cf955d38599a49dadbf0e8d2e92c6fdfbcf3fe8c8",
}
TABLES = HERE / "tables"
FIGURES = HERE / "figures"
INK = "#155e80"
ALT = "#cc7843"
MUTED = "#526172"
GAIN = "#287a59"
TIER_COLORS = {"T1": "#155e80", "T2": "#7952a5", "T3": "#cc7843"}
OUTCOMES = (
    ("time_gain_pct", "Elapsed-time gain (%)", "time"),
    ("code_loc_gain_pct", "Submitted-code-line gain (%)", "loc"),
    ("token_gain_pct", "Observed net-new-token gain (%)", "tokens"),
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def code_lines(path: Path) -> int:
    """The ten-task controller's nonblank/noncomment Lean-line rule."""
    source = path.read_text()
    depth = 0
    quoted = False
    escaped = False
    count = 0
    for line in source.splitlines():
        i = 0
        has_code = False
        while i < len(line):
            pair = line[i:i + 2]
            if depth:
                if pair == "/-":
                    depth += 1
                    i += 2
                elif pair == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            if quoted:
                has_code = True
                if escaped:
                    escaped = False
                elif line[i] == "\\":
                    escaped = True
                elif line[i] == '"':
                    quoted = False
                i += 1
                continue
            if pair == "--":
                break
            if pair == "/-":
                depth += 1
                i += 2
                continue
            if line[i] == '"':
                quoted = True
                has_code = True
            elif not line[i].isspace():
                has_code = True
            i += 1
        count += has_code
    if depth or quoted:
        raise ValueError(f"unterminated Lean comment/string: {path}")
    return count


def add_aligned_code_counts(tasks: list[dict[str, str]],
                            attempts: list[dict[str, str]]) -> dict:
    """Rescan accepted proof bytes, preserving physical LOC as a diagnostic."""
    by_task: dict[tuple[str, str], list[int]] = defaultdict(list)
    ledger = []
    root = PROOFS.resolve()
    for row in attempts:
        path = (root / row["proof_path"]).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise ValueError(f"accepted proof missing or outside archive: {path}")
        if sha256(path) != row["proof_sha256"]:
            raise ValueError(f"accepted proof hash mismatch: {path}")
        value = code_lines(path)
        assert value <= int(row["physical_loc"])
        by_task[(row["task_id"], row["condition"])].append(value)
        ledger.append({"task_id": row["task_id"], "pair_id": row["pair_id"],
                       "condition": row["condition"], "proof_sha256": sha256(path),
                       "code_lines": value, "physical_lines": int(row["physical_loc"]),
                       "proof_path": row["proof_path"]})
    for row in tasks:
        n = by_task[(row["task_id"], "N")]
        l = by_task[(row["task_id"], "L")]
        assert len(n) == len(l) == 3
        row["mean_N_code_loc"] = mean(n)
        row["mean_L_code_loc"] = mean(l)
        row["code_loc_gain_pct"] = 100 * (mean(n) - mean(l)) / mean(n)
    (HERE / "accepted_code_line_scan.json").write_text(json.dumps({
        "rule": "The design29_report.py _code_lines rule: physical lines with Lean tokens, excluding blank and comment-only lines; complete submitted file including helpers and imports.",
        "source_attempt_csv_sha256": EXPECTED[ATTEMPT_CSV],
        "attempts": sorted(ledger, key=lambda item:
                           (item["task_id"], item["pair_id"], item["condition"])),
    }, indent=2) + "\n")
    return {"N_mean": mean([row["mean_N_code_loc"] for row in tasks]),
            "L_mean": mean([row["mean_L_code_loc"] for row in tasks]),
            "L_better_tasks": sum(row["mean_L_code_loc"] < row["mean_N_code_loc"]
                                  for row in tasks)}


def add_direct_proof_counts(tasks: list[dict[str, str]],
                            attempts: list[dict[str, str]]) -> list[dict]:
    """Use the ten-task proof-term/local-helper scanner, not distance-one reach."""
    scan = json.loads(DP_SCAN.read_text())
    if (scan["schema"] != "historical-direct-proof-scan-v1"
            or scan["manifest_sha256"] != DP_MANIFEST_SHA256
            or scan["scanner_sha256"] != DP_SCANNER_SHA256
            or scan["library_commit"] != "045daf28056a6e4358d5de7c22c7a9d7acc2e80e"
            or scan["mathlib_commit"] != "e8ea1afc32790ce1d4e1a4e45cc412ba9388716b"
            or scan["lean_version"] != "4.29.0-rc3"):
        raise ValueError("historical direct-proof scan identity mismatch")
    expected = {(row["task_id"], row["pair_id"]): row for row in attempts
                if row["condition"] == "L"}
    found: dict[tuple[str, str], dict] = {}
    by_task: dict[str, list[int]] = defaultdict(list)
    for entry in scan["entries"]:
        key = (entry["task_id"], entry["pair_id"])
        if key not in expected or key in found:
            raise ValueError(f"unexpected/duplicate direct-proof scan: {key}")
        row = expected[key]
        if (entry["proof_sha256"] != row["proof_sha256"]
                or entry["attempt_sha256"] != row["attempt_sha256"]
                or entry["scanner_sha256"] != DP_SCANNER_SHA256
                or len(set(entry["direct_proof_names"])) != entry["direct_proof_count"]):
            raise ValueError(f"direct-proof scan failed accepted-source check: {key}")
        found[key] = entry
        by_task[entry["task_id"]].append(entry["direct_proof_count"])
    if len(expected) != 90 or len(found) != 90:
        raise ValueError("direct-proof scan lacks accepted L attempts")
    for task in tasks:
        values = by_task[task["task_id"]]
        if len(values) != 3:
            raise ValueError(f"task lacks three direct-proof scans: {task['task_id']}")
        task["mean_L_direct_proof"] = mean(values)
        task["direct_proof_any_runs"] = sum(value > 0 for value in values)
    return scan["entries"]


def write_aligned_totals(tasks: list[dict[str, str]], code_summary: dict) -> None:
    time_n = mean([float(row["mean_N_time"]) for row in tasks])
    time_l = mean([float(row["mean_L_time"]) for row in tasks])
    token_n = mean([float(row["mean_N_tokens"]) for row in tasks])
    token_l = mean([float(row["mean_L_tokens"]) for row in tasks])
    code_n, code_l = code_summary["N_mean"], code_summary["L_mean"]
    gain = lambda n, l: 100 * (n - l) / n
    time_better = sum(float(row["mean_L_time"]) < float(row["mean_N_time"])
                      for row in tasks)
    token_better = sum(float(row["mean_L_tokens"]) < float(row["mean_N_tokens"])
                       for row in tasks)
    rows_out = "\n".join((
        f"Elapsed time & {time_n:.1f} & {time_l:.1f} & {gain(time_n,time_l):+.1f}\\% & "
        f"{time_better}/30 & seconds & mixed historical protocols " + r"\\",
        f"Observed net-new tokens & {token_n/1e6:.3f}M & {token_l/1e6:.3f}M & "
        f"{gain(token_n,token_l):+.1f}\\% & {token_better}/30 & "
        "tokens & incomplete lower bounds " + r"\\",
        f"Submitted code lines & {code_n:.1f} & {code_l:.1f} & "
        f"{gain(code_n,code_l):+.1f}\\% & {code_summary['L_better_tasks']}/30 & "
        "lines & blank/comment-only excluded " + r"\\",
    )) + "\n\\bottomrule\n"
    (TABLES / "totals_aligned.tex").write_text(rows_out)
    (TABLES / "aligned_code_stats.tex").write_text(
        f"\\renewcommand{{\\LocGainTotals}}{{{gain(code_n,code_l):+.1f}\\%}}\n"
        f"\\renewcommand{{\\LocBetterTasks}}{{{code_summary['L_better_tasks']}}}\n"
    )


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def ranks(values: list[float]) -> list[float]:
    order = sorted(range(len(values)), key=values.__getitem__)
    result = [0.0] * len(values)
    start = 0
    while start < len(order):
        stop = start + 1
        while stop < len(order) and values[order[stop]] == values[order[start]]:
            stop += 1
        value = (start + 1 + stop) / 2
        for index in order[start:stop]:
            result[index] = value
        start = stop
    return result


def spearman(x: list[float], y: list[float]) -> float:
    a, b = ranks(x), ranks(y)
    ma, mb = mean(a), mean(b)
    numerator = sum((u-ma)*(v-mb) for u, v in zip(a, b))
    denominator = math.sqrt(sum((u-ma)**2 for u in a) * sum((v-mb)**2 for v in b))
    return numerator / denominator if denominator else float("nan")


def tex_name(value: str) -> str:
    return value.replace("_", r"\_").replace("%", r"\%")


def campaign(task: dict[str, str]) -> str:
    return "r11" if task["tier"] in {"T1", "T2"} else "r09/r10"


def save_figure(fig: plt.Figure, stem: str) -> None:
    fig.savefig(FIGURES / (stem + ".pdf"), bbox_inches="tight", pad_inches=.12)
    plt.close(fig)


def plot_secondary_source_usage(tasks: list[dict[str, str]],
                                attempts: list[dict[str, str]]) -> None:
    """Replace legacy cached-inclusive appendix plots with aligned gains."""
    by_task = defaultdict(list)
    for row in attempts:
        if row["condition"] == "L":
            by_task[row["task_id"]].append(row)
    specs = (
        ("qualified_distinct", "Distinct qualified source names",
         lambda row: float(row["mean_L_qualified_distinct"])),
        ("qualified_occurrences", "Qualified source occurrences",
         lambda row: mean([float(a["qualified_occurrences"])
                           for a in by_task[row["task_id"]]])),
        ("transitive", "Transitive audited dependencies",
         lambda row: float(row["mean_L_transitive"])),
    )
    for stem, xlabel, measure in specs:
        x = [measure(row) for row in tasks]
        fig, axes = plt.subplots(3, 1, figsize=(7.2, 9.1))
        for ax, (key, ylabel, _) in zip(axes, OUTCOMES):
            y = [float(row[key]) for row in tasks]
            rho = spearman(x, y)
            for row, xi, yi in zip(tasks, x, y):
                ax.scatter(xi, yi, s=48, color=TIER_COLORS[row["tier"]],
                           edgecolors="white", linewidths=.5)
                if row["task_id"] == "P15-T3":
                    ax.scatter(xi, yi, s=88, facecolors="none",
                               edgecolors="black", linewidths=1.0)
            ax.axhline(0, color=MUTED, linewidth=.8)
            ax.grid(alpha=.18)
            ax.set_axisbelow(True)
            ax.set_xlabel(xlabel)
            ax.set_ylabel(ylabel)
            ax.text(.03, .97, f"Spearman rho={rho:+.2f}; n=30",
                    transform=ax.transAxes, va="top", ha="left", fontsize=8,
                    bbox=dict(facecolor="white", edgecolor="none", alpha=.86))
        fig.suptitle(f"Secondary usage: {xlabel}", fontsize=13, fontweight="bold")
        fig.text(.5, .008,
                 "Blue: T1  |  Purple: T2  |  Orange: T3  |  Ring: P15-T3",
                 ha="center", fontsize=8)
        fig.tight_layout(rect=(0, .04, 1, .95), h_pad=1.7)
        fig.savefig(FIGURES / f"{stem}.png", dpi=160,
                    bbox_inches="tight", pad_inches=.12)
        svg_path = FIGURES / f"{stem}.svg"
        fig.savefig(svg_path, bbox_inches="tight", pad_inches=.12)
        svg_path.write_text("\n".join(line.rstrip() for line in
                                      svg_path.read_text().splitlines()) + "\n")
        plt.close(fig)


def plot_task_pairs(tasks: list[dict[str, str]]) -> None:
    """Show each task's three-run N/L means, as in the ten-task report."""
    ordered = sorted(tasks, key=lambda row: row["task_id"])
    specs = (
        ("mean_N_time", "mean_L_time", 1.0,
         "Contestant-active seconds", "Proof-task elapsed time", "time"),
        ("mean_N_tokens", "mean_L_tokens", 1_000.0,
         "Observed net-new tokens (thousands)", "Observed proof-task net-new tokens", "tokens"),
        ("mean_N_code_loc", "mean_L_code_loc", 1.0,
         "Nonblank, noncomment lines", "Complete submitted code", "loc"),
    )
    for n_key, l_key, scale, xlabel, title, stem in specs:
        maximum = max(float(row[key]) / scale for row in ordered
                      for key in (n_key, l_key))
        fig, axes = plt.subplots(2, 1, figsize=(7.4, 9.3))
        for ax, chunk in zip(axes, (ordered[:15], ordered[15:])):
            positions = np.arange(len(chunk))
            n = [float(row[n_key]) / scale for row in chunk]
            l = [float(row[l_key]) / scale for row in chunk]
            ax.barh(positions - .18, n, height=.34, color=INK, label="N: Mathlib")
            ax.barh(positions + .18, l, height=.34, color=ALT,
                    label="L: NumStability")
            ax.set_yticks(positions, labels=[row["task_id"] for row in chunk], fontsize=8)
            ax.invert_yaxis()
            ax.set_xlim(0, maximum * 1.06)
            ax.set_xlabel(xlabel)
            ax.grid(axis="x", alpha=.2)
            ax.set_axisbelow(True)
        handles, labels = axes[0].get_legend_handles_labels()
        fig.legend(handles, labels, loc="upper center", ncol=2, frameon=False,
                   bbox_to_anchor=(.5, .972))
        fig.suptitle(title + ": N and L task means", fontsize=13,
                     fontweight="bold", y=.998)
        fig.tight_layout(rect=(0, 0, 1, .935), h_pad=1.4)
        save_figure(fig, f"task_{stem}_nl")


def plot_cumulative_resources(tasks: list[dict[str, str]]) -> dict:
    """Task-mean resource sums in canonical ID order, not campaign makespan."""
    ordered = sorted(tasks, key=lambda row: row["task_id"])
    assert len(ordered) == 30 and len({row["task_id"] for row in ordered}) == 30
    specs = (
        ("time", "mean_N_time", "mean_L_time", 3600.0,
         "Contestant-active time (hours)", "Cumulative elapsed time"),
        ("tokens", "mean_N_tokens", "mean_L_tokens", 1_000_000.0,
         "Observed net-new tokens (million)", "Cumulative observed net-new tokens"),
        ("loc", "mean_N_loc", "mean_L_loc", 1.0,
         "Submitted physical LOC", "Cumulative submitted lines"),
    )
    checkpoint_indices = (5, 10, 15, 20, 25, 30)
    checkpoints = {k: {"task_id": ordered[k-1]["task_id"]} for k in checkpoint_indices}
    points = [{"index": i + 1, "task_id": row["task_id"]}
              for i, row in enumerate(ordered)]
    final_gains = {}
    x = np.arange(1, len(ordered) + 1)

    for stem, n_field, l_field, divisor, ylabel, title in specs:
        n = np.cumsum(np.array([float(row[n_field]) for row in ordered]))
        l = np.cumsum(np.array([float(row[l_field]) for row in ordered]))
        assert np.all(n > 0)
        gains = (n - l) / n * 100.0
        final_gains[stem] = float(gains[-1])
        for i, point in enumerate(points):
            point[stem] = {"N_sum": float(n[i]), "L_sum": float(l[i]),
                           "L_gain_pct": float(gains[i])}
        for k in checkpoint_indices:
            checkpoints[k][stem + "_gain_pct"] = float(gains[k-1])

        fig, (left, right) = plt.subplots(1, 2, figsize=(12.2, 3.9))
        left.plot(x, n / divisor, label="N", color=INK, linewidth=2.2,
                  marker="o", markersize=3.1)
        left.plot(x, l / divisor, label="L", color=ALT, linewidth=2.2,
                  marker="s", markersize=3.1)
        left.set_ylabel(ylabel)
        left.legend(frameon=False, loc="upper left")
        right.plot(x, gains, color=GAIN, linewidth=2.2,
                   marker="D", markersize=3.1)
        right.axhline(0, color=MUTED, linewidth=.9)
        right.set_ylabel("Running L gain (%)")
        right.set_title(f"Final gain: {gains[-1]:+.1f}%", fontsize=11)
        for ax in (left, right):
            ax.set_xlim(1, 30)
            ax.set_xticks([1, 5, 10, 15, 20, 25, 30])
            ax.set_xlabel("Tasks included (ID order)")
            ax.grid(alpha=.2)
            ax.set_axisbelow(True)
        fig.suptitle(f"{title}: N and L sums with running gain",
                     fontsize=13, fontweight="bold")
        fig.tight_layout(rect=(0, .015, 1, .91), w_pad=2.4)
        save_figure(fig, f"cumulative_{stem}")

    lines = []
    for k in checkpoint_indices:
        row = checkpoints[k]
        lines.append(
            f"{k} & {tex_name(row['task_id'])} & "
            f"{row['time_gain_pct']:+.1f}\\% & "
            f"{row['tokens_gain_pct']:+.1f}\\% & "
            f"{row['loc_gain_pct']:+.1f}\\% \\\\\n"
        )
    (TABLES / "cumulative_checkpoints.tex").write_text(
        "".join(lines) + "\\bottomrule\n"
    )
    payload = {
        "method": "Cumulative sums of three-run N/L task means in sorted task-ID order; not campaign chronology or parallel makespan.",
        "source_sha256": {path.name: digest for path, digest in EXPECTED.items()},
        "points": points,
        "checkpoints": checkpoints,
        "final_gain_pct": final_gains,
    }
    (HERE / "cumulative_points.json").write_text(json.dumps(payload, indent=2) + "\n")
    return {"final_gain_pct": final_gains,
            "checkpoints": checkpoints}


def plot_uptake(tasks: list[dict[str, str]]) -> dict[str, float]:
    x = [float(row["any_use_runs"]) for row in tasks]
    fig, axes = plt.subplots(3, 1, figsize=(7.2, 9.1))
    results = {}
    for ax, (key, label, _) in zip(axes, OUTCOMES):
        y = [float(row[key]) for row in tasks]
        rho = spearman(x, y)
        results[key] = rho
        for index, row in enumerate(tasks):
            xi = x[index] + ((index % 5) - 2)*.035
            ax.scatter(xi, y[index], s=46,
                       color=TIER_COLORS[row["tier"]],
                       edgecolors="white", linewidths=.5, zorder=3)
        ax.set_xlim(-.3, 3.3)
        ax.set_xticks([0, 1, 2, 3])
        ax.axhline(0, color=MUTED, linewidth=.8)
        ax.grid(alpha=.18)
        ax.set_axisbelow(True)
        ax.set_xlabel("L accepted proofs with any audited use (of 3)")
        ax.set_ylabel(label)
        ax.text(.03, .97, f"Spearman rho={rho:+.2f}; n=30", transform=ax.transAxes,
                va="top", ha="left", fontsize=8,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.86))
    fig.suptitle("Observed library uptake and paired gains", fontsize=14, fontweight="bold")
    fig.text(.5, .008, "Blue: T1  |  Purple: T2  |  Orange: T3  |  Offsets are display-only",
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .04, 1, .95), h_pad=1.7)
    save_figure(fig, "uptake_gain")
    return results


def plot_direct_usage(tasks: list[dict[str, str]]) -> dict[str, float]:
    """Primary direct-use measure: proof terms and proof-local helpers."""
    x = [float(row["mean_L_direct_proof"]) for row in tasks]
    fig, axes = plt.subplots(3, 1, figsize=(7.2, 9.1))
    results = {}
    for ax, (key, label, _) in zip(axes, OUTCOMES):
        y = [float(row[key]) for row in tasks]
        rho = spearman(x, y)
        results[key] = rho
        for row, xi, yi in zip(tasks, x, y):
            ax.scatter(xi, yi, s=52, color=TIER_COLORS[row["tier"]],
                       edgecolors="white", linewidths=.6, zorder=3)
        ax.axhline(0, color=MUTED, linewidth=.8)
        ax.grid(alpha=.18)
        ax.set_axisbelow(True)
        ax.set_xlabel("Direct proof declaration use (DP)")
        ax.set_ylabel(label)
        ax.text(.03, .97, f"Spearman rho={rho:+.2f}; n=30",
                transform=ax.transAxes, va="top", ha="left", fontsize=8,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.86))
    fig.suptitle("Proof-task gains vs. direct proof library use",
                 fontsize=14, fontweight="bold")
    fig.text(.5, .008, "Blue: T1  |  Purple: T2  |  Orange: T3  |  Tiers are prior expectations",
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .04, 1, .95), h_pad=1.7)
    save_figure(fig, "direct_usage_gains")
    return results


def direct_usage_tables(tasks: list[dict[str, str]],
                        attempts: list[dict[str, str]],
                        correlations: dict[str, float]) -> dict:
    zero_tasks = sum(float(row["mean_L_direct_proof"]) == 0 for row in tasks)
    consistent_tasks = sum(row["direct_proof_any_runs"] == 3 for row in tasks)
    (TABLES / "direct_proof_stats.tex").write_text(
        f"\\newcommand{{\\DPTimeRho}}{{{correlations['time_gain_pct']:+.2f}}}\n"
        f"\\newcommand{{\\DPCodeRho}}{{{correlations['code_loc_gain_pct']:+.2f}}}\n"
        f"\\newcommand{{\\DPTokenRho}}{{{correlations['token_gain_pct']:+.2f}}}\n"
        f"\\newcommand{{\\DPZeroTasks}}{{{zero_tasks}}}\n"
        f"\\newcommand{{\\DPConsistentTasks}}{{{consistent_tasks}}}\n"
    )
    (TABLES / "direct_usage_correlations.tex").write_text(
        "Direct proof declaration use (DP) & "
        + " & ".join(f"{correlations[key]:+.2f}" for key, _, _ in OUTCOMES)
        + " " + r"\\" + "\n\\bottomrule\n")
    tier_rows = []
    tier_stats = {}
    for tier in ("T1", "T2", "T3"):
        subset = [row for row in tasks if row["tier"] == tier]
        values = [float(row["mean_L_direct_proof"]) for row in subset]
        zero = sum(value == 0 for value in values)
        tier_stats[tier] = {"tasks": len(subset), "mean_direct": mean(values),
                            "zero_direct_tasks": zero}
        tier_rows.append(f"{tier} & {len(subset)} & {mean(values):.1f} & {zero} "
                         + r"\\" + "\n")
    (TABLES / "direct_usage_by_tier.tex").write_text("".join(tier_rows) + "\\bottomrule\n")

    resource_rows = []
    use_code_rows = []
    physical_rows = []
    for row in sorted(tasks, key=lambda item: item["task_id"]):
        resource_rows.append(
            f"{row['task_id']} & "
            f"{float(row['mean_N_time']):.0f} & {float(row['mean_L_time']):.0f} & "
            f"{float(row['time_gain_pct']):+.1f}\\% & "
            f"{float(row['mean_N_tokens']) / 1000:.0f} & "
            f"{float(row['mean_L_tokens']) / 1000:.0f} & "
            f"{float(row['token_gain_pct']):+.1f}\\% " + r"\\" + "\n")
        use_code_rows.append(
            f"{row['task_id']} & {row['tier']} & {float(row['mean_L_direct_proof']):.1f} & "
            f"{float(row['mean_N_code_loc']):.1f} & "
            f"{float(row['mean_L_code_loc']):.1f} & "
            f"{float(row['code_loc_gain_pct']):+.1f}\\% " + r"\\" + "\n")
        physical_rows.append(
            f"{row['task_id']} & {float(row['mean_N_loc']):.1f} & "
            f"{float(row['mean_L_loc']):.1f} & "
            f"{float(row['loc_gain_pct']):+.1f}\\% " + r"\\" + "\n")
    (TABLES / "all_tasks_resources.tex").write_text(
        "".join(resource_rows) + "\\bottomrule\n")
    (TABLES / "all_tasks_use_code.tex").write_text(
        "".join(use_code_rows) + "\\bottomrule\n")
    (TABLES / "physical_loc_diagnostic.tex").write_text(
        "".join(physical_rows) + "\\bottomrule\n")

    by_task = defaultdict(list)
    for row in attempts:
        if row["condition"] == "L":
            by_task[row["task_id"]].append(row)
    supplementary = (
        ("Archived direct-target reach",
         [float(row["mean_L_distance1"]) for row in tasks]),
        ("Proofs with any dependency (0--3)",
         [float(row["any_use_runs"]) for row in tasks]),
        ("Distinct qualified source names",
         [float(row["mean_L_qualified_distinct"]) for row in tasks]),
        ("Qualified source occurrences",
         [mean([float(item["qualified_occurrences"]) for item in by_task[row["task_id"]]])
          for row in tasks]),
        ("Transitive dependency count",
         [float(row["mean_L_transitive"]) for row in tasks]),
    )
    appendix_rows = []
    appendix_stats = {}
    for label, measure in supplementary:
        coefficients = [spearman(measure, [float(row[key]) for row in tasks])
                        for key, _, _ in OUTCOMES]
        appendix_stats[label] = dict(zip((key for key, _, _ in OUTCOMES), coefficients))
        appendix_rows.append(tex_name(label) + " & "
                             + " & ".join(f"{value:+.2f}" for value in coefficients)
                             + " " + r"\\" + "\n")
    (TABLES / "secondary_usage_correlations.tex").write_text(
        "".join(appendix_rows) + "\\bottomrule\n")
    return {"by_tier": tier_stats, "zero_tasks": zero_tasks,
            "consistent_tasks": consistent_tasks,
            "secondary_correlations": appendix_stats}


def plot_averages(tasks: list[dict[str, str]]) -> None:
    """Absolute condition means, not separately normalized percentage bars."""
    specs = (
        ("Time", "mean_N_time", "mean_L_time", 1.0, "Seconds/task"),
        ("Observed net-new tokens*", "mean_N_tokens", "mean_L_tokens", 1_000.0,
         "Thousands/task"),
        ("Submitted code", "mean_N_code_loc", "mean_L_code_loc", 1.0,
         "Nonblank lines/task"),
    )
    fig, axes = plt.subplots(3, 1, figsize=(7.0, 6.9))
    for ax, (title, n_key, l_key, scale, xlabel) in zip(axes, specs):
        n = mean([float(row[n_key]) for row in tasks]) / scale
        l = mean([float(row[l_key]) for row in tasks]) / scale
        ax.barh([-.18], [n], height=.35, color=INK, label="N: Mathlib")
        ax.barh([.18], [l], height=.35, color=ALT,
                label="L: NumStability")
        ax.set_yticks([])
        ax.set_ylim(.58, -.58)
        ax.set_xlim(0, max(n, l) * 1.17)
        for y, value in ((-.18, n), (.18, l)):
            ax.text(value + max(n, l) * .015, y, f"{value:.1f}",
                    ha="left", va="center", fontsize=8)
        ax.set_title(title, fontsize=11, fontweight="bold")
        ax.set_xlabel(xlabel)
        ax.grid(axis="x", alpha=.18)
        ax.set_axisbelow(True)
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, frameon=False, ncol=2,
               loc="upper center", bbox_to_anchor=(.5, 1.02))
    fig.text(.5, .005, "*Observed net-new tokens are incomplete lower bounds, not exact spend.",
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .05, 1, .90), h_pad=1.4)
    save_figure(fig, "averages_nl")


def proof_region(tasks: list[dict[str, str]], attempts: list[dict[str, str]]) -> dict:
    by_task: dict[str, dict[str, list[int]]] = defaultdict(lambda: defaultdict(list))
    for row in attempts:
        by_task[row["task_id"]][row["condition"]].append(int(row["proof_region_loc"]))
    lines = []
    n_means, l_means = [], []
    for task in sorted(tasks, key=lambda row: row["task_id"]):
        task_id = task["task_id"]
        n, l = by_task[task_id]["N"], by_task[task_id]["L"]
        assert len(n) == len(l) == 3
        nm, lm = mean(n), mean(l)
        n_means.append(nm)
        l_means.append(lm)
        gain = (nm-lm)/nm*100 if nm else float("nan")
        lines.append(f"{task_id} & {nm:.1f} & {lm:.1f} & {gain:+.1f}\\% \\\\\n")
    (TABLES / "proof_region.tex").write_text("".join(lines) + "\\bottomrule\n")
    return {"N_task_mean": mean(n_means), "L_task_mean": mean(l_means),
            "gain_of_totals_pct": (sum(n_means)-sum(l_means))/sum(n_means)*100}


def direct_declarations(scans: list[dict]) -> list[dict]:
    counts: Counter[str] = Counter()
    task_sets: dict[str, set[str]] = defaultdict(set)
    for row in scans:
        names = set(row["direct_proof_names"])
        for name in names:
            counts[name] += 1
            task_sets[name].add(row["task_id"])
    top = sorted(counts, key=lambda name: (-counts[name], name))[:14]
    lines = []
    for name in top:
        lines.append(f"{tex_name(name)} & {counts[name]} & {len(task_sets[name])} \\\\\n")
    (TABLES / "top_direct_declarations.tex").write_text("".join(lines) + "\\bottomrule\n")
    return [{"name": name, "L_proofs": counts[name], "tasks": len(task_sets[name])}
            for name in top]


def mixed_task(attempts: list[dict[str, str]]) -> None:
    found = defaultdict(dict)
    for row in attempts:
        if row["task_id"] == "P01-T1":
            found[row["pair_id"]][row["condition"]] = row
    lines = []
    for pair_id in sorted(found):
        n, l = found[pair_id]["N"], found[pair_id]["L"]
        t_gain = (float(n["time_seconds"])-float(l["time_seconds"]))/float(n["time_seconds"])*100
        loc_gain = (float(n["physical_loc"])-float(l["physical_loc"]))/float(n["physical_loc"])*100
        use = "yes" if int(l["transitive_declarations"]) else "no"
        lines.append(f"{pair_id.split('-')[-1]} & {use} & {t_gain:+.1f}\\% & {loc_gain:+.1f}\\% \\\\\n")
    (TABLES / "mixed_task.tex").write_text("".join(lines) + "\\bottomrule\n")


def main() -> None:
    for path, expected in EXPECTED.items():
        assert sha256(path) == expected, f"Source changed: {path}"
    retained = {row["task_id"] for row in rows(SCOPE_CSV)}
    tasks = [row for row in rows(TASK_CSV) if row["task_id"] in retained]
    attempts = [row for row in rows(ATTEMPT_CSV) if row["task_id"] in retained]
    assert len(tasks) == 30 and len(attempts) == 180
    assert Counter((r["task_id"], r["condition"]) for r in attempts) == Counter({
        (task["task_id"], condition): 3 for task in tasks for condition in ("N", "L")
    })
    TABLES.mkdir(exist_ok=True)
    FIGURES.mkdir(exist_ok=True)
    token_ledger = apply_net_new_tokens(tasks, attempts, PROOFS, HERE / "observed_net_new_tokens.json")
    code_summary = add_aligned_code_counts(tasks, attempts)
    scans = add_direct_proof_counts(tasks, attempts)
    write_aligned_totals(tasks, code_summary)
    plot_task_pairs(tasks)
    uptake = plot_uptake(tasks)
    direct_correlation = plot_direct_usage(tasks)
    direct_summary = direct_usage_tables(tasks, attempts, direct_correlation)
    plot_secondary_source_usage(tasks, attempts)
    plot_averages(tasks)
    proof = proof_region(tasks, attempts)
    direct = direct_declarations(scans)
    mixed_task(attempts)
    (HERE / "extended_stats.json").write_text(json.dumps({
        "source_sha256": {path.name: digest for path, digest in EXPECTED.items()},
        "token_ledger_sha256": sha256(HERE / "observed_net_new_tokens.json"),
        "token_totals": token_ledger["totals"],
        "direct_proof_scan_sha256": sha256(DP_SCAN),
        "direct_proof_manifest_sha256": DP_MANIFEST_SHA256,
        "direct_proof_scanner_sha256": DP_SCANNER_SHA256,
        "task_count": 30, "pair_count": 90, "accepted_attempts": 180,
        "aligned_code_lines": code_summary,
        "proof_region_loc": proof,
        "uptake_spearman": uptake,
        "direct_use_spearman": direct_correlation,
        "direct_use_summary": direct_summary,
        "top_direct_declarations": direct,
    }, indent=2) + "\n")
    print(json.dumps({"proof_region_loc": proof, "uptake_spearman": uptake}, indent=2))


if __name__ == "__main__":
    main()
