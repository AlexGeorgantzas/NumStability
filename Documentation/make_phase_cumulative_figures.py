#!/usr/bin/env python3
"""Generate phase-specific ten-task figures and cumulative-gain table rows.

This reads the archived paired ledger and summary only. It never reruns a
contestant or changes a benchmark outcome.
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "benchmark" / "results"
FIGURES = ROOT / "benchmark" / "figures"
GENERATED = ROOT / "Documentation" / "generated"
BLUE = "#24547a"
ORANGE = "#d27834"


def load() -> tuple[list[dict], dict]:
    ledger = json.loads((RESULTS / "source_task_ledger.json").read_text())
    summary = json.loads((RESULTS / "summary.json").read_text())
    tasks = ledger["tasks"]
    assert len(tasks) == 10
    assert [task["task_id"] for task in tasks] == summary["scheduled_task_ids"]
    for metric in (
        "formalization_seconds_inclusive", "proof_seconds_inclusive",
        "total_seconds_inclusive", "formalization_tokens_net_new",
        "proof_tokens_net_new", "total_tokens_net_new",
    ):
        for condition in ("N", "L"):
            observed = sum(task[condition][metric] for task in tasks)
            expected = summary["groups"]["reported"]["metrics"][metric][condition]
            assert abs(observed - expected) < 1e-6, (metric, condition)
    return tasks, summary


def task_label(task: dict) -> str:
    return task["task_id"].replace("P14-SHIFTED-", "P14-S-")


def pair_bars(tasks: list[dict], metric: str, title: str,
              xlabel: str, filename: str, scale: float = 1) -> None:
    y = np.arange(len(tasks))
    fig, ax = plt.subplots(figsize=(8.2, 5.5))
    ax.barh(y - .19, [task["N"][metric] / scale for task in tasks], .37,
            color=BLUE, label="N: Mathlib")
    ax.barh(y + .19, [task["L"][metric] / scale for task in tasks], .37,
            color=ORANGE, label="L: NumStability")
    ax.set_yticks(y, [task_label(task) for task in tasks], fontsize=8.5)
    ax.invert_yaxis()
    ax.set_xlabel(xlabel)
    ax.set_title(title, loc="left", fontweight="bold")
    fig.legend(frameon=False, ncol=2, loc="upper right",
               bbox_to_anchor=(.98, .985), fontsize=8)
    ax.grid(axis="x", alpha=.2)
    ax.set_axisbelow(True)
    fig.tight_layout(rect=(0, 0, 1, .93))
    fig.savefig(FIGURES / filename, bbox_inches="tight", pad_inches=.12)
    plt.close(fig)


def gain(n: float, l: float) -> float:
    assert n > 0
    return 100 * (n - l) / n


def cumulative_phases(tasks: list[dict], unit: str, filename: str) -> None:
    if unit == "seconds":
        phase_metrics = (
            ("formalization_seconds_inclusive", "Formalization"),
            ("proof_seconds_inclusive", "Proof"),
        )
        divisor, ylabel = 1, "Cumulative contestant-active seconds"
    else:
        phase_metrics = (
            ("formalization_tokens_net_new", "Formalization"),
            ("proof_tokens_net_new", "Proof"),
        )
        divisor, ylabel = 1000, "Cumulative net-new tokens (thousands)"
    x = np.arange(1, len(tasks) + 1)
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.0), sharex=True)
    for ax, (metric, phase) in zip(axes, phase_metrics):
        n = np.cumsum([task["N"][metric] for task in tasks]) / divisor
        l = np.cumsum([task["L"][metric] for task in tasks]) / divisor
        ax.plot(x, n, marker="o", ms=3.5, color=BLUE, label="N")
        ax.plot(x, l, marker="o", ms=3.5, color=ORANGE, label="L")
        ax.set_xticks(x)
        ax.set_xlabel("Task in scheduled sequence")
        ax.set_ylabel(ylabel)
        ax.set_title(f"{phase}: final L gain {gain(n[-1], l[-1]):+.1f}%",
                     fontweight="bold", fontsize=10)
        ax.grid(alpha=.18)
    axes[0].legend(frameon=False, ncol=2, fontsize=8)
    fig.tight_layout()
    fig.savefig(FIGURES / filename, bbox_inches="tight", pad_inches=.12)
    plt.close(fig)


def milestone_rows(tasks: list[dict], summary: dict, unit: str) -> None:
    if unit == "seconds":
        metrics = (
            "formalization_seconds_inclusive", "proof_seconds_inclusive",
            "total_seconds_inclusive",
        )
        warm = summary["warm_seconds"]
    else:
        metrics = (
            "formalization_tokens_net_new", "proof_tokens_net_new",
            "total_tokens_net_new",
        )
        warm = summary["warm_net_new_tokens"]
    target = GENERATED / f"cumulative_{unit}_milestones.tex"
    with target.open("w") as output:
        for count in (1, 5, 10):
            values = []
            for metric in metrics:
                n = sum(task["N"][metric] for task in tasks[:count])
                l = sum(task["L"][metric] for task in tasks[:count])
                values.append(gain(n, l))
                if metric == metrics[-1]:
                    values.append(gain(n, l + warm))
            formatted = " & ".join(f"{value:+.1f}\\%" for value in values)
            output.write(f"{count} & {formatted} " + r"\\" + "\n")
        output.write("\\bottomrule\n")


def main() -> None:
    tasks, summary = load()
    FIGURES.mkdir(exist_ok=True)
    GENERATED.mkdir(exist_ok=True)
    for metric, title, xlabel, filename, scale in (
        ("formalization_seconds_inclusive", "Formalization time",
         "Contestant-active seconds", "03a_formalization_time.pdf", 1),
        ("proof_seconds_inclusive", "Proof time",
         "Contestant-active seconds", "03b_proof_time.pdf", 1),
        ("formalization_tokens_net_new", "Formalization tokens",
         "Net-new tokens (thousands)", "06a_formalization_tokens.pdf", 1000),
        ("proof_tokens_net_new", "Proof tokens",
         "Net-new tokens (thousands)", "06b_proof_tokens.pdf", 1000),
    ):
        pair_bars(tasks, metric, title, xlabel, filename, scale)
    cumulative_phases(tasks, "seconds", "12a_cumulative_phase_time.pdf")
    cumulative_phases(tasks, "tokens", "12b_cumulative_phase_tokens.pdf")
    milestone_rows(tasks, summary, "seconds")
    milestone_rows(tasks, summary, "tokens")
    print("PASS: six phase figures and two cumulative milestone tables")


if __name__ == "__main__":
    main()
