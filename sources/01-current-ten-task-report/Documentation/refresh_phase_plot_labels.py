#!/usr/bin/env python3
"""Render the three phase-aligned plots with a plain Library usage axis.

The exact phase-specific declaration counts and correlations come from the
archived ten-task phase ledger. This changes labels only, not coordinates.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


HERE = Path(__file__).resolve().parent
FIGURES = HERE.parents[2] / "benchmark" / "figures"
SOURCE = Path(os.environ.get(
    "NUMSTABILITY_REPORT_SOURCE",
    str(HERE.parents[2]),
))
RESULTS = SOURCE / "benchmark" / "results"
POINTS = RESULTS / "phase_usage_points.json"
PHASES = (
    ("formalization", "statement", (
        ("formalization_time_gain_pct", "Formalization-time gain (%)"),
        ("formalization_tokens_gain_pct", "Formalization net-new-token gain (%)"),
        ("statement_lines_gain_pct", "Faithful-statement-line gain (%)"),
    ), "19a_statement_use_formalization"),
    ("proof", "proof_term", (
        ("proof_time_gain_pct", "Proof-time gain (%)"),
        ("proof_tokens_gain_pct", "Proof net-new-token gain (%)"),
        ("proof_line_gain_pct", "Proof-code-line gain (%)"),
    ), "19b_proof_use_proving"),
    ("total", "union", (
        ("total_time_gain_pct", "Total active-time gain (%)"),
        ("total_tokens_gain_pct", "Total net-new-token gain (%)"),
        ("total_code_lines_gain_pct", "Statement-plus-proof-line gain (%)"),
    ), "19c_union_use_total"),
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def render(rows: list[dict], correlations: dict, phase: str, use_key: str,
           outcomes: tuple, stem: str) -> None:
    x = np.array([row["usage"][use_key] for row in rows], dtype=float)
    fig, axes = plt.subplots(1, 3, figsize=(12.2, 7.0))
    fig.suptitle(f"{phase.capitalize()} gains vs. library usage",
                 x=.50, y=.975, fontsize=15, fontweight="bold")
    for ax, (outcome, label) in zip(axes, outcomes):
        y = np.array([row["gains"][outcome] for row in rows])
        display = x.copy()
        for value in sorted(set(x)):
            peers = [i for i, v in enumerate(x) if v == value]
            peers.sort(key=lambda i: y[i])
            for offset, i in enumerate(peers):
                display[i] += .22 * (offset - (len(peers) - 1) / 2)
        ax.scatter(display, y, s=165, c="#24547a", edgecolors="white",
                   linewidths=.8, zorder=3)
        for i, row in enumerate(rows):
            ax.text(display[i], y[i], str(row["number"]), ha="center", va="center",
                    color="white", fontsize=8, fontweight="bold", zorder=4)
        rho = correlations[phase][outcome]["spearman_rho"]
        ax.text(.02, .98, f"Spearman $\\rho$={rho:+.2f}; n=10",
                transform=ax.transAxes, ha="left", va="top", fontsize=9,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.88))
        ax.axhline(0, color="#59636e", linewidth=.85)
        low, high = min(float(y.min()), 0), max(float(y.max()), 0)
        pad = max(5, .10 * (high - low))
        ax.set_ylim(low - pad, high + pad)
        ax.set_xlim(min(-1.1, x.min() - 1.1), x.max() + 1.1)
        ax.set_xlabel("Library usage", fontsize=9)
        ax.set_ylabel(label, fontsize=9)
        ax.grid(alpha=.18)
        ax.set_axisbelow(True)
    for j, row in enumerate(rows):
        col, line = j // 5, j % 5
        name = row["task_id"].replace("P14-SHIFTED-", "P14-S-")
        fig.text(.09 + .48 * col, .19 - .035 * line,
                 f"{row['number']:>2}. {name}", fontsize=8.5, ha="left")
    fig.text(.50, .008,
             "Positive gain favors L; numbered points match the task key. Horizontal offsets are visual only.",
             fontsize=8, ha="center")
    fig.tight_layout(rect=(0, .23, 1, .94), w_pad=2.0)
    fig.savefig(FIGURES / f"{stem}.pdf", bbox_inches="tight", pad_inches=.10)
    plt.close(fig)


def main() -> None:
    record = json.loads(POINTS.read_text())
    assert record["task_count"] == 10 and len(record["rows"]) == 10
    for name, expected in record["source_sha256"].items():
        assert sha256(RESULTS / name) == expected, f"Changed source: {name}"
    FIGURES.mkdir(exist_ok=True)
    for phase, use_key, outcomes, stem in PHASES:
        render(record["rows"], record["spearman"], phase, use_key, outcomes, stem)
    print("Regenerated three label-only phase figures from hash-checked data")


if __name__ == "__main__":
    main()
