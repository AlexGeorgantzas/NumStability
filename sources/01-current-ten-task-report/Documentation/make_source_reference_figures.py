#!/usr/bin/env python3
"""Plot explicit NumStability source citations against paired N-to-L gains.

The offline .ilean source-reference ledger and frozen ten-task gain ledger are
the only data inputs. The program does not rerun contestants or audits.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from make_occurrence_tables import spearman


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "source_reference_counts.json"
LEDGER = HERE.parents[2] / "benchmark/results/usage_metric_points.json"
FIGURES = HERE.parents[2] / "benchmark/figures"
OUTCOMES = (
    ("total_time_gain_pct", "Total active-time gain (%)"),
    ("proof_line_gain_pct", "Proof-code-line gain (%)"),
    ("total_tokens_gain_pct", "Net-new-token gain (%)"),
)
INK = "#24547a"
MUTED = "#59636e"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def plot(source_rows: list[dict], gain_rows: list[dict], key: str,
         x_label: str, filename: str) -> None:
    x = np.array([float(row[key]) for row in source_rows])
    fig, axes = plt.subplots(1, 3, figsize=(12.2, 6.8))
    fig.suptitle(x_label + " vs. N-to-L gains", x=.50, y=.975,
                 fontsize=15, fontweight="bold")
    for ax, (outcome, y_label) in zip(axes, OUTCOMES):
        y = np.array([float(row["gains"][outcome]) for row in gain_rows])
        rho = spearman(x.tolist(), y.tolist())
        shown = x.copy()
        for value in sorted(set(x)):
            peers = [i for i, number in enumerate(x) if number == value]
            peers.sort(key=lambda i: y[i])
            for offset, index in enumerate(peers):
                shown[index] += .15 * (offset - (len(peers) - 1) / 2)
        ax.scatter(shown, y, s=165, c=INK, edgecolors="white",
                   linewidths=.8, zorder=3)
        for number, (x_value, y_value) in enumerate(zip(shown, y), 1):
            ax.text(x_value, y_value, str(number), ha="center", va="center",
                    fontsize=8, fontweight="bold", color="white", zorder=4)
        ax.text(.02, .98, f"Spearman $\\rho$={rho:+.2f}; n=10",
                transform=ax.transAxes, ha="left", va="top", fontsize=9,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.88))
        ax.axhline(0, color=MUTED, linewidth=.85)
        low, high = min(float(y.min()), 0), max(float(y.max()), 0)
        pad = max(5.0, .10 * (high - low))
        ax.set_ylim(low - pad, high + pad)
        xpad = max(1.0, .04 * (float(x.max()) - float(x.min())))
        ax.set_xlim(float(shown.min()) - xpad, float(shown.max()) + xpad)
        ax.set_xlabel(x_label + " (count)", fontsize=9)
        ax.set_ylabel(y_label, fontsize=9)
        ax.grid(alpha=.18)
        ax.set_axisbelow(True)
    for index, row in enumerate(source_rows):
        col, line = divmod(index, 5)
        label = row["task_id"].replace("P14-SHIFTED-", "P14-S-")
        fig.text(.09 + .48 * col, .19 - .035 * line,
                 f"{index+1:>2}. {label}", fontsize=8.5, ha="left")
    fig.text(.50, .008, "Positive gain favors L; numbered points match Table 13.",
             fontsize=8, ha="center")
    fig.tight_layout(rect=(0, .23, 1, .94), w_pad=2.0)
    FIGURES.mkdir(parents=True, exist_ok=True)
    fig.savefig(FIGURES / filename, bbox_inches="tight", pad_inches=.10)
    plt.close(fig)


def main() -> None:
    source = json.loads(SOURCE.read_text())
    ledger = json.loads(LEDGER.read_text())
    rows, gains = source["rows"], ledger["rows"]
    assert source["metric_ledger_sha256"] == sha256(LEDGER)
    assert len(rows) == len(gains) == 10
    assert all(row["task_id"] == gain["task_id"] and
               row["candidate_sha256"] == gain["accepted_proof_sha256"]
               for row, gain in zip(rows, gains))
    plot(rows, gains, "distinct_source_names", "Distinct written library names",
         "20a_source_distinct_gains.pdf")
    plot(rows, gains, "source_references", "Written library references",
         "20b_source_references_gains.pdf")


if __name__ == "__main__":
    main()
