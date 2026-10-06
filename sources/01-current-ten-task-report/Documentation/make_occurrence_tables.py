#!/usr/bin/env python3
"""Rebuild the occurrence-count tables from frozen post-run evidence.

Spearman coefficients use average ranks for ties. No contestant is rerun.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


HERE = Path(__file__).resolve().parent
GENERATED = HERE.parents[2] / "Documentation/generated"
OCCURRENCES = HERE / "direct_occurrences.json"
LEDGER = HERE.parents[2] / "benchmark/results/usage_metric_points.json"
METRICS = (
    ("occurrences_statement", "Statement occurrences"),
    ("occurrences_proof", "Proof occurrences"),
    ("occurrences_combined", "Statement + proof occurrences"),
)
OUTCOMES = (
    "total_time_gain_pct", "proof_line_gain_pct", "total_tokens_gain_pct",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ranks(values: list[float]) -> list[float]:
    order = sorted(range(len(values)), key=lambda i: values[i])
    result = [0.0] * len(values)
    cursor = 0
    while cursor < len(order):
        end = cursor + 1
        while end < len(order) and values[order[end]] == values[order[cursor]]:
            end += 1
        mean_rank = (cursor + 1 + end) / 2
        for position in order[cursor:end]:
            result[position] = mean_rank
        cursor = end
    return result


def spearman(x: list[float], y: list[float]) -> float:
    left, right = ranks(x), ranks(y)
    lx, ry = sum(left) / len(left), sum(right) / len(right)
    top = sum((a - lx) * (b - ry) for a, b in zip(left, right))
    bottom = math.sqrt(sum((a - lx) ** 2 for a in left)
                       * sum((b - ry) ** 2 for b in right))
    if bottom == 0:
        raise ValueError("constant metric or outcome")
    return top / bottom


def main() -> None:
    record = json.loads(OCCURRENCES.read_text())
    ledger = json.loads(LEDGER.read_text())
    assert record["task_count"] == len(record["rows"]) == len(ledger["rows"]) == 10
    assert record["source_metric_ledger_sha256"] == sha256(LEDGER)
    assert [r["task_id"] for r in record["rows"]] == [r["task_id"] for r in ledger["rows"]]

    count_lines = []
    for i, row in enumerate(record["rows"], 1):
        count_lines.append(
            f'{i} & {row["task_id"]} & {row["occurrences_statement"]:,} & '
            f'{row["occurrences_proof"]:,} & {row["occurrences_combined"]:,} '
            + "\\\\" + "\n"
        )
    (GENERATED / "direct_occurrence_counts.tex").write_text("".join(count_lines) + "\\bottomrule\n")

    stats: dict[str, dict[str, float]] = {}
    correlation_lines = []
    for key, label in METRICS:
        x = [float(row[key]) for row in record["rows"]]
        stats[key] = {}
        values = []
        for outcome in OUTCOMES:
            y = [float(row["gains"][outcome]) for row in ledger["rows"]]
            rho = spearman(x, y)
            stats[key][outcome] = rho
            values.append(f"{rho:+.2f}")
        correlation_lines.append(label + " & " + " & ".join(values) + " \\\\\n")
    (GENERATED / "direct_occurrence_correlations.tex").write_text("".join(correlation_lines) + "\\bottomrule\n")
    (GENERATED / "direct_occurrence_statistics.json").write_text(
        json.dumps({"source_sha256": sha256(OCCURRENCES), "spearman": stats}, indent=2) + "\n"
    )


if __name__ == "__main__":
    main()
