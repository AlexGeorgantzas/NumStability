#!/usr/bin/env python3
"""Build namespace-resolved source-reference tables from frozen artifacts."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from make_occurrence_tables import spearman

HERE = Path(__file__).resolve().parent
LEDGER = HERE.parents[2] / "benchmark/results/usage_metric_points.json"
SOURCE = HERE / "source_reference_counts.json"
GENERATED = HERE.parents[2] / "Documentation/generated"
OUTCOMES = ("total_time_gain_pct", "proof_line_gain_pct", "total_tokens_gain_pct")

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    record = json.loads(SOURCE.read_text())
    ledger = json.loads(LEDGER.read_text())
    assert record["task_count"] == len(record["rows"]) == len(ledger["rows"]) == 10
    assert record["metric_ledger_sha256"] == sha256(LEDGER)
    assert [r["task_id"] for r in record["rows"]] == [r["task_id"] for r in ledger["rows"]]
    assert all(r["candidate_sha256"] == l["accepted_proof_sha256"] for r, l in zip(record["rows"], ledger["rows"]))

    lines = []
    for number, row in enumerate(record["rows"], 1):
        lines.append(f'{number} & {row["task_id"]} & {row["distinct_source_names"]} & {row["source_references"]} ' + r"\\" + "\n")
    (GENERATED / "source_reference_counts.tex").write_text("".join(lines) + "\\bottomrule\n")

    correlations = {}
    table_lines = []
    for key, label in (("distinct_source_names", "Distinct source names"),
                       ("source_references", "Written source references")):
        x = [float(r[key]) for r in record["rows"]]
        correlations[key] = {
            name: spearman(x, [float(r["gains"][name]) for r in ledger["rows"]])
            for name in OUTCOMES
        }
        table_lines.append(
            label + " & " + " & ".join(f"{correlations[key][name]:+.2f}"
                                     for name in OUTCOMES) + " " + r"\\" + "\n"
        )
    (GENERATED / "source_reference_correlations.tex").write_text(
        "".join(table_lines) + "\\bottomrule\n")
    (GENERATED / "source_reference_statistics.json").write_text(json.dumps({
        "source_sha256": sha256(SOURCE),
        "metric_ledger_sha256": sha256(LEDGER),
        "spearman": correlations,
    }, indent=2) + "\n")

if __name__ == "__main__":
    main()
