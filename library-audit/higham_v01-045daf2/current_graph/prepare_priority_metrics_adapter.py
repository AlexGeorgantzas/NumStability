#!/usr/bin/env python3
"""Create the legacy-column view required by prepare_priority_reviews.py.

Schema: numstability-priority-review-metrics-adapter/1.0.0

This adapter does not recompute SCCs or transitive reachability. It maps direct
metrics from the validated current analyzer and computes the legacy
cross-module incoming edge count from unique current project dependency rows.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path


SCHEMA_VERSION = "numstability-priority-review-metrics-adapter/1.0.0"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--metrics", type=Path, required=True)
    parser.add_argument("--edges", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--provenance", type=Path, required=True)
    args = parser.parse_args()

    cross_module_incoming: Counter[str] = Counter()
    with gzip.open(args.edges, "rt", newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            if row["same_module"] == "false":
                cross_module_incoming[row["target"]] += 1

    with gzip.open(args.metrics, "rt", newline="", encoding="utf-8") as source:
        reader = csv.DictReader(source)
        if reader.fieldnames is None:
            raise ValueError("metrics CSV has no header")
        aliases = [
            "incoming_project_reference_count",
            "cross_module_incoming_count",
            "is_apparent_leaf",
            "is_project_foundational",
            "is_project_isolated",
            "is_used_outside_module",
        ]
        fields = list(reader.fieldnames) + [
            field for field in aliases if field not in reader.fieldnames
        ]
        args.output.parent.mkdir(parents=True, exist_ok=True)
        rows = 0
        with args.output.open("w", newline="", encoding="utf-8") as target:
            writer = csv.DictWriter(target, fieldnames=fields)
            writer.writeheader()
            for row in reader:
                row["incoming_project_reference_count"] = row[
                    "direct_project_consumer_count"
                ]
                row["cross_module_incoming_count"] = str(
                    cross_module_incoming[row["name"]]
                )
                row["is_apparent_leaf"] = row["no_incoming_project_edge"]
                row["is_project_foundational"] = row["no_outgoing_project_edge"]
                row["is_project_isolated"] = row["isolated_in_project_graph"]
                row["is_used_outside_module"] = row["used_by_different_module"]
                expected = str(cross_module_incoming[row["name"]] > 0).lower()
                if row["is_used_outside_module"] != expected:
                    raise ValueError(
                        f"cross-module Boolean/count mismatch for {row['name']}"
                    )
                writer.writerow(row)
                rows += 1

    provenance = {
        "schema_version": SCHEMA_VERSION,
        "source_commit": args.source_commit,
        "adapter_sha256": sha256(Path(__file__)),
        "metrics_input": str(args.metrics),
        "metrics_input_sha256": sha256(args.metrics),
        "edges_input": str(args.edges),
        "edges_input_sha256": sha256(args.edges),
        "output": str(args.output),
        "output_sha256": sha256(args.output),
        "rows": rows,
        "definitions": {
            "incoming_project_reference_count": "direct_project_consumer_count",
            "cross_module_incoming_count": "count of unique incoming project declaration pairs whose source_module differs from target_module",
            "is_apparent_leaf": "no_incoming_project_edge",
            "is_project_foundational": "no_outgoing_project_edge",
            "is_project_isolated": "isolated_in_project_graph",
            "is_used_outside_module": "used_by_different_module",
        },
        "limitation": "Compatibility view for the bundled priority-review script; it does not use recovered SCC or transitive fields.",
    }
    args.provenance.write_text(
        json.dumps(provenance, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(provenance, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
