#!/usr/bin/env python3
"""Group exact structural statement fingerprints for human duplicate review."""

from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path


PROPOSITION_KINDS = {"theorem", "axiom", "opaque"}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("fingerprints", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    groups: dict[str, list[dict[str, str]]] = defaultdict(list)
    with args.fingerprints.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            if row["kind"] not in PROPOSITION_KINDS:
                continue
            if row["is_internal"] == "true" or row["is_private"] == "true":
                continue
            groups[row["type_equivalence_id"]].append(row)

    candidates = [rows for rows in groups.values() if len(rows) > 1]
    candidates.sort(key=lambda rows: (-len(rows), rows[0]["type_hash"]))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    fields = [
        "group_id",
        "group_size",
        "type_hash",
        "type_equivalence_id",
        "type_reference_count",
        "name",
        "module",
        "kind",
        "classification",
        "review_notes",
    ]
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for group_id, rows in enumerate(candidates, start=1):
            for row in sorted(rows, key=lambda item: (item["module"], item["name"])):
                writer.writerow(
                    {
                        "group_id": group_id,
                        "group_size": len(rows),
                        "type_hash": row["type_hash"],
                        "type_equivalence_id": row["type_equivalence_id"],
                        "type_reference_count": row["type_reference_count"],
                        "name": row["name"],
                        "module": row["module"],
                        "kind": row["kind"],
                        "classification": "unreviewed_possible_duplicate",
                        "review_notes": "",
                    }
                )
    print(
        f"candidate_groups={len(candidates)}, "
        f"candidate_declarations={sum(map(len, candidates))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
