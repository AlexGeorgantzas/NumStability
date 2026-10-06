#!/usr/bin/env python3
"""Prepare and update the human review queue for apparent declaration leaves."""

from __future__ import annotations

import argparse
import csv
from collections import Counter, defaultdict
from pathlib import Path


CLASSIFICATIONS = {
    "unreviewed",
    "intended_public_endpoint",
    "legitimate_final_result",
    "foundational_or_interface_declaration",
    "unfinished_or_experimental",
    "generated_or_private_helper",
    "possible_duplicate",
    "genuinely_unused",
}


def read_manual(path: Path | None) -> dict[str, dict[str, str]]:
    if path is None or not path.exists():
        return {}
    with path.open(newline="", encoding="utf-8") as handle:
        rows = {row["name"]: row for row in csv.DictReader(handle)}
    invalid = sorted(
        {
            row.get("classification", "")
            for row in rows.values()
            if row.get("classification", "") not in CLASSIFICATIONS
        }
    )
    if invalid:
        raise ValueError(f"invalid leaf classifications: {invalid}")
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("apparent_leaves", type=Path)
    parser.add_argument("--manual", type=Path)
    parser.add_argument("--duplicates", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    args = parser.parse_args()

    manual = read_manual(args.manual)
    duplicate_names: set[str] = set()
    if args.duplicates is not None and args.duplicates.exists():
        with args.duplicates.open(newline="", encoding="utf-8") as handle:
            duplicate_names = {row["name"] for row in csv.DictReader(handle)}
    with args.apparent_leaves.open(newline="", encoding="utf-8") as handle:
        leaves = list(csv.DictReader(handle))

    fields = [
        "name",
        "module",
        "kind",
        "is_public",
        "direct_project_dependency_count",
        "transitive_project_dependency_count",
        "is_isolated",
        "classification",
        "review_status",
        "review_notes",
    ]
    classification_counts = Counter()
    module_counts: dict[str, Counter[str]] = defaultdict(Counter)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for leaf in leaves:
            override = manual.get(leaf["name"])
            if override is not None:
                classification = override["classification"]
                review_status = "manually_reviewed"
                notes = override.get("review_notes", "")
            elif leaf["is_public"] == "false":
                classification = "generated_or_private_helper"
                review_status = "automatic_visibility_classification"
                notes = "Non-public apparent leaf; retain until generated/private ownership is reviewed."
            elif leaf["name"] in duplicate_names:
                classification = "possible_duplicate"
                review_status = "automatic_exact_statement_candidate"
                notes = "Shares an exactly equal elaborated statement with another public declaration; aliases and API endpoints may be intentional."
            else:
                classification = "unreviewed"
                review_status = "unreviewed"
                notes = ""
            row = {
                key: leaf[key]
                for key in fields
                if key in leaf and key not in {"classification", "review_notes"}
            }
            row.update(
                {
                    "classification": classification,
                    "review_status": review_status,
                    "review_notes": notes,
                }
            )
            writer.writerow(row)
            classification_counts[classification] += 1
            module_counts[leaf["module"]][classification] += 1

    with args.summary.open("w", newline="", encoding="utf-8") as handle:
        summary_fields = [
            "module",
            "total_apparent_leaves",
            *sorted(CLASSIFICATIONS),
        ]
        writer = csv.DictWriter(handle, fieldnames=summary_fields)
        writer.writeheader()
        for module, counts in sorted(
            module_counts.items(),
            key=lambda item: (-sum(item[1].values()), item[0]),
        ):
            writer.writerow(
                {
                    "module": module,
                    "total_apparent_leaves": sum(counts.values()),
                    **{classification: counts[classification] for classification in CLASSIFICATIONS},
                }
            )
    print(
        ", ".join(
            f"{classification}={classification_counts[classification]}"
            for classification in sorted(CLASSIFICATIONS)
            if classification_counts[classification]
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
