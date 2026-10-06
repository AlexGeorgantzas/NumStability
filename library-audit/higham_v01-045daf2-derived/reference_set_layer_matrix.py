#!/usr/bin/env python3
"""Layer dependency matrix restricted to the conservative reference set.

Derived from the immutable higham_v01 audit bundle (commit 045daf2).  The
reference set is the audit's `confirmed_source_written_public` universe:
declarations with is_public = true and authorship_class =
confirmed_source_written (47,890 declarations).  Only induced edges are kept:
both endpoints must belong to the reference set.  Edge orientation follows the
audit: consumer -> dependency.

This is a new derived measurement, not part of the audit's frozen metric
contract.  It cross-checks itself against the audit's own values for the same
universe (size, Source layer size, metric M9, isolated declarations).

Usage (from the thesis repository root):
    python3 sources/library-audit/higham_v01-045daf2-derived/reference_set_layer_matrix.py
"""

import collections
import csv
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BUNDLE = ROOT.parent / "higham_v01-045daf2"
DECLS = BUNDLE / "current_graph/metrics/declaration_metrics.csv.gz"
EDGES = BUNDLE / "current_graph/metrics/direct_project_dependencies.csv.gz"
OUT_CSV = ROOT / "reference_set_layer_matrix.csv"
OUT_JSON = ROOT / "reference_set_layer_matrix_summary.json"

LOWER_REUSABLE = {"Algorithms", "Analysis", "FloatingPoint"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    layer_of = {}
    isolated = 0
    with gzip.open(DECLS, "rt", newline="") as handle:
        for row in csv.DictReader(handle):
            if (row["is_public"] == "true"
                    and row["authorship_class"] == "confirmed_source_written"):
                layer_of[row["name"]] = row["layer"]
                isolated += row["isolated_in_project_graph"] == "true"

    pairs = collections.Counter()
    consumers = collections.defaultdict(set)
    dependencies = collections.defaultdict(set)
    seen = set()
    with gzip.open(EDGES, "rt", newline="") as handle:
        for row in csv.DictReader(handle):
            source, target = row["source"], row["target"]
            if source not in layer_of or target not in layer_of:
                continue
            if (source, target) in seen:
                raise SystemExit(f"duplicate pair {source} -> {target}")
            seen.add((source, target))
            key = (layer_of[source], layer_of[target])
            pairs[key] += 1
            consumers[key].add(source)
            dependencies[key].add(target)

    layer_sizes = collections.Counter(layer_of.values())
    source_to_lower = set()
    for (src_layer, dst_layer), names in consumers.items():
        if src_layer == "Source" and dst_layer in LOWER_REUSABLE:
            source_to_lower |= names

    checks = {
        "reference_set_size": (len(layer_of), 47890),
        "source_layer_size": (layer_sizes["Source"], 30289),
        "m9_source_using_lower_layers": (len(source_to_lower), 22062),
        "isolated_in_project_graph": (isolated, 143),
    }
    failed = {k: v for k, v in checks.items() if v[0] != v[1]}
    if failed:
        raise SystemExit(f"cross-check failed: {failed}")

    with OUT_CSV.open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow([
            "consumer_layer", "dependency_layer", "unique_declaration_pairs",
            "distinct_consumer_declarations",
            "distinct_dependency_declarations",
        ])
        for key in sorted(pairs):
            writer.writerow([key[0], key[1], pairs[key],
                             len(consumers[key]), len(dependencies[key])])

    summary = {
        "schema": "numstability-reference-set-layer-matrix/1.0.0",
        "audited_commit": "045daf28056a6e4358d5de7c22c7a9d7acc2e80e",
        "universe": "is_public=true AND "
                    "authorship_class=confirmed_source_written",
        "edge_rule": "induced: both endpoints in the universe; "
                     "consumer -> dependency",
        "status": "derived measurement outside the audit metric contract",
        "inputs": {
            str(DECLS.relative_to(ROOT.parent)): sha256(DECLS),
            str(EDGES.relative_to(ROOT.parent)): sha256(EDGES),
        },
        "layer_sizes": dict(sorted(layer_sizes.items())),
        "induced_pairs_total": sum(pairs.values()),
        "cross_checks": {k: v[0] for k, v in checks.items()},
    }
    OUT_JSON.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
