#!/usr/bin/env python3
"""Compute induced weak/strong components for source-written declarations."""

from __future__ import annotations

import csv
import gzip
import hashlib
import io
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path


SCHEMA_VERSION = "numstability-source-written-components/1.0.0"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def weak_components(nodes: set[str], adjacency: dict[str, set[str]]) -> list[list[str]]:
    undirected: dict[str, set[str]] = {node: set() for node in nodes}
    for source in nodes:
        for target in adjacency.get(source, set()):
            if target in nodes:
                undirected[source].add(target)
                undirected[target].add(source)
    seen: set[str] = set()
    result: list[list[str]] = []
    for start in sorted(nodes):
        if start in seen:
            continue
        component: list[str] = []
        stack = [start]
        seen.add(start)
        while stack:
            node = stack.pop()
            component.append(node)
            for target in undirected[node]:
                if target not in seen:
                    seen.add(target)
                    stack.append(target)
        result.append(sorted(component))
    return sorted(result, key=lambda component: (-len(component), component[0]))


def strong_components(nodes: set[str], adjacency: dict[str, set[str]]) -> list[list[str]]:
    sys.setrecursionlimit(max(200_000, len(nodes) * 3))
    index = 0
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    result: list[list[str]] = []

    def visit(node: str) -> None:
        nonlocal index
        indices[node] = index
        lowlink[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for target in sorted(adjacency.get(node, set())):
            if target not in nodes:
                continue
            if target not in indices:
                visit(target)
                lowlink[node] = min(lowlink[node], lowlink[target])
            elif target in on_stack:
                lowlink[node] = min(lowlink[node], indices[target])
        if lowlink[node] == indices[node]:
            component: list[str] = []
            while True:
                target = stack.pop()
                on_stack.remove(target)
                component.append(target)
                if target == node:
                    break
            result.append(sorted(component))

    for node in sorted(nodes):
        if node not in indices:
            visit(node)
    return sorted(result, key=lambda component: (-len(component), component[0]))


def toy_validation() -> None:
    nodes = {"a", "b", "c", "d", "e"}
    graph = {"a": {"b"}, "d": {"e"}, "e": {"d"}}
    assert [len(c) for c in weak_components(nodes, graph)] == [2, 2, 1]
    assert [len(c) for c in strong_components(nodes, graph)] == [2, 1, 1, 1]


def main() -> None:
    toy_validation()
    script = Path(__file__).resolve()
    audit_root = script.parent.parent
    metrics_dir = audit_root / "current_graph" / "metrics"
    authorship_path = metrics_dir / "declaration_origins_and_authorship.csv"
    dependency_path = metrics_dir / "direct_project_dependencies.csv.gz"
    existing_components_path = metrics_dir / "components.csv"

    with authorship_path.open(encoding="utf-8", newline="") as stream:
        authorship_rows = list(csv.DictReader(stream))
    metadata = {row["name"]: row for row in authorship_rows}
    source_written = {
        row["name"]
        for row in authorship_rows
        if row["authorship_class"] == "confirmed_source_written"
    }
    source_written_public = {
        row["name"]
        for row in authorship_rows
        if row["authorship_class"] == "confirmed_source_written"
        and row["is_public"] == "true"
    }
    assert len(source_written) == 49_573
    assert len(source_written_public) == 47_890

    adjacency: dict[str, set[str]] = defaultdict(set)
    induced_edge_count = 0
    with gzip.open(dependency_path, "rt", encoding="utf-8", newline="") as stream:
        for row in csv.DictReader(stream):
            adjacency[row["source"]].add(row["target"])
            if row["source"] in source_written and row["target"] in source_written:
                induced_edge_count += 1

    weak = weak_components(source_written, adjacency)
    strong = strong_components(source_written, adjacency)
    public_weak_validation = weak_components(source_written_public, adjacency)

    existing_rows: list[dict[str, str]]
    with existing_components_path.open(encoding="utf-8", newline="") as stream:
        existing_rows = list(csv.DictReader(stream))
    expected_public_weak = [
        int(row["size"])
        for row in existing_rows
        if row["universe"] == "confirmed_source_written_public"
        and row["component_kind"] == "weak_induced"
    ]
    assert [len(component) for component in public_weak_validation] == expected_public_weak

    weak_membership: dict[str, tuple[int, int]] = {}
    for component_id, component in enumerate(weak):
        for name in component:
            weak_membership[name] = (component_id, len(component))
    strong_membership: dict[str, tuple[int, int]] = {}
    for component_id, component in enumerate(strong):
        for name in component:
            strong_membership[name] = (component_id, len(component))

    membership_path = metrics_dir / "source_written_component_memberships.csv.gz"
    membership_fields = [
        "name",
        "module",
        "kind",
        "is_public",
        "weak_component_id",
        "weak_component_size",
        "strong_component_id",
        "strong_component_size",
        "universe",
        "edge_orientation",
    ]
    gzip_stream = gzip.GzipFile(filename=str(membership_path), mode="wb", mtime=0)
    with io.TextIOWrapper(gzip_stream, encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=membership_fields, lineterminator="\n")
        writer.writeheader()
        for name in sorted(source_written):
            weak_id, weak_size = weak_membership[name]
            strong_id, strong_size = strong_membership[name]
            writer.writerow(
                {
                    "name": name,
                    "module": metadata[name]["module"],
                    "kind": metadata[name]["kind"],
                    "is_public": metadata[name]["is_public"],
                    "weak_component_id": weak_id,
                    "weak_component_size": weak_size,
                    "strong_component_id": strong_id,
                    "strong_component_size": strong_size,
                    "universe": "confirmed_source_written",
                    "edge_orientation": "consumer -> dependency",
                }
            )

    distribution_rows: list[dict[str, object]] = []
    for component_kind, components in (("weak_induced", weak), ("strong_induced", strong)):
        distribution = Counter(map(len, components))
        for size, count in sorted(distribution.items(), reverse=True):
            distribution_rows.append(
                {
                    "universe": "confirmed_source_written",
                    "universe_declarations": len(source_written),
                    "component_kind": component_kind,
                    "component_size": size,
                    "component_count": count,
                    "declarations_covered": size * count,
                    "percent_of_universe": round(
                        100 * size * count / len(source_written), 6
                    ),
                    "edge_filter": "both endpoints have authorship_class=confirmed_source_written",
                    "raw_artifacts": "current_graph/metrics/declaration_origins_and_authorship.csv; current_graph/metrics/direct_project_dependencies.csv.gz",
                    "raw_columns": "name,module,kind,is_public,authorship_class; source,target",
                }
            )
    distribution_path = metrics_dir / "source_written_component_size_distribution.csv"
    with distribution_path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=list(distribution_rows[0]), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(distribution_rows)

    nontrivial_strong = [component for component in strong if len(component) > 1]
    summary = {
        "schema_version": SCHEMA_VERSION,
        "universe": {
            "name": "confirmed_source_written",
            "filter": "authorship_class=confirmed_source_written; public and nonpublic retained",
            "declarations": len(source_written),
        },
        "edge_orientation": "consumer -> dependency",
        "edge_filter": "direct project pair with both endpoints in the named universe",
        "induced_direct_pairs": induced_edge_count,
        "weak_components": {
            "count": len(weak),
            "largest_size": len(weak[0]),
            "largest_coverage_numerator": len(weak[0]),
            "largest_coverage_denominator": len(source_written),
            "largest_coverage_percent": round(
                100 * len(weak[0]) / len(source_written), 6
            ),
            "nontrivial_count": sum(len(component) > 1 for component in weak),
            "singleton_count": sum(len(component) == 1 for component in weak),
        },
        "strong_components": {
            "count": len(strong),
            "largest_size": len(strong[0]),
            "nontrivial_count": len(nontrivial_strong),
            "declarations_in_nontrivial": sum(map(len, nontrivial_strong)),
            "nontrivial_members": nontrivial_strong,
        },
        "interpretation": [
            "Weak connectedness forgets edge direction and is not reuse or usefulness.",
            "Strong components identify directed cycles only within the induced source-written graph.",
            "The authorship classifier is conservative source-origin evidence, not proof of human authorship.",
        ],
        "validation": {
            "toy_weak_and_strong_components_passed": True,
            "source_written_universe_expected_49573": len(source_written) == 49_573,
            "source_written_public_weak_distribution_matches_v2_analyzer": True,
            "membership_rows_cover_universe_exactly": len(weak_membership)
            == len(strong_membership)
            == len(source_written),
        },
        "inputs": {
            "current_graph/metrics/declaration_origins_and_authorship.csv": sha256(
                authorship_path
            ),
            "current_graph/metrics/direct_project_dependencies.csv.gz": sha256(
                dependency_path
            ),
            "current_graph/metrics/components.csv": sha256(existing_components_path),
        },
        "tool": {
            "path": "current_graph/analyze_source_written_components.py",
            "sha256": sha256(script),
        },
        "outputs": {
            "memberships": "current_graph/metrics/source_written_component_memberships.csv.gz",
            "size_distribution": "current_graph/metrics/source_written_component_size_distribution.csv",
            "validation_log": "current_graph/source_written_components_validation.log",
        },
    }
    summary_path = metrics_dir / "source_written_components_summary.json"
    summary_path.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    validation_path = audit_root / "current_graph" / "source_written_components_validation.log"
    validation_path.write_text(
        "\n".join(
            [
                f"schema_version={SCHEMA_VERSION}",
                "command=python3 current_graph/analyze_source_written_components.py",
                "toy_components=PASS",
                f"source_written_nodes={len(source_written)}",
                f"induced_edges={induced_edge_count}",
                f"weak_components={len(weak)}",
                f"largest_weak={len(weak[0])}",
                f"strong_components={len(strong)}",
                f"nontrivial_strong_components={len(nontrivial_strong)}",
                "source_written_public_crosscheck=PASS",
                "all_validations=PASS",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "nodes": len(source_written),
                "induced_edges": induced_edge_count,
                "weak_components": len(weak),
                "largest_weak": len(weak[0]),
                "strong_components": len(strong),
                "nontrivial_strong_components": len(nontrivial_strong),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
