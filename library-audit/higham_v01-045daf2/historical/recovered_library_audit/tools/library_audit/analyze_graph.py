#!/usr/bin/env python3
"""Compute reproducible NumStability metrics from DeclarationGraph.lean CSV output."""

from __future__ import annotations

import argparse
import csv
import json
import sys
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Declaration:
    name: str
    module: str
    kind: str
    is_internal: bool
    is_private: bool
    has_body: bool
    type_direct_count: int
    body_direct_count: int

    @property
    def is_public(self) -> bool:
        return not self.is_internal and not self.is_private


def parse_bool(value: str) -> bool:
    if value == "true":
        return True
    if value == "false":
        return False
    raise ValueError(f"expected true/false, got {value!r}")


def read_declarations(path: Path) -> dict[str, Declaration]:
    result: dict[str, Declaration] = {}
    with path.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            declaration = Declaration(
                name=row["name"],
                module=row["module"],
                kind=row["kind"],
                is_internal=parse_bool(row["is_internal"]),
                is_private=parse_bool(row["is_private"]),
                has_body=parse_bool(row["has_body"]),
                type_direct_count=int(row["type_direct_count"]),
                body_direct_count=int(row["body_direct_count"]),
            )
            result[declaration.name] = declaration
    return result


def read_imports(path: Path) -> set[tuple[str, str]]:
    imports: set[tuple[str, str]] = set()
    with path.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            if row["target_scope"] == "project":
                imports.add((row["source_module"], row["target_module"]))
    return imports


def finish_order(adjacency: list[set[int]]) -> list[int]:
    """Iterative DFS finishing order, avoiding Python recursion limits."""
    seen = bytearray(len(adjacency))
    order: list[int] = []
    for start in range(len(adjacency)):
        if seen[start]:
            continue
        seen[start] = 1
        stack: list[tuple[int, bool]] = [(start, False)]
        while stack:
            node, expanded = stack.pop()
            if expanded:
                order.append(node)
                continue
            stack.append((node, True))
            for target in adjacency[node]:
                if not seen[target]:
                    seen[target] = 1
                    stack.append((target, False))
    return order


def strongly_connected_components(
    adjacency: list[set[int]], reverse: list[set[int]]
) -> tuple[list[int], list[list[int]]]:
    component_of = [-1] * len(adjacency)
    components: list[list[int]] = []
    for start in reversed(finish_order(adjacency)):
        if component_of[start] != -1:
            continue
        component_id = len(components)
        members: list[int] = []
        component_of[start] = component_id
        stack = [start]
        while stack:
            node = stack.pop()
            members.append(node)
            for source in reverse[node]:
                if component_of[source] == -1:
                    component_of[source] = component_id
                    stack.append(source)
        components.append(members)
    return component_of, components


class UnionFind:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))
        self.weight = [1] * size

    def find(self, node: int) -> int:
        root = node
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[node] != node:
            parent = self.parent[node]
            self.parent[node] = root
            node = parent
        return root

    def union(self, left: int, right: int) -> None:
        left_root = self.find(left)
        right_root = self.find(right)
        if left_root == right_root:
            return
        if self.weight[left_root] < self.weight[right_root]:
            left_root, right_root = right_root, left_root
        self.parent[right_root] = left_root
        self.weight[left_root] += self.weight[right_root]


def transitive_project_counts(
    adjacency: list[set[int]], component_of: list[int], components: list[list[int]]
) -> list[int]:
    """Exact reachability counts via SCC condensation and Python integer bitsets."""
    component_edges: list[set[int]] = [set() for _ in components]
    indegree = [0] * len(components)
    for source, targets in enumerate(adjacency):
        source_component = component_of[source]
        for target in targets:
            target_component = component_of[target]
            if source_component == target_component:
                continue
            if target_component not in component_edges[source_component]:
                component_edges[source_component].add(target_component)
                indegree[target_component] += 1

    queue = deque(index for index, degree in enumerate(indegree) if degree == 0)
    topological: list[int] = []
    while queue:
        component = queue.popleft()
        topological.append(component)
        for target in component_edges[component]:
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    if len(topological) != len(components):
        raise RuntimeError("SCC condensation unexpectedly contains a cycle")

    member_bits = [0] * len(components)
    for component, members in enumerate(components):
        bits = 0
        for member in members:
            bits |= 1 << member
        member_bits[component] = bits

    reachable_bits = member_bits.copy()
    for component in reversed(topological):
        bits = reachable_bits[component]
        for target in component_edges[component]:
            bits |= reachable_bits[target]
        reachable_bits[component] = bits

    return [
        reachable_bits[component_of[node]].bit_count() - 1
        for node in range(len(adjacency))
    ]


def dot_escape(value: str) -> str:
    return value.replace("\\", "\\\\").replace('"', '\\"')


def write_module_dot(
    path: Path, graph_name: str, edges: Counter[tuple[str, str]], label: str
) -> None:
    with path.open("w", encoding="utf-8") as handle:
        handle.write(f'digraph "{dot_escape(graph_name)}" {{\n')
        handle.write('  rankdir="LR";\n')
        for (source, target), count in sorted(edges.items()):
            handle.write(
                f'  "{dot_escape(source)}" -> "{dot_escape(target)}" '
                f'[label="{count} {dot_escape(label)}"];\n'
            )
        handle.write("}\n")


def write_import_dot(path: Path, imports: set[tuple[str, str]]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        handle.write('digraph "NumStability direct module imports" {\n')
        handle.write('  rankdir="LR";\n')
        for source, target in sorted(imports):
            handle.write(f'  "{dot_escape(source)}" -> "{dot_escape(target)}";\n')
        handle.write("}\n")


def percent(numerator: int, denominator: int) -> float:
    return round(100.0 * numerator / denominator, 4) if denominator else 0.0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("raw_dir", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    declarations = read_declarations(args.raw_dir / "declarations.csv")
    names = sorted(declarations)
    index_of = {name: index for index, name in enumerate(names)}
    adjacency: list[set[int]] = [set() for _ in names]
    reverse: list[set[int]] = [set() for _ in names]
    direct_scope_counts = [Counter() for _ in names]
    direct_type_project = [0] * len(names)
    direct_body_project = [0] * len(names)
    cross_module_outgoing = [0] * len(names)
    cross_module_incoming = [0] * len(names)
    module_declaration_edges: Counter[tuple[str, str]] = Counter()

    with (args.raw_dir / "direct_dependencies.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        for row in csv.DictReader(handle):
            source_index = index_of.get(row["source"])
            if source_index is None:
                continue
            scope = row["target_scope"]
            direct_scope_counts[source_index][scope] += 1
            if scope != "project":
                continue
            target_index = index_of.get(row["target"])
            if target_index is None:
                direct_scope_counts[source_index]["project_missing_node"] += 1
                continue
            adjacency[source_index].add(target_index)
            reverse[target_index].add(source_index)
            if parse_bool(row["occurs_in_type"]):
                direct_type_project[source_index] += 1
            if parse_bool(row["occurs_in_body"]):
                direct_body_project[source_index] += 1
            if row["source_module"] != row["target_module"]:
                cross_module_outgoing[source_index] += 1
                cross_module_incoming[target_index] += 1
                module_declaration_edges[
                    (row["source_module"], row["target_module"])
                ] += 1

    union_find = UnionFind(len(names))
    for source, targets in enumerate(adjacency):
        for target in targets:
            union_find.union(source, target)
    weak_roots = [union_find.find(node) for node in range(len(names))]
    weak_sizes = Counter(weak_roots)
    weak_ids = {
        root: component_id
        for component_id, (root, _) in enumerate(
            sorted(weak_sizes.items(), key=lambda item: (-item[1], item[0]))
        )
    }

    component_of, strong_components = strongly_connected_components(adjacency, reverse)
    transitive_counts = transitive_project_counts(
        adjacency, component_of, strong_components
    )

    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    metric_fields = [
        "name",
        "module",
        "kind",
        "is_internal",
        "is_private",
        "has_body",
        "direct_type_reference_count_all",
        "direct_body_reference_count_all",
        "direct_project_dependency_count",
        "direct_project_type_dependency_count",
        "direct_project_body_dependency_count",
        "direct_mathlib_dependency_count",
        "direct_other_external_dependency_count",
        "incoming_project_reference_count",
        "cross_module_outgoing_count",
        "cross_module_incoming_count",
        "transitive_project_dependency_count",
        "weak_component",
        "strong_component",
        "is_apparent_leaf",
        "is_project_foundational",
        "is_project_isolated",
        "is_used_outside_module",
    ]
    with (output / "declaration_metrics.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=metric_fields)
        writer.writeheader()
        for node, name in enumerate(names):
            declaration = declarations[name]
            incoming_count = len(reverse[node])
            outgoing_count = len(adjacency[node])
            scopes = direct_scope_counts[node]
            writer.writerow(
                {
                    "name": name,
                    "module": declaration.module,
                    "kind": declaration.kind,
                    "is_internal": str(declaration.is_internal).lower(),
                    "is_private": str(declaration.is_private).lower(),
                    "has_body": str(declaration.has_body).lower(),
                    "direct_type_reference_count_all": declaration.type_direct_count,
                    "direct_body_reference_count_all": declaration.body_direct_count,
                    "direct_project_dependency_count": outgoing_count,
                    "direct_project_type_dependency_count": direct_type_project[node],
                    "direct_project_body_dependency_count": direct_body_project[node],
                    "direct_mathlib_dependency_count": scopes["mathlib"],
                    "direct_other_external_dependency_count": sum(
                        count
                        for scope, count in scopes.items()
                        if scope not in {"project", "mathlib", "project_missing_node"}
                    ),
                    "incoming_project_reference_count": incoming_count,
                    "cross_module_outgoing_count": cross_module_outgoing[node],
                    "cross_module_incoming_count": cross_module_incoming[node],
                    "transitive_project_dependency_count": transitive_counts[node],
                    "weak_component": weak_ids[weak_roots[node]],
                    "strong_component": component_of[node],
                    "is_apparent_leaf": str(incoming_count == 0).lower(),
                    "is_project_foundational": str(outgoing_count == 0).lower(),
                    "is_project_isolated": str(
                        incoming_count == 0 and outgoing_count == 0
                    ).lower(),
                    "is_used_outside_module": str(
                        cross_module_incoming[node] > 0
                    ).lower(),
                }
            )

    module_members: dict[str, list[int]] = defaultdict(list)
    for node, name in enumerate(names):
        module_members[declarations[name].module].append(node)
    module_fields = [
        "module",
        "declaration_count",
        "public_declaration_count",
        "declarations_used_by_project",
        "public_declarations_used_by_project",
        "declarations_used_outside_module",
        "public_declarations_used_outside_module",
        "apparent_leaf_count",
        "public_apparent_leaf_count",
        "isolated_count",
        "public_isolated_count",
        "outside_module_utilization_percent",
        "public_outside_module_utilization_percent",
    ]
    with (output / "module_metrics.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=module_fields)
        writer.writeheader()
        for module, members in sorted(module_members.items()):
            public_members = [
                node for node in members if declarations[names[node]].is_public
            ]
            used = [node for node in members if reverse[node]]
            public_used = [
                node for node in public_members if reverse[node]
            ]
            used_outside = [
                node for node in members if cross_module_incoming[node] > 0
            ]
            public_used_outside = [
                node for node in public_members if cross_module_incoming[node] > 0
            ]
            leaves = [node for node in members if not reverse[node]]
            public_leaves = [node for node in public_members if not reverse[node]]
            isolated = [
                node for node in members if not reverse[node] and not adjacency[node]
            ]
            public_isolated = [
                node
                for node in public_members
                if not reverse[node] and not adjacency[node]
            ]
            writer.writerow(
                {
                    "module": module,
                    "declaration_count": len(members),
                    "public_declaration_count": len(public_members),
                    "declarations_used_by_project": len(used),
                    "public_declarations_used_by_project": len(public_used),
                    "declarations_used_outside_module": len(used_outside),
                    "public_declarations_used_outside_module": len(
                        public_used_outside
                    ),
                    "apparent_leaf_count": len(leaves),
                    "public_apparent_leaf_count": len(public_leaves),
                    "isolated_count": len(isolated),
                    "public_isolated_count": len(public_isolated),
                    "outside_module_utilization_percent": percent(
                        len(used_outside), len(members)
                    ),
                    "public_outside_module_utilization_percent": percent(
                        len(public_used_outside), len(public_members)
                    ),
                }
            )

    with (output / "apparent_leaves.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        fields = [
            "name",
            "module",
            "kind",
            "is_public",
            "direct_project_dependency_count",
            "transitive_project_dependency_count",
            "is_isolated",
            "classification",
            "review_notes",
        ]
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for node, name in enumerate(names):
            if reverse[node]:
                continue
            declaration = declarations[name]
            writer.writerow(
                {
                    "name": name,
                    "module": declaration.module,
                    "kind": declaration.kind,
                    "is_public": str(declaration.is_public).lower(),
                    "direct_project_dependency_count": len(adjacency[node]),
                    "transitive_project_dependency_count": transitive_counts[node],
                    "is_isolated": str(not adjacency[node]).lower(),
                    "classification": "unreviewed",
                    "review_notes": "",
                }
            )

    imports = read_imports(args.raw_dir / "module_imports.csv")
    compiled_project_modules = set(module_members)
    for source_module, target_module in imports:
        compiled_project_modules.add(source_module)
        compiled_project_modules.add(target_module)
    declaration_module_pairs = set(module_declaration_edges)
    comparison_fields = [
        "source_module",
        "target_module",
        "is_direct_import",
        "has_direct_declaration_reference",
        "direct_declaration_edge_count",
        "interpretation",
    ]
    with (output / "module_dependency_comparison.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=comparison_fields)
        writer.writeheader()
        for source, target in sorted(imports | declaration_module_pairs):
            is_import = (source, target) in imports
            has_reference = (source, target) in declaration_module_pairs
            if is_import and has_reference:
                interpretation = "direct import with direct declaration use"
            elif is_import:
                interpretation = "direct import without direct declaration use"
            else:
                interpretation = "declaration use supplied through transitive import"
            writer.writerow(
                {
                    "source_module": source,
                    "target_module": target,
                    "is_direct_import": str(is_import).lower(),
                    "has_direct_declaration_reference": str(has_reference).lower(),
                    "direct_declaration_edge_count": module_declaration_edges[
                        (source, target)
                    ],
                    "interpretation": interpretation,
                }
            )

    write_module_dot(
        output / "module_declaration_graph.dot",
        "NumStability declaration-derived module graph",
        module_declaration_edges,
        "declaration edges",
    )
    write_import_dot(output / "module_import_graph.dot", imports)

    public_nodes = [
        node for node, name in enumerate(names) if declarations[name].is_public
    ]
    main_weak_size = max(weak_sizes.values(), default=0)
    main_weak_root = (
        max(weak_sizes, key=weak_sizes.get) if weak_sizes else None
    )
    public_in_main = sum(
        1 for node in public_nodes if weak_roots[node] == main_weak_root
    )
    apparent_leaves = sum(1 for incoming in reverse if not incoming)
    public_apparent_leaves = sum(1 for node in public_nodes if not reverse[node])
    declarations_used_by_project = sum(1 for incoming in reverse if incoming)
    public_declarations_used_by_project = sum(
        1 for node in public_nodes if reverse[node]
    )
    declarations_used_outside_module = sum(
        1 for count in cross_module_incoming if count > 0
    )
    public_declarations_used_outside_module = sum(
        1 for node in public_nodes if cross_module_incoming[node] > 0
    )
    isolated = sum(
        1
        for node in range(len(names))
        if not reverse[node] and not adjacency[node]
    )
    public_isolated = sum(
        1 for node in public_nodes if not reverse[node] and not adjacency[node]
    )
    summary = {
        "schema_version": 1,
        "edge_direction": "A -> B means declaration A directly depends on declaration B",
        "counts": {
            "declarations": len(names),
            "public_declarations": len(public_nodes),
            "project_direct_edges": sum(map(len, adjacency)),
            "cross_module_declaration_edges": sum(module_declaration_edges.values()),
            "project_modules_with_declarations": len(module_members),
            "project_modules_in_compiled_graph": len(compiled_project_modules),
            "direct_project_import_edges": len(imports),
            "weak_components": len(weak_sizes),
            "strong_components": len(strong_components),
            "apparent_leaves": apparent_leaves,
            "public_apparent_leaves": public_apparent_leaves,
            "declarations_used_by_project": declarations_used_by_project,
            "public_declarations_used_by_project": public_declarations_used_by_project,
            "declarations_used_outside_module": declarations_used_outside_module,
            "public_declarations_used_outside_module": public_declarations_used_outside_module,
            "isolated_declarations": isolated,
            "public_isolated_declarations": public_isolated,
        },
        "connected_component_coverage": {
            "largest_weak_component_declarations": main_weak_size,
            "largest_weak_component_percent": percent(main_weak_size, len(names)),
            "public_declarations_in_largest_weak_component": public_in_main,
            "public_largest_weak_component_percent": percent(
                public_in_main, len(public_nodes)
            ),
        },
        "usage_rates": {
            "declarations_with_any_incoming_project_reference_percent": percent(
                declarations_used_by_project, len(names)
            ),
            "public_declarations_with_any_incoming_project_reference_percent": percent(
                public_declarations_used_by_project, len(public_nodes)
            ),
            "declarations_used_outside_their_module_percent": percent(
                declarations_used_outside_module, len(names)
            ),
            "public_declarations_used_outside_their_module_percent": percent(
                public_declarations_used_outside_module, len(public_nodes)
            ),
        },
        "module_import_vs_declaration_use": {
            "direct_imports_without_direct_declaration_use": len(
                imports - declaration_module_pairs
            ),
            "declaration_module_pairs_without_direct_import": len(
                declaration_module_pairs - imports
            ),
        },
        "limitations": [
            "No incoming project edge means unused by declarations in this build, not necessarily redundant or unsuitable as a public endpoint.",
            "The logical declaration graph does not record syntax, macro, tactic, attribute, or other elaboration-only dependencies.",
            "Generated, internal, and private declarations are retained and separately labelled.",
            "Duplicate or near-duplicate semantics require a separate statement-normalization analysis and human review.",
            "Transitive counts are exact for NumStability declarations reachable through the exported direct project graph; external transitive closure is not materialized.",
        ],
    }
    (output / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
