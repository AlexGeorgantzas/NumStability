#!/usr/bin/env python3
"""Reproducible elaborated-graph metrics for the higham_v01 architecture audit.

Schema: numstability-elaborated-architecture/2.1.0

The declaration-edge orientation is consumer to dependency: ``A -> B`` means
that A directly references B in its elaborated type or body/proof.  This script
uses only Python's standard library and accepts both plain and gzip-compressed
CSV inputs.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
import math
import re
import statistics
import sys
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, TextIO


SCHEMA_VERSION = "numstability-elaborated-architecture/2.1.0"
EDGE_DIRECTION = (
    "consumer -> dependency; A -> B means A directly references B in its "
    "elaborated type or body/proof"
)
PERCENTILES = (0.0, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99, 1.0)
LAYER_RANK = {
    "FloatingPoint": 0,
    "Analysis": 1,
    "Algorithms": 2,
    "Source": 3,
    "Examples": 4,
}


@dataclass(frozen=True)
class Decl:
    name: str
    module: str
    kind: str
    is_internal: bool
    is_private: bool
    has_body: bool
    type_direct_count_all: int
    body_direct_count_all: int

    @property
    def is_public(self) -> bool:
        return not self.is_internal and not self.is_private


@dataclass(frozen=True)
class ModuleInfo:
    module: str
    source_path: str
    physical_layer: str
    effective_layer: str
    chapter: str
    domain: str
    physical_lines: int
    code_lines: int
    static_declaration_starters: int


@dataclass(frozen=True)
class Metadata:
    reserved: bool
    unsafe: bool
    partial: bool
    instance: bool
    structure: bool
    class_: bool
    reducibility_kind: str
    documented: bool
    selection_start_line: int | None
    selection_start_column: int | None
    selection_end_line: int | None
    selection_end_column: int | None


@dataclass(frozen=True)
class Edge:
    source: int
    target: int
    in_type: bool
    in_body: bool


def parse_bool(value: str) -> bool:
    if value == "true":
        return True
    if value == "false":
        return False
    raise ValueError(f"expected true/false, got {value!r}")


def optional_int(value: str) -> int | None:
    return int(value) if value else None


def open_text(path: Path, mode: str = "rt") -> TextIO:
    if path.suffix == ".gz":
        return gzip.open(path, mode, newline="", encoding="utf-8")  # type: ignore[return-value]
    return path.open(mode.replace("t", ""), newline="", encoding="utf-8")


def gzip_csv_writer(path: Path, fieldnames: list[str]):
    handle = gzip.open(path, "wt", newline="", encoding="utf-8", compresslevel=9)
    writer = csv.DictWriter(handle, fieldnames=fieldnames)
    writer.writeheader()
    return handle, writer


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def layer_for_module(module: str, modules: dict[str, ModuleInfo]) -> str:
    if module in modules:
        value = modules[module].effective_layer
        if value and value not in {"Other", "Upstream"}:
            return value
    for layer in ("Examples", "Source", "Algorithms", "Analysis", "FloatingPoint"):
        if module == f"NumStability.{layer}" or module.startswith(
            f"NumStability.{layer}."
        ):
            return layer
    return "Root"


def chapter_for_module(module: str, modules: dict[str, ModuleInfo]) -> str:
    if module in modules and modules[module].chapter:
        raw = modules[module].chapter
        match = re.search(r"(\d{1,2})", raw)
        if match:
            return f"Chapter{int(match.group(1)):02d}"
    match = re.search(r"(?:^|\.)Chapter(\d{2})(?:\.|$)", module)
    return f"Chapter{match.group(1)}" if match else "Unassigned"


def domain_for_module(module: str, modules: dict[str, ModuleInfo]) -> str:
    if module in modules and modules[module].domain:
        return modules[module].domain
    return "Other"


def top_namespace(name: str) -> str:
    parts = name.split(".")
    return parts[1] if len(parts) > 2 and parts[0] == "NumStability" else parts[0]


def nearest_rank(values: list[int], q: float) -> int:
    """Nearest-rank percentile: sorted[ceil(q*n)-1], with q=0 selecting min."""
    if not values:
        return 0
    ordered = sorted(values)
    if q <= 0:
        return ordered[0]
    return ordered[min(len(ordered) - 1, math.ceil(q * len(ordered)) - 1)]


def distribution(values: list[int]) -> dict[str, float | int]:
    return {
        "count": len(values),
        "mean": round(statistics.fmean(values), 6) if values else 0.0,
        **{f"p{int(q * 100):02d}": nearest_rank(values, q) for q in PERCENTILES},
    }


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
        left, right = self.find(left), self.find(right)
        if left == right:
            return
        if self.weight[left] < self.weight[right]:
            left, right = right, left
        self.parent[right] = left
        self.weight[left] += self.weight[right]


def weak_components(
    node_count: int,
    edges: Iterable[tuple[int, int]],
    included: set[int],
    names: list[str],
) -> tuple[list[int | None], list[list[int]]]:
    uf = UnionFind(node_count)
    for source, target in edges:
        if source in included and target in included:
            uf.union(source, target)
    groups: dict[int, list[int]] = defaultdict(list)
    for node in included:
        groups[uf.find(node)].append(node)
    components = sorted(
        groups.values(), key=lambda members: (-len(members), min(names[n] for n in members))
    )
    component_of: list[int | None] = [None] * node_count
    for component_id, members in enumerate(components):
        for node in members:
            component_of[node] = component_id
    return component_of, components


def finishing_order(adjacency: list[set[int]]) -> list[int]:
    seen = bytearray(len(adjacency))
    order: list[int] = []
    for start in range(len(adjacency)):
        if seen[start]:
            continue
        seen[start] = 1
        stack: list[tuple[int, Iterator[int]]] = [(start, iter(adjacency[start]))]
        while stack:
            node, targets = stack[-1]
            try:
                target = next(targets)
            except StopIteration:
                stack.pop()
                order.append(node)
                continue
            if not seen[target]:
                seen[target] = 1
                stack.append((target, iter(adjacency[target])))
    return order


def strongly_connected_components(
    adjacency: list[set[int]], reverse: list[set[int]], names: list[str]
) -> tuple[list[int], list[list[int]]]:
    raw_of = [-1] * len(adjacency)
    raw_components: list[list[int]] = []
    for start in reversed(finishing_order(adjacency)):
        if raw_of[start] != -1:
            continue
        cid = len(raw_components)
        raw_of[start] = cid
        members: list[int] = []
        stack = [start]
        while stack:
            node = stack.pop()
            members.append(node)
            for source in reverse[node]:
                if raw_of[source] == -1:
                    raw_of[source] = cid
                    stack.append(source)
        raw_components.append(members)
    order = sorted(
        range(len(raw_components)),
        key=lambda cid: (-len(raw_components[cid]), min(names[n] for n in raw_components[cid])),
    )
    remap = {old: new for new, old in enumerate(order)}
    components = [raw_components[old] for old in order]
    return [remap[cid] for cid in raw_of], components


def condensation(
    adjacency: list[set[int]], component_of: list[int], component_count: int
) -> tuple[list[set[int]], list[set[int]], list[int]]:
    dag = [set() for _ in range(component_count)]
    rev = [set() for _ in range(component_count)]
    indegree = [0] * component_count
    for source, targets in enumerate(adjacency):
        source_component = component_of[source]
        for target in targets:
            target_component = component_of[target]
            if source_component == target_component or target_component in dag[source_component]:
                continue
            dag[source_component].add(target_component)
            rev[target_component].add(source_component)
            indegree[target_component] += 1
    queue = deque(index for index, degree in enumerate(indegree) if degree == 0)
    topo: list[int] = []
    while queue:
        component = queue.popleft()
        topo.append(component)
        for target in dag[component]:
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    if len(topo) != component_count:
        raise RuntimeError("SCC condensation unexpectedly cyclic")
    return dag, rev, topo


def transitive_component_counts(
    graph: list[set[int]], topo: list[int], components: list[list[int]]
) -> list[int]:
    """Exact declaration-weighted reachability on a DAG using integer bitsets."""
    member_bits = [
        sum(1 << member for member in members) for members in components
    ]
    reach = member_bits.copy()
    for component in reversed(topo):
        bits = reach[component]
        for target in graph[component]:
            bits |= reach[target]
        reach[component] = bits
    return [bits.bit_count() - 1 for bits in reach]


def reverse_transitive_component_counts(
    reverse_graph: list[set[int]], topo_original: list[int], components: list[list[int]]
) -> list[int]:
    """Exact declaration-weighted consumer reachability (reverse closure)."""
    member_bits = [
        sum(1 << member for member in members) for members in components
    ]
    reach = member_bits.copy()
    # Original topological order lists consumers before their dependencies.
    for component in topo_original:
        bits = reach[component]
        for consumer in reverse_graph[component]:
            bits |= reach[consumer]
        reach[component] = bits
    return [bits.bit_count() - 1 for bits in reach]


def depths(
    dag: list[set[int]], reverse: list[set[int]], topo: list[int]
) -> tuple[list[int], list[int], list[int | None]]:
    dependency_depth = [0] * len(dag)
    next_dependency: list[int | None] = [None] * len(dag)
    for component in reversed(topo):
        if dag[component]:
            # Prefer the lowest stable component id when depths tie so the
            # representative longest path does not depend on set iteration.
            best = min(
                dag[component],
                key=lambda target: (-dependency_depth[target], target),
            )
            dependency_depth[component] = dependency_depth[best] + 1
            next_dependency[component] = best
    downstream_depth = [0] * len(dag)
    for component in topo:
        if reverse[component]:
            downstream_depth[component] = 1 + max(
                downstream_depth[consumer] for consumer in reverse[component]
            )
    return dependency_depth, downstream_depth, next_dependency


def category_downstream_masks(
    reverse_dag: list[set[int]],
    topo: list[int],
    member_categories: list[set[str]],
) -> tuple[list[int], dict[str, int]]:
    categories = sorted({value for values in member_categories for value in values})
    index = {value: idx for idx, value in enumerate(categories)}
    own = [sum(1 << index[value] for value in values) for values in member_categories]
    masks = [0] * len(reverse_dag)
    for component in topo:
        mask = 0
        for consumer in reverse_dag[component]:
            mask |= own[consumer] | masks[consumer]
        masks[component] = mask
    return masks, index


def mask_values(mask: int, index: dict[str, int]) -> list[str]:
    return [value for value, position in index.items() if (mask >> position) & 1]


def read_declarations(path: Path) -> tuple[list[str], dict[str, Decl]]:
    declarations: dict[str, Decl] = {}
    with open_text(path) as handle:
        for row in csv.DictReader(handle):
            decl = Decl(
                row["name"],
                row["module"],
                row["kind"],
                parse_bool(row["is_internal"]),
                parse_bool(row["is_private"]),
                parse_bool(row["has_body"]),
                int(row["type_direct_count"]),
                int(row["body_direct_count"]),
            )
            if decl.name in declarations:
                raise ValueError(f"duplicate declaration row: {decl.name}")
            declarations[decl.name] = decl
    names = sorted(declarations)
    return names, declarations


def read_modules(path: Path) -> dict[str, ModuleInfo]:
    result: dict[str, ModuleInfo] = {}
    with path.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            result[row["module"]] = ModuleInfo(
                module=row["module"],
                source_path=row["source_path"],
                physical_layer=row["physical_layer"],
                effective_layer=row["effective_architectural_layer"],
                chapter=row["chapter_guess"],
                domain=row["domain_guess"],
                physical_lines=int(row["physical_lines"]),
                code_lines=int(row["code_bearing_lines"]),
                static_declaration_starters=int(row["static_declaration_starter_count"]),
            )
    return result


def read_metadata(path: Path) -> dict[str, Metadata]:
    result: dict[str, Metadata] = {}
    with open_text(path) as handle:
        for row in csv.DictReader(handle):
            result[row["name"]] = Metadata(
                reserved=parse_bool(row["is_reserved_name"]),
                unsafe=parse_bool(row["is_unsafe"]),
                partial=parse_bool(row["is_partial"]),
                instance=parse_bool(row["is_instance"]),
                structure=parse_bool(row["is_structure"]),
                class_=parse_bool(row["is_class"]),
                reducibility_kind=row["reducibility_kind"],
                documented=parse_bool(row["has_docstring"]),
                selection_start_line=optional_int(row["selection_start_line"]),
                selection_start_column=optional_int(row["selection_start_column"]),
                selection_end_line=optional_int(row["selection_end_line"]),
                selection_end_column=optional_int(row["selection_end_column"]),
            )
    return result


def source_token(
    decl: Decl,
    metadata: Metadata,
    modules: dict[str, ModuleInfo],
    worktree: Path,
    source_cache: dict[Path, list[str]],
) -> str:
    info = modules.get(decl.module)
    if (
        info is None
        or metadata.selection_start_line is None
        or metadata.selection_end_line is None
        or metadata.selection_start_column is None
        or metadata.selection_end_column is None
    ):
        return ""
    path = worktree / info.source_path
    try:
        if path not in source_cache:
            source_cache[path] = path.read_text(encoding="utf-8").splitlines()
        lines = source_cache[path]
        if metadata.selection_start_line != metadata.selection_end_line:
            return ""
        line = lines[metadata.selection_start_line - 1]
        return line[
            metadata.selection_start_column : metadata.selection_end_column
        ].strip().strip("`")
    except (OSError, IndexError):
        return ""


def authorship_class(
    decl: Decl,
    metadata: Metadata,
    token: str,
    static_names_in_module: dict[str, Counter[str]],
) -> str:
    terminal = decl.name.rsplit(".", 1)[-1]
    if metadata.reserved:
        return "lean_reserved_generated"
    if token and (token == terminal or decl.name.endswith("." + token)):
        return "confirmed_source_written"
    if token:
        return "range_present_token_mismatch_generated_or_unresolved"
    if decl.kind == "recursor":
        return "generated_kind_no_direct_range"
    if decl.is_internal:
        return "internal_no_direct_range"
    if static_names_in_module[decl.module][terminal] == 1:
        return "likely_source_written_unique_static_name"
    return "unresolved_no_direct_range"


def read_static_names(path: Path) -> dict[str, Counter[str]]:
    result: dict[str, Counter[str]] = defaultdict(Counter)
    with path.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            result[row["module"]][row["name_guess"]] += 1
    return result


def refined_kind(decl: Decl, metadata: Metadata) -> str:
    """Mutually exclusive reporting category built from Lean environment metadata."""
    if metadata.instance:
        return "instance"
    if metadata.class_:
        return "class"
    if metadata.structure:
        return "structure"
    if metadata.reducibility_kind == "abbrev":
        return "abbreviation"
    return decl.kind


def module_import_closure(imports: set[tuple[str, str]]) -> dict[str, set[str]]:
    adjacency: dict[str, set[str]] = defaultdict(set)
    nodes: set[str] = set()
    for source, target in imports:
        adjacency[source].add(target)
        nodes.update((source, target))
    cache: dict[str, set[str]] = {}
    visiting: set[str] = set()

    def visit(node: str) -> set[str]:
        if node in cache:
            return cache[node]
        if node in visiting:
            # Compiled Lean module imports should be acyclic; handled separately.
            return set()
        visiting.add(node)
        reached: set[str] = set()
        for target in adjacency[node]:
            reached.add(target)
            reached.update(visit(target))
        visiting.remove(node)
        cache[node] = reached
        return reached

    for node in nodes:
        visit(node)
    return cache


def named_graph_sccs(edges: set[tuple[str, str]]) -> list[list[str]]:
    nodes = sorted({value for edge in edges for value in edge})
    index = {name: idx for idx, name in enumerate(nodes)}
    adjacency = [set() for _ in nodes]
    reverse = [set() for _ in nodes]
    for source, target in edges:
        adjacency[index[source]].add(index[target])
        reverse[index[target]].add(index[source])
    _, components = strongly_connected_components(adjacency, reverse, nodes)
    return [[nodes[node] for node in members] for members in components]


def pct(numerator: int, denominator: int) -> float:
    return round(100 * numerator / denominator, 6) if denominator else 0.0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--declarations", type=Path, required=True)
    parser.add_argument("--dependencies", type=Path, required=True)
    parser.add_argument("--imports", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    parser.add_argument("--origins", type=Path, required=True)
    parser.add_argument("--modules", type=Path, required=True)
    parser.add_argument("--static-declarations", type=Path, required=True)
    parser.add_argument("--entry-points", type=Path, required=True)
    parser.add_argument("--worktree", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    if not re.fullmatch(r"[0-9a-f]{40}", args.source_commit):
        raise ValueError("--source-commit must be a lowercase 40-hex Git object id")

    output: Path = args.output
    output.mkdir(parents=True, exist_ok=True)
    names, declarations_by_name = read_declarations(args.declarations)
    declarations = [declarations_by_name[name] for name in names]
    index_of = {name: index for index, name in enumerate(names)}
    modules = read_modules(args.modules)
    metadata_by_name = read_metadata(args.metadata)
    static_names = read_static_names(args.static_declarations)

    if set(metadata_by_name) != set(names):
        raise ValueError("metadata declaration universe differs from graph universe")
    with open_text(args.origins) as handle:
        origins = {row["name"]: row for row in csv.DictReader(handle)}
    if set(origins) != set(names):
        raise ValueError("origin declaration universe differs from graph universe")
    for name in names:
        if parse_bool(origins[name]["is_reserved_name"]) != metadata_by_name[name].reserved:
            raise ValueError(f"reserved-name extractors disagree for {name}")

    layers = [layer_for_module(decl.module, modules) for decl in declarations]
    domains = [domain_for_module(decl.module, modules) for decl in declarations]
    chapters = [chapter_for_module(decl.module, modules) for decl in declarations]
    namespaces = [top_namespace(decl.name) for decl in declarations]
    source_cache: dict[Path, list[str]] = {}
    source_tokens = [
        source_token(
            decl, metadata_by_name[decl.name], modules, args.worktree, source_cache
        )
        for decl in declarations
    ]
    authorship = [
        authorship_class(
            decl, metadata_by_name[decl.name], source_tokens[index], static_names
        )
        for index, decl in enumerate(declarations)
    ]

    node_count = len(names)
    adjacency = [set() for _ in names]
    reverse = [set() for _ in names]
    edges: list[Edge] = []
    all_scope_out = [Counter() for _ in names]
    duplicate_project_rows = 0
    missing_project_targets = 0
    seen_pairs: set[tuple[int, int]] = set()
    edge_fields = [
        "source",
        "source_module",
        "source_layer",
        "source_domain",
        "source_chapter",
        "target",
        "target_module",
        "target_layer",
        "target_domain",
        "target_chapter",
        "occurs_in_type",
        "occurs_in_body",
        "edge_class",
        "same_module",
        "cross_namespace",
        "cross_layer",
        "against_intended_layer_direction",
        "cross_domain",
        "cross_chapter",
        "raw_artifact",
    ]
    project_handle, project_writer = gzip_csv_writer(
        output / "direct_project_dependencies.csv.gz", edge_fields
    )
    type_handle, type_writer = gzip_csv_writer(
        output / "type_project_dependencies.csv.gz", edge_fields
    )
    body_handle, body_writer = gzip_csv_writer(
        output / "body_project_dependencies.csv.gz", edge_fields
    )
    both_handle, both_writer = gzip_csv_writer(
        output / "type_and_body_project_dependencies.csv.gz", edge_fields
    )
    try:
        with open_text(args.dependencies) as handle:
            for row in csv.DictReader(handle):
                source = index_of.get(row["source"])
                if source is None:
                    continue
                scope = row["target_scope"]
                all_scope_out[source][scope] += 1
                if scope != "project":
                    continue
                target = index_of.get(row["target"])
                if target is None:
                    missing_project_targets += 1
                    continue
                pair = (source, target)
                if pair in seen_pairs:
                    duplicate_project_rows += 1
                    continue
                seen_pairs.add(pair)
                in_type = parse_bool(row["occurs_in_type"])
                in_body = parse_bool(row["occurs_in_body"])
                edge = Edge(source, target, in_type, in_body)
                edges.append(edge)
                adjacency[source].add(target)
                reverse[target].add(source)
                source_layer, target_layer = layers[source], layers[target]
                same_module = declarations[source].module == declarations[target].module
                against_direction = (
                    source_layer in LAYER_RANK
                    and target_layer in LAYER_RANK
                    and LAYER_RANK[source_layer] < LAYER_RANK[target_layer]
                )
                edge_class = (
                    "both" if in_type and in_body else "type" if in_type else "body"
                )
                outrow = {
                    "source": names[source],
                    "source_module": declarations[source].module,
                    "source_layer": source_layer,
                    "source_domain": domains[source],
                    "source_chapter": chapters[source],
                    "target": names[target],
                    "target_module": declarations[target].module,
                    "target_layer": target_layer,
                    "target_domain": domains[target],
                    "target_chapter": chapters[target],
                    "occurs_in_type": str(in_type).lower(),
                    "occurs_in_body": str(in_body).lower(),
                    "edge_class": edge_class,
                    "same_module": str(same_module).lower(),
                    "cross_namespace": str(namespaces[source] != namespaces[target]).lower(),
                    "cross_layer": str(source_layer != target_layer).lower(),
                    "against_intended_layer_direction": str(against_direction).lower(),
                    "cross_domain": str(domains[source] != domains[target]).lower(),
                    "cross_chapter": str(
                        chapters[source] != "Unassigned"
                        and chapters[target] != "Unassigned"
                        and chapters[source] != chapters[target]
                    ).lower(),
                    "raw_artifact": str(args.dependencies),
                }
                project_writer.writerow(outrow)
                if in_type:
                    type_writer.writerow(outrow)
                if in_body:
                    body_writer.writerow(outrow)
                if in_type and in_body:
                    both_writer.writerow(outrow)
    finally:
        project_handle.close()
        type_handle.close()
        body_handle.close()
        both_handle.close()

    if duplicate_project_rows:
        raise ValueError(f"raw graph has {duplicate_project_rows} duplicate project pairs")
    if missing_project_targets:
        raise ValueError(f"raw graph has {missing_project_targets} missing project targets")

    public_nodes = {i for i, decl in enumerate(declarations) if decl.is_public}
    confirmed_nodes = {
        i for i, value in enumerate(authorship) if value == "confirmed_source_written"
    }
    confirmed_public_nodes = public_nodes & confirmed_nodes
    universes = {
        "all_project_environment": set(range(node_count)),
        "environment_public": public_nodes,
        "confirmed_source_written_public": confirmed_public_nodes,
    }

    edge_pairs = [(edge.source, edge.target) for edge in edges]
    weak_assignments: dict[str, list[int | None]] = {}
    weak_component_lists: dict[str, list[list[int]]] = {}
    for universe, included in universes.items():
        assignments, components = weak_components(node_count, edge_pairs, included, names)
        weak_assignments[universe] = assignments
        weak_component_lists[universe] = components

    strong_of, strong_components = strongly_connected_components(adjacency, reverse, names)
    dag, reverse_dag, topo = condensation(adjacency, strong_of, len(strong_components))
    component_sizes = [len(component) for component in strong_components]
    transitive_dependency_by_component = transitive_component_counts(
        dag, topo, strong_components
    )
    transitive_consumer_by_component = reverse_transitive_component_counts(
        reverse_dag, topo, strong_components
    )
    dependency_depth_by_component, downstream_depth_by_component, next_component = depths(
        dag, reverse_dag, topo
    )

    member_layers = [set() for _ in strong_components]
    member_domains = [set() for _ in strong_components]
    member_chapters = [set() for _ in strong_components]
    member_modules = [set() for _ in strong_components]
    for node in range(node_count):
        component = strong_of[node]
        member_layers[component].add(layers[node])
        member_domains[component].add(domains[node])
        member_chapters[component].add(chapters[node])
        member_modules[component].add(declarations[node].module)
    downstream_layer_masks, layer_index = category_downstream_masks(
        reverse_dag, topo, member_layers
    )
    downstream_domain_masks, domain_index = category_downstream_masks(
        reverse_dag, topo, member_domains
    )
    downstream_chapter_masks, chapter_index = category_downstream_masks(
        reverse_dag, topo, member_chapters
    )
    downstream_module_masks, module_index = category_downstream_masks(
        reverse_dag, topo, member_modules
    )

    direct_consumer_modules = [set() for _ in names]
    direct_consumer_layers = [set() for _ in names]
    direct_consumer_domains = [set() for _ in names]
    direct_consumer_chapters = [set() for _ in names]
    cross_module_outgoing = [0] * node_count
    for edge in edges:
        consumer, dependency = edge.source, edge.target
        direct_consumer_modules[dependency].add(declarations[consumer].module)
        direct_consumer_layers[dependency].add(layers[consumer])
        direct_consumer_domains[dependency].add(domains[consumer])
        direct_consumer_chapters[dependency].add(chapters[consumer])
        if declarations[consumer].module != declarations[dependency].module:
            cross_module_outgoing[consumer] += 1

    declaration_fields = [
        "name",
        "module",
        "source_path",
        "source_line",
        "source_token",
        "kind",
        "refined_kind",
        "layer",
        "domain",
        "chapter",
        "top_namespace",
        "is_public",
        "is_private",
        "is_internal",
        "is_reserved_name",
        "authorship_class",
        "is_confirmed_source_written",
        "has_body",
        "is_unsafe",
        "is_partial",
        "is_instance",
        "is_structure",
        "is_class",
        "reducibility_kind",
        "has_docstring",
        "direct_project_dependency_count",
        "direct_project_type_dependency_count",
        "direct_project_body_dependency_count",
        "direct_project_both_dependency_count",
        "direct_project_consumer_count",
        "direct_consumer_module_count",
        "direct_consumer_layer_count",
        "direct_consumer_domain_count",
        "direct_consumer_chapter_count",
        "used_by_different_module",
        "used_by_different_layer",
        "used_by_multiple_modules",
        "used_by_multiple_domains",
        "transitive_project_dependency_count",
        "transitive_downstream_consumer_count",
        "transitive_downstream_module_count",
        "transitive_downstream_layer_count",
        "transitive_downstream_layers",
        "transitive_downstream_domain_count",
        "transitive_downstream_domains",
        "transitive_downstream_chapter_count",
        "transitive_downstream_chapters",
        "dependency_depth_scc_condensation",
        "downstream_depth_scc_condensation",
        "weak_component_all",
        "weak_component_public_induced",
        "weak_component_confirmed_source_written_public_induced",
        "strong_component_all",
        "strong_component_size",
        "no_incoming_project_edge",
        "no_outgoing_project_edge",
        "isolated_in_project_graph",
        "direct_mathlib_dependency_count",
        "direct_other_external_dependency_count",
        "raw_declaration_artifact",
        "raw_dependency_artifact",
    ]
    decl_path = output / "declaration_metrics.csv.gz"
    decl_handle, decl_writer = gzip_csv_writer(decl_path, declaration_fields)
    authorship_counter: Counter[str] = Counter()
    kind_counter: Counter[str] = Counter()
    refined_kind_counter: Counter[str] = Counter()
    layer_counter: Counter[str] = Counter()
    domain_counter: Counter[str] = Counter()
    chapter_counter: Counter[str] = Counter()
    namespace_counter: Counter[str] = Counter()
    try:
        for node, decl in enumerate(declarations):
            meta = metadata_by_name[decl.name]
            info = modules.get(decl.module)
            component = strong_of[node]
            authorship_counter[authorship[node]] += 1
            kind_counter[decl.kind] += 1
            refined_kind_counter[refined_kind(decl, meta)] += 1
            layer_counter[layers[node]] += 1
            domain_counter[domains[node]] += 1
            chapter_counter[chapters[node]] += 1
            namespace_counter[namespaces[node]] += 1
            # Type/body counts are populated by the deterministic rewrite below.
            row = {
                "name": decl.name,
                "module": decl.module,
                "source_path": info.source_path if info else "",
                "source_line": meta.selection_start_line or "",
                "source_token": source_tokens[node],
                "kind": decl.kind,
                "refined_kind": refined_kind(decl, meta),
                "layer": layers[node],
                "domain": domains[node],
                "chapter": chapters[node],
                "top_namespace": namespaces[node],
                "is_public": str(decl.is_public).lower(),
                "is_private": str(decl.is_private).lower(),
                "is_internal": str(decl.is_internal).lower(),
                "is_reserved_name": str(meta.reserved).lower(),
                "authorship_class": authorship[node],
                "is_confirmed_source_written": str(node in confirmed_nodes).lower(),
                "has_body": str(decl.has_body).lower(),
                "is_unsafe": str(meta.unsafe).lower(),
                "is_partial": str(meta.partial).lower(),
                "is_instance": str(meta.instance).lower(),
                "is_structure": str(meta.structure).lower(),
                "is_class": str(meta.class_).lower(),
                "reducibility_kind": meta.reducibility_kind,
                "has_docstring": str(meta.documented).lower(),
                "direct_project_dependency_count": len(adjacency[node]),
                "direct_project_type_dependency_count": 0,
                "direct_project_body_dependency_count": 0,
                "direct_project_both_dependency_count": 0,
                "direct_project_consumer_count": len(reverse[node]),
                "direct_consumer_module_count": len(direct_consumer_modules[node]),
                "direct_consumer_layer_count": len(direct_consumer_layers[node]),
                "direct_consumer_domain_count": len(direct_consumer_domains[node]),
                "direct_consumer_chapter_count": len(direct_consumer_chapters[node]),
                "used_by_different_module": str(any(
                    declarations[c].module != decl.module for c in reverse[node]
                )).lower(),
                "used_by_different_layer": str(any(
                    layers[c] != layers[node] for c in reverse[node]
                )).lower(),
                "used_by_multiple_modules": str(len(direct_consumer_modules[node]) >= 2).lower(),
                "used_by_multiple_domains": str(len(direct_consumer_domains[node]) >= 2).lower(),
                "transitive_project_dependency_count": transitive_dependency_by_component[component],
                "transitive_downstream_consumer_count": transitive_consumer_by_component[component],
                "transitive_downstream_module_count": downstream_module_masks[component].bit_count(),
                "transitive_downstream_layer_count": downstream_layer_masks[component].bit_count(),
                "transitive_downstream_layers": ";".join(mask_values(downstream_layer_masks[component], layer_index)),
                "transitive_downstream_domain_count": downstream_domain_masks[component].bit_count(),
                "transitive_downstream_domains": ";".join(mask_values(downstream_domain_masks[component], domain_index)),
                "transitive_downstream_chapter_count": downstream_chapter_masks[component].bit_count(),
                "transitive_downstream_chapters": ";".join(mask_values(downstream_chapter_masks[component], chapter_index)),
                "dependency_depth_scc_condensation": dependency_depth_by_component[component],
                "downstream_depth_scc_condensation": downstream_depth_by_component[component],
                "weak_component_all": weak_assignments["all_project_environment"][node],
                "weak_component_public_induced": weak_assignments["environment_public"][node] if node in public_nodes else "",
                "weak_component_confirmed_source_written_public_induced": weak_assignments["confirmed_source_written_public"][node] if node in confirmed_public_nodes else "",
                "strong_component_all": component,
                "strong_component_size": component_sizes[component],
                "no_incoming_project_edge": str(not reverse[node]).lower(),
                "no_outgoing_project_edge": str(not adjacency[node]).lower(),
                "isolated_in_project_graph": str(not reverse[node] and not adjacency[node]).lower(),
                "direct_mathlib_dependency_count": all_scope_out[node]["mathlib"],
                "direct_other_external_dependency_count": sum(
                    count for scope, count in all_scope_out[node].items()
                    if scope not in {"project", "mathlib"}
                ),
                "raw_declaration_artifact": str(args.declarations),
                "raw_dependency_artifact": str(args.dependencies),
            }
            decl_writer.writerow(row)
    finally:
        decl_handle.close()

    # Patch the type/body counts with a streaming rewrite, avoiding a per-edge object map.
    type_counts = [0] * node_count
    body_counts = [0] * node_count
    both_counts = [0] * node_count
    for edge in edges:
        type_counts[edge.source] += edge.in_type
        body_counts[edge.source] += edge.in_body
        both_counts[edge.source] += edge.in_type and edge.in_body
    rewritten = output / "declaration_metrics.rewrite.csv.gz"
    with gzip.open(decl_path, "rt", newline="", encoding="utf-8") as source_handle, gzip.open(
        rewritten, "wt", newline="", encoding="utf-8", compresslevel=9
    ) as target_handle:
        reader = csv.DictReader(source_handle)
        writer = csv.DictWriter(target_handle, fieldnames=declaration_fields)
        writer.writeheader()
        for node, row in enumerate(reader):
            row["direct_project_type_dependency_count"] = type_counts[node]
            row["direct_project_body_dependency_count"] = body_counts[node]
            row["direct_project_both_dependency_count"] = both_counts[node]
            writer.writerow(row)
    rewritten.replace(decl_path)

    origins_fields = [
        "name", "module", "kind", "is_public", "is_internal", "is_private",
        "is_reserved_name", "equation_parent", "has_direct_selection_range",
        "selection_source_token", "authorship_class", "classifier_evidence",
    ]
    with (output / "declaration_origins_and_authorship.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=origins_fields)
        writer.writeheader()
        for node, decl in enumerate(declarations):
            meta = metadata_by_name[decl.name]
            token = source_tokens[node]
            writer.writerow({
                "name": decl.name,
                "module": decl.module,
                "kind": decl.kind,
                "is_public": str(decl.is_public).lower(),
                "is_internal": str(decl.is_internal).lower(),
                "is_private": str(decl.is_private).lower(),
                "is_reserved_name": str(meta.reserved).lower(),
                "equation_parent": origins[decl.name]["equation_parent"],
                "has_direct_selection_range": str(meta.selection_start_line is not None).lower(),
                "selection_source_token": token,
                "authorship_class": authorship[node],
                "classifier_evidence": (
                    "Lean isReservedName=true"
                    if meta.reserved
                    else "direct selection-range token equals final declaration-name component or exact namespace-qualified suffix"
                    if authorship[node] == "confirmed_source_written"
                    else "unique static declaration-introducer name in owning module; no direct range"
                    if authorship[node] == "likely_source_written_unique_static_name"
                    else "direct range token does not equal final declaration-name component"
                    if token
                    else "no direct declaration range; not promoted to confirmed source-written"
                ),
            })

    component_fields = ["universe", "component_kind", "component_id", "size", "is_nontrivial"]
    with (output / "components.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=component_fields)
        writer.writeheader()
        for universe, components in weak_component_lists.items():
            for cid, members in enumerate(components):
                writer.writerow({"universe": universe, "component_kind": "weak_induced", "component_id": cid, "size": len(members), "is_nontrivial": str(len(members) > 1).lower()})
        for cid, members in enumerate(strong_components):
            writer.writerow({"universe": "all_project_environment", "component_kind": "strong", "component_id": cid, "size": len(members), "is_nontrivial": str(len(members) > 1).lower()})

    weak_membership_fields = [
        "universe", "component_id", "component_size", "name", "module",
        "is_public", "authorship_class",
    ]
    weak_membership_path = output / "weak_component_memberships.csv.gz"
    weak_handle, weak_writer = gzip_csv_writer(
        weak_membership_path, weak_membership_fields
    )
    try:
        for universe, included in universes.items():
            assignments = weak_assignments[universe]
            sizes = [len(members) for members in weak_component_lists[universe]]
            for node in sorted(included, key=lambda n: names[n]):
                component_id = assignments[node]
                assert component_id is not None
                weak_writer.writerow({
                    "universe": universe,
                    "component_id": component_id,
                    "component_size": sizes[component_id],
                    "name": names[node],
                    "module": declarations[node].module,
                    "is_public": str(declarations[node].is_public).lower(),
                    "authorship_class": authorship[node],
                })
    finally:
        weak_handle.close()

    strong_membership_fields = [
        "universe", "component_id", "component_size", "is_nontrivial",
        "name", "module", "kind", "is_public", "authorship_class",
    ]
    strong_membership_path = output / "strong_component_memberships.csv.gz"
    strong_handle, strong_writer = gzip_csv_writer(
        strong_membership_path, strong_membership_fields
    )
    try:
        for node, name in enumerate(names):
            component_id = strong_of[node]
            size = component_sizes[component_id]
            strong_writer.writerow({
                "universe": "all_project_environment",
                "component_id": component_id,
                "component_size": size,
                "is_nontrivial": str(size > 1).lower(),
                "name": name,
                "module": declarations[node].module,
                "kind": declarations[node].kind,
                "is_public": str(declarations[node].is_public).lower(),
                "authorship_class": authorship[node],
            })
    finally:
        strong_handle.close()

    leaf_fields = [
        "name", "module", "kind", "layer", "domain", "chapter", "is_public",
        "authorship_class", "no_incoming_project_edge", "no_outgoing_project_edge",
        "isolated_in_project_graph", "direct_dependency_count", "transitive_dependency_count",
        "endpoint_caution",
    ]
    with (output / "isolates_and_apparent_leaves.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=leaf_fields)
        writer.writeheader()
        for node, decl in enumerate(declarations):
            if reverse[node] and adjacency[node]:
                continue
            writer.writerow({
                "name": decl.name,
                "module": decl.module,
                "kind": decl.kind,
                "layer": layers[node],
                "domain": domains[node],
                "chapter": chapters[node],
                "is_public": str(decl.is_public).lower(),
                "authorship_class": authorship[node],
                "no_incoming_project_edge": str(not reverse[node]).lower(),
                "no_outgoing_project_edge": str(not adjacency[node]).lower(),
                "isolated_in_project_graph": str(not reverse[node] and not adjacency[node]).lower(),
                "direct_dependency_count": len(adjacency[node]),
                "transitive_dependency_count": transitive_dependency_by_component[strong_of[node]],
                "endpoint_caution": "No incoming project edge is not evidence of redundancy; this may be an external API endpoint.",
            })

    coverage_fields = [
        "universe", "metric", "numerator", "denominator", "percent", "filters",
        "raw_artifact", "raw_columns",
    ]
    coverage_rows: list[dict[str, object]] = []
    for universe, included in universes.items():
        predicates = {
            "at_least_one_incoming_project_reference": lambda n: bool(reverse[n]),
            "used_by_at_least_one_different_module": lambda n: any(declarations[c].module != declarations[n].module for c in reverse[n]),
            "used_by_at_least_one_different_layer": lambda n: any(layers[c] != layers[n] for c in reverse[n]),
            "used_by_multiple_consumer_modules": lambda n: len(direct_consumer_modules[n]) >= 2,
            "used_by_multiple_consumer_domains": lambda n: len(direct_consumer_domains[n]) >= 2,
            "no_incoming_project_edge": lambda n: not reverse[n],
            "no_outgoing_project_edge": lambda n: not adjacency[n],
            "neither_incoming_nor_outgoing_project_edge": lambda n: not reverse[n] and not adjacency[n],
            "participates_in_nontrivial_multistep_chain": lambda n: dependency_depth_by_component[strong_of[n]] >= 2 or downstream_depth_by_component[strong_of[n]] >= 2,
        }
        for metric, predicate in predicates.items():
            numerator = sum(1 for node in included if predicate(node))
            coverage_rows.append({
                "universe": universe,
                "metric": metric,
                "numerator": numerator,
                "denominator": len(included),
                "percent": pct(numerator, len(included)),
                "filters": "target declaration belongs to named universe; consumers may be any project declaration",
                "raw_artifact": f"{args.declarations}; {args.dependencies}",
                "raw_columns": "name,is_internal,is_private; source,target,target_scope,source_module,target_module",
            })
    with (output / "incoming_and_cross_boundary_coverage.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=coverage_fields)
        writer.writeheader()
        writer.writerows(coverage_rows)

    inventory_fields = ["universe", "dimension", "category", "count", "universe_denominator", "percent", "filters"]
    with (output / "declaration_inventory.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=inventory_fields)
        writer.writeheader()
        for universe, included in universes.items():
            dimensions = {
                "raw_constant_kind": [declarations[n].kind for n in included],
                "refined_mutually_exclusive_kind": [refined_kind(declarations[n], metadata_by_name[names[n]]) for n in included],
                "architectural_layer": [layers[n] for n in included],
                "domain": [domains[n] for n in included],
                "chapter": [chapters[n] for n in included],
                "top_level_namespace_after_NumStability": [namespaces[n] for n in included],
                "authorship_class": [authorship[n] for n in included],
                "body_presence": ["with_body" if declarations[n].has_body else "without_body" for n in included],
                "documentation": ["documented" if metadata_by_name[names[n]].documented else "undocumented" for n in included],
                "environment_visibility": [
                    "public"
                    if declarations[n].is_public
                    else "internal_and_private"
                    if declarations[n].is_internal and declarations[n].is_private
                    else "internal_only"
                    if declarations[n].is_internal
                    else "private_only"
                    for n in included
                ],
            }
            for dimension, values in dimensions.items():
                for category, count in sorted(Counter(values).items()):
                    writer.writerow({
                        "universe": universe,
                        "dimension": dimension,
                        "category": category,
                        "count": count,
                        "universe_denominator": len(included),
                        "percent": pct(count, len(included)),
                        "filters": "declaration belongs to named universe; mutually exclusive within each dimension",
                    })

    # Dependency matrices count unique declaration pairs, because the extractor emits one row per pair.
    matrix_specs = {
        "layer_dependency_matrix.csv": (layers, layers),
        "domain_dependency_matrix.csv": (domains, domains),
        "chapter_dependency_matrix.csv": (chapters, chapters),
    }
    matrix_summaries: dict[str, int] = {}
    for filename, (source_categories, target_categories) in matrix_specs.items():
        counts: dict[tuple[str, str], Counter[str]] = defaultdict(Counter)
        sources: dict[tuple[str, str], set[int]] = defaultdict(set)
        targets: dict[tuple[str, str], set[int]] = defaultdict(set)
        for edge in edges:
            key = (source_categories[edge.source], target_categories[edge.target])
            counts[key]["edges"] += 1
            counts[key]["type"] += edge.in_type
            counts[key]["body"] += edge.in_body
            counts[key]["both"] += edge.in_type and edge.in_body
            sources[key].add(edge.source)
            targets[key].add(edge.target)
        fields = ["consumer_category", "dependency_category", "unique_declaration_pairs", "type_pairs", "body_pairs", "both_pairs", "distinct_consumer_declarations", "distinct_dependency_declarations", "orientation"]
        with (output / filename).open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fields)
            writer.writeheader()
            for key in sorted(counts):
                writer.writerow({
                    "consumer_category": key[0],
                    "dependency_category": key[1],
                    "unique_declaration_pairs": counts[key]["edges"],
                    "type_pairs": counts[key]["type"],
                    "body_pairs": counts[key]["body"],
                    "both_pairs": counts[key]["both"],
                    "distinct_consumer_declarations": len(sources[key]),
                    "distinct_dependency_declarations": len(targets[key]),
                    "orientation": EDGE_DIRECTION,
                })
        matrix_summaries[filename] = len(counts)

    # Compiled project imports versus declaration-derived module pairs.
    imports: set[tuple[str, str]] = set()
    with open_text(args.imports) as handle:
        for row in csv.DictReader(handle):
            if row["target_scope"] == "project":
                imports.add((row["source_module"], row["target_module"]))
    logical_pair_counts: Counter[tuple[str, str]] = Counter()
    logical_pair_type: Counter[tuple[str, str]] = Counter()
    logical_pair_body: Counter[tuple[str, str]] = Counter()
    logical_pair_sources: dict[tuple[str, str], set[int]] = defaultdict(set)
    for edge in edges:
        pair = (declarations[edge.source].module, declarations[edge.target].module)
        if pair[0] == pair[1]:
            continue
        logical_pair_counts[pair] += 1
        logical_pair_type[pair] += edge.in_type
        logical_pair_body[pair] += edge.in_body
        logical_pair_sources[pair].add(edge.source)
    import_closure = module_import_closure(imports)
    import_sccs = named_graph_sccs(imports)
    logical_sccs = named_graph_sccs(set(logical_pair_counts))
    nontrivial_logical_scc_of: dict[str, int] = {}
    for component_id, members in enumerate(logical_sccs):
        if len(members) > 1:
            for module in members:
                nontrivial_logical_scc_of[module] = component_id
    with (output / "module_graph_components.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        fields = ["graph", "component_id", "size", "is_cycle", "member_modules"]
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for graph_name, components in (
            ("compiled_project_import", import_sccs),
            ("declaration_derived_logical", logical_sccs),
        ):
            for component_id, members in enumerate(components):
                writer.writerow({
                    "graph": graph_name,
                    "component_id": component_id,
                    "size": len(members),
                    "is_cycle": str(len(members) > 1).lower(),
                    "member_modules": ";".join(sorted(members)),
                })

    # Preserve declaration rows inducing each apparent module-level logical SCC.
    # This is deliberately separate from the compiled import graph: generated or
    # privately owned constants can produce a logical ownership anomaly without
    # a source/module import cycle.
    logical_scc_edge_fields = edge_fields + [
        "logical_module_scc_id", "source_authorship_class",
        "target_authorship_class", "interpretation_caution",
    ]
    with (output / "logical_module_scc_edge_evidence.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=logical_scc_edge_fields)
        writer.writeheader()
        for edge in edges:
            source_module = declarations[edge.source].module
            target_module = declarations[edge.target].module
            component_id = nontrivial_logical_scc_of.get(source_module)
            if (
                component_id is None
                or nontrivial_logical_scc_of.get(target_module) != component_id
                or source_module == target_module
            ):
                continue
            source_layer, target_layer = layers[edge.source], layers[edge.target]
            in_type, in_body = edge.in_type, edge.in_body
            writer.writerow({
                "source": names[edge.source],
                "source_module": source_module,
                "source_layer": source_layer,
                "source_domain": domains[edge.source],
                "source_chapter": chapters[edge.source],
                "target": names[edge.target],
                "target_module": target_module,
                "target_layer": target_layer,
                "target_domain": domains[edge.target],
                "target_chapter": chapters[edge.target],
                "occurs_in_type": str(in_type).lower(),
                "occurs_in_body": str(in_body).lower(),
                "edge_class": "both" if in_type and in_body else "type" if in_type else "body",
                "same_module": "false",
                "cross_namespace": str(namespaces[edge.source] != namespaces[edge.target]).lower(),
                "cross_layer": str(source_layer != target_layer).lower(),
                "against_intended_layer_direction": str(
                    source_layer in LAYER_RANK
                    and target_layer in LAYER_RANK
                    and LAYER_RANK[source_layer] < LAYER_RANK[target_layer]
                ).lower(),
                "cross_domain": str(domains[edge.source] != domains[edge.target]).lower(),
                "cross_chapter": str(
                    chapters[edge.source] != "Unassigned"
                    and chapters[edge.target] != "Unassigned"
                    and chapters[edge.source] != chapters[edge.target]
                ).lower(),
                "raw_artifact": str(args.dependencies),
                "logical_module_scc_id": component_id,
                "source_authorship_class": authorship[edge.source],
                "target_authorship_class": authorship[edge.target],
                "interpretation_caution": (
                    "Module-level logical SCC only; inspect generated/private ownership. "
                    "It is not a compiled import cycle."
                ),
            })
    module_dep_fields = [
        "consumer_module", "dependency_module", "is_direct_compiled_import",
        "has_direct_logical_declaration_pair", "logical_unique_declaration_pairs",
        "logical_type_pairs", "logical_body_pairs", "distinct_consumer_declarations",
        "dependency_available_through_transitive_import", "classification", "caution",
    ]
    with (output / "module_import_vs_logical_dependencies.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=module_dep_fields)
        writer.writeheader()
        for pair in sorted(imports | set(logical_pair_counts)):
            is_import = pair in imports
            has_logical = pair in logical_pair_counts
            transitive = pair[1] in import_closure.get(pair[0], set()) and not is_import
            classification = (
                "direct_import_with_direct_logical_use" if is_import and has_logical
                else "direct_import_without_direct_logical_use" if is_import
                else "logical_use_via_transitive_import" if transitive
                else "logical_use_without_compiled_import_reachability_unexpected"
            )
            writer.writerow({
                "consumer_module": pair[0],
                "dependency_module": pair[1],
                "is_direct_compiled_import": str(is_import).lower(),
                "has_direct_logical_declaration_pair": str(has_logical).lower(),
                "logical_unique_declaration_pairs": logical_pair_counts[pair],
                "logical_type_pairs": logical_pair_type[pair],
                "logical_body_pairs": logical_pair_body[pair],
                "distinct_consumer_declarations": len(logical_pair_sources[pair]),
                "dependency_available_through_transitive_import": str(transitive).lower(),
                "classification": classification,
                "caution": "Import-only does not imply removable: notation, tactics, macros, attributes, and instances are not logical declaration edges.",
            })

    module_members: dict[str, list[int]] = defaultdict(list)
    for node, decl in enumerate(declarations):
        module_members[decl.module].append(node)
    import_out: Counter[str] = Counter(source for source, _ in imports)
    import_in: Counter[str] = Counter(target for _, target in imports)
    logical_out_pairs: Counter[str] = Counter(source for source, _ in logical_pair_counts)
    logical_in_pairs: Counter[str] = Counter(target for _, target in logical_pair_counts)
    module_fields = [
        "module", "source_path", "layer", "domain", "chapter", "physical_lines",
        "code_bearing_lines", "environment_declarations", "public_declarations",
        "confirmed_source_written_public_declarations", "declarations_per_100_code_lines",
        "direct_compiled_project_import_count", "direct_logical_dependency_module_count",
        "direct_logical_consumer_module_count", "imports_without_direct_logical_dependency_count",
        "public_declarations_used_outside_module", "internal_edge_count",
        "external_api_declarations", "internal_coupling_to_external_api_ratio",
    ]
    with (output / "module_metrics.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=module_fields)
        writer.writeheader()
        for module in sorted(set(module_members) | {s for s, _ in imports} | {t for _, t in imports}):
            members = module_members.get(module, [])
            info = modules.get(module)
            internal_edges = sum(
                1 for node in members for target in adjacency[node]
                if declarations[target].module == module
            )
            external_api = sum(
                1 for node in members if declarations[node].is_public and any(
                    declarations[c].module != module for c in reverse[node]
                )
            )
            import_without = sum(
                1 for pair in imports if pair[0] == module and pair not in logical_pair_counts
            )
            code_lines = info.code_lines if info else 0
            writer.writerow({
                "module": module,
                "source_path": info.source_path if info else "",
                "layer": layer_for_module(module, modules),
                "domain": domain_for_module(module, modules),
                "chapter": chapter_for_module(module, modules),
                "physical_lines": info.physical_lines if info else "",
                "code_bearing_lines": code_lines if info else "",
                "environment_declarations": len(members),
                "public_declarations": sum(declarations[n].is_public for n in members),
                "confirmed_source_written_public_declarations": sum(n in confirmed_public_nodes for n in members),
                "declarations_per_100_code_lines": round(100 * len(members) / code_lines, 6) if code_lines else "",
                "direct_compiled_project_import_count": import_out[module],
                "direct_logical_dependency_module_count": logical_out_pairs[module],
                "direct_logical_consumer_module_count": logical_in_pairs[module],
                "imports_without_direct_logical_dependency_count": import_without,
                "public_declarations_used_outside_module": external_api,
                "internal_edge_count": internal_edges,
                "external_api_declarations": external_api,
                "internal_coupling_to_external_api_ratio": round(internal_edges / external_api, 6) if external_api else "",
            })

    # Aggregate/entry-point exposure: module import closure plus the entry module itself.
    entry_modules: list[str] = []
    with args.entry_points.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            if row["entry_kind"] in {"root_entry", "documented_aggregate"}:
                entry_modules.append(row["module"])
    exposure_fields = ["entry_module", "universe", "reachable_declarations", "universe_declarations", "percent", "reachability_basis", "visibility_limitation"]
    with (output / "public_entrypoint_exposure.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=exposure_fields)
        writer.writeheader()
        for entry in sorted(set(entry_modules)):
            reachable_modules = {entry} | import_closure.get(entry, set())
            for universe, included in universes.items():
                reachable = sum(declarations[node].module in reachable_modules for node in included)
                writer.writerow({
                    "entry_module": entry,
                    "universe": universe,
                    "reachable_declarations": reachable,
                    "universe_declarations": len(included),
                    "percent": pct(reachable, len(included)),
                    "reachability_basis": "compiled transitive module-import closure plus entry module",
                    "visibility_limitation": "Reachability is not practical usability; consumer probes are separate.",
                })

    # Longest reliable component-level path, with actual declaration edges for every step.
    edge_for_component_pair: dict[tuple[int, int], Edge] = {}
    for edge in edges:
        pair = (strong_of[edge.source], strong_of[edge.target])
        if pair[0] != pair[1] and pair not in edge_for_component_pair:
            edge_for_component_pair[pair] = edge
    start_component = max(range(len(dag)), key=lambda c: dependency_depth_by_component[c])
    path_components = [start_component]
    while next_component[path_components[-1]] is not None:
        path_components.append(next_component[path_components[-1]])  # type: ignore[arg-type]
    longest_fields = ["step", "source", "source_module", "target", "target_module", "occurs_in_type", "occurs_in_body", "source_scc", "target_scc"]
    with (output / "longest_dependency_path.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=longest_fields)
        writer.writeheader()
        for step, (source_component, target_component) in enumerate(zip(path_components, path_components[1:]), 1):
            edge = edge_for_component_pair[(source_component, target_component)]
            writer.writerow({
                "step": step,
                "source": names[edge.source],
                "source_module": declarations[edge.source].module,
                "target": names[edge.target],
                "target_module": declarations[edge.target].module,
                "occurs_in_type": str(edge.in_type).lower(),
                "occurs_in_body": str(edge.in_body).lower(),
                "source_scc": source_component,
                "target_scc": target_component,
            })

    # Human-sortable fan-in leaders and low/high hierarchy signals.
    leader_fields = ["rank_metric", "rank", "name", "module", "kind", "layer", "domain", "chapter", "value", "direct_fan_in", "direct_fan_out", "transitive_downstream_consumers", "downstream_modules", "downstream_depth", "dependency_depth"]
    with (output / "reuse_leaders.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=leader_fields)
        writer.writeheader()
        ranking_specs = {
            "direct_fan_in": lambda n: len(reverse[n]),
            "transitive_downstream_consumers": lambda n: transitive_consumer_by_component[strong_of[n]],
            "downstream_consumer_modules": lambda n: downstream_module_masks[strong_of[n]].bit_count(),
            "downstream_depth": lambda n: downstream_depth_by_component[strong_of[n]],
            "reused_low_in_hierarchy_product": lambda n: transitive_consumer_by_component[strong_of[n]] * (1 + downstream_depth_by_component[strong_of[n]]),
        }
        for metric, value_fn in ranking_specs.items():
            ranked = sorted(range(node_count), key=lambda n: (-value_fn(n), names[n]))[:100]
            for rank, node in enumerate(ranked, 1):
                component = strong_of[node]
                writer.writerow({
                    "rank_metric": metric,
                    "rank": rank,
                    "name": names[node],
                    "module": declarations[node].module,
                    "kind": declarations[node].kind,
                    "layer": layers[node],
                    "domain": domains[node],
                    "chapter": chapters[node],
                    "value": value_fn(node),
                    "direct_fan_in": len(reverse[node]),
                    "direct_fan_out": len(adjacency[node]),
                    "transitive_downstream_consumers": transitive_consumer_by_component[component],
                    "downstream_modules": downstream_module_masks[component].bit_count(),
                    "downstream_depth": downstream_depth_by_component[component],
                    "dependency_depth": dependency_depth_by_component[component],
                })

    universe_summary: dict[str, object] = {}
    distribution_rows: list[dict[str, object]] = []
    for universe, included in universes.items():
        components = weak_component_lists[universe]
        largest = len(components[0]) if components else 0
        universe_summary[universe] = {
            "declarations": len(included),
            "weak_components_induced": len(components),
            "largest_weak_component_declarations": largest,
            "largest_weak_component_percent": pct(largest, len(included)),
        }
        metrics = {
            "direct_fan_in": [len(reverse[n]) for n in included],
            "direct_fan_out": [len(adjacency[n]) for n in included],
            "transitive_downstream_consumers": [transitive_consumer_by_component[strong_of[n]] for n in included],
            "transitive_project_dependencies": [transitive_dependency_by_component[strong_of[n]] for n in included],
            "dependency_depth": [dependency_depth_by_component[strong_of[n]] for n in included],
            "downstream_depth": [downstream_depth_by_component[strong_of[n]] for n in included],
        }
        for metric, values in metrics.items():
            row: dict[str, object] = {"universe": universe, "metric": metric, "percentile_method": "nearest-rank sorted[ceil(q*n)-1]; p0=min"}
            row.update(distribution(values))
            distribution_rows.append(row)
    dist_fields = ["universe", "metric", "percentile_method", "count", "mean", "p00", "p25", "p50", "p75", "p90", "p95", "p99", "p100"]
    with (output / "fan_and_depth_distributions.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=dist_fields)
        writer.writeheader()
        writer.writerows(distribution_rows)

    edge_counts = Counter()
    for edge in edges:
        edge_counts["all"] += 1
        edge_counts["type"] += edge.in_type
        edge_counts["body"] += edge.in_body
        edge_counts["both"] += edge.in_type and edge.in_body
        edge_counts["intra_module"] += declarations[edge.source].module == declarations[edge.target].module
        edge_counts["cross_module"] += declarations[edge.source].module != declarations[edge.target].module
        edge_counts["cross_namespace"] += namespaces[edge.source] != namespaces[edge.target]
        edge_counts["cross_layer"] += layers[edge.source] != layers[edge.target]
        edge_counts["cross_domain"] += domains[edge.source] != domains[edge.target]
        edge_counts["cross_chapter"] += chapters[edge.source] != "Unassigned" and chapters[edge.target] != "Unassigned" and chapters[edge.source] != chapters[edge.target]
        edge_counts["against_intended_layer_direction"] += layers[edge.source] in LAYER_RANK and layers[edge.target] in LAYER_RANK and LAYER_RANK[layers[edge.source]] < LAYER_RANK[layers[edge.target]]

    coverage_index = {
        f"{row['universe']}::{row['metric']}": {
            "numerator": row["numerator"],
            "denominator": row["denominator"],
            "percent": row["percent"],
        }
        for row in coverage_rows
    }
    summary = {
        "schema_version": SCHEMA_VERSION,
        "source_commit": args.source_commit,
        "analyzer_sha256": sha256(Path(__file__)),
        "edge_direction": EDGE_DIRECTION,
        "scope": {
            "project_prefix": "NumStability",
            "raw_declarations": str(args.declarations),
            "raw_dependencies": str(args.dependencies),
            "raw_imports": str(args.imports),
            "metadata": str(args.metadata),
            "origins": str(args.origins),
            "declaration_row_count": node_count,
            "input_sha256": {
                str(path): sha256(path)
                for path in (
                    args.declarations, args.dependencies, args.imports,
                    args.metadata, args.origins, args.modules,
                    args.static_declarations, args.entry_points,
                )
            },
        },
        "declaration_inventory": {
            "all_environment_declarations": node_count,
            "environment_public_declarations": len(public_nodes),
            "environment_private_or_internal_declarations": node_count - len(public_nodes),
            "confirmed_source_written_declarations": len(confirmed_nodes),
            "confirmed_source_written_public_declarations": len(confirmed_public_nodes),
            "reserved_declarations": sum(metadata_by_name[name].reserved for name in names),
            "generated_or_authorship_unresolved_declarations": node_count - len(confirmed_nodes),
            "with_bodies": sum(decl.has_body for decl in declarations),
            "without_bodies": sum(not decl.has_body for decl in declarations),
            "documented": sum(metadata_by_name[name].documented for name in names),
            "unsafe": sum(metadata_by_name[name].unsafe for name in names),
            "partial": sum(metadata_by_name[name].partial for name in names),
            "by_kind": dict(sorted(kind_counter.items())),
            "by_refined_kind_mutually_exclusive": dict(sorted(refined_kind_counter.items())),
            "by_layer": dict(sorted(layer_counter.items())),
            "by_domain": dict(sorted(domain_counter.items())),
            "by_chapter": dict(sorted(chapter_counter.items())),
            "by_top_namespace": dict(namespace_counter.most_common()),
            "by_authorship_class": {
                category: authorship_counter[category]
                for category in (
                    "confirmed_source_written",
                    "likely_source_written_unique_static_name",
                    "lean_reserved_generated",
                    "range_present_token_mismatch_generated_or_unresolved",
                    "generated_kind_no_direct_range",
                    "internal_no_direct_range",
                    "unresolved_no_direct_range",
                )
            },
            "environment_internal_declarations": sum(decl.is_internal for decl in declarations),
            "environment_private_declarations": sum(decl.is_private for decl in declarations),
            "environment_internal_and_private_declarations": sum(
                decl.is_internal and decl.is_private for decl in declarations
            ),
        },
        "direct_project_graph": dict(edge_counts),
        "component_and_depth": {
            "universes": universe_summary,
            "strong_components_all": len(strong_components),
            "nontrivial_strong_components_all": sum(size > 1 for size in component_sizes),
            "declarations_in_nontrivial_strong_components": sum(size for size in component_sizes if size > 1),
            "maximum_dependency_depth_scc_condensation": max(dependency_depth_by_component, default=0),
            "maximum_downstream_depth_scc_condensation": max(downstream_depth_by_component, default=0),
            "longest_path_edge_count": len(path_components) - 1,
            "longest_path_artifact": str(output / "longest_dependency_path.csv"),
        },
        "coverage": coverage_index,
        "module_import_vs_logical": {
            "direct_compiled_project_import_pairs": len(imports),
            "cross_module_logical_dependency_pairs": len(logical_pair_counts),
            "direct_imports_without_direct_logical_pair": len(imports - set(logical_pair_counts)),
            "logical_pairs_without_direct_import": len(set(logical_pair_counts) - imports),
            "logical_pairs_available_only_through_transitive_import": sum(pair[1] in import_closure.get(pair[0], set()) for pair in set(logical_pair_counts) - imports),
            "compiled_import_nontrivial_sccs": sum(len(component) > 1 for component in import_sccs),
            "logical_module_dependency_nontrivial_sccs": sum(len(component) > 1 for component in logical_sccs),
            "logical_module_scc_edge_evidence": str(output / "logical_module_scc_edge_evidence.csv"),
            "logical_module_scc_caution": "A declaration-derived module SCC is not necessarily a source/import cycle; the compiled import graph must be checked separately.",
        },
        "matrix_nonempty_cells": matrix_summaries,
        "validation": {
            "raw_project_pair_duplicates": duplicate_project_rows,
            "project_targets_missing_from_declaration_universe": missing_project_targets,
            "metadata_universe_exact_match": True,
            "origin_universe_exact_match": True,
            "two_reserved_extractors_agree": True,
        },
        "authorship_classifier": {
            "confirmed_source_written": "non-reserved declaration with a direct Lean selection range whose exact source slice equals the terminal declaration-name component or an exact namespace-qualified suffix of the environment name",
            "likely_source_written": "non-reserved declaration without a direct range but with a unique same-terminal static declaration-introducer in the owning module; excluded from confirmed-source-written metrics",
            "generated_reserved": "Lean Environment.isReservedName=true",
            "limitations": "A range/token is declaration-origin evidence, not human authorship proof; macro-generated declarations can inherit ranges. Conservative metrics use only the confirmed category and keep all other categories separate.",
        },
        "metric_contract": {
            "incoming_coverage": "target declarations in the named universe with >=1 distinct incoming direct edge from any project declaration / declaration count of that universe",
            "cross_module_use": "target declarations in the named universe with >=1 incoming direct edge whose consumer module differs / declaration count of that universe",
            "direct_edge_count": "unique ordered project declaration pairs; type/body flags can overlap and both is their intersection",
            "transitive_downstream_count": "exact distinct project declarations in reverse transitive closure, excluding self; SCC-condensed integer-bitset algorithm",
            "component_coverage": "weak components of the universe-induced undirected project graph; connectedness, not reuse",
            "depth": "longest path in the SCC condensation DAG; cycles are collapsed",
            "percentiles": "nearest-rank sorted[ceil(q*n)-1], with p0=min",
        },
        "limitations": [
            "Compilation establishes acceptance in the recorded Lean environment, not faithfulness to Higham.",
            "A dependency edge establishes formal reference and compositional typechecking, not source faithfulness.",
            "Weak-component membership is connectedness, not consumption or usefulness.",
            "No incoming project edge is not redundancy; it may identify an intended external endpoint.",
            "Import-only pairs may be required for notation, tactics, macros, attributes, or instances.",
            "Generated declarations are not handwritten API; authorship classes remain separate.",
            "High fan-in measures internal consumption, not interface quality.",
            "Path-derived domains/layers/chapters are deterministic architectural classifications, not mathematical proof.",
        ],
    }
    summary_path = output / "summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    schema_text = f"""# Current elaborated graph schema

    Schema: `{SCHEMA_VERSION}`. Source commit: `{args.source_commit}`.

Edge orientation: `{EDGE_DIRECTION}`.

The raw dependency extractor emits one row per ordered source/target pair and
two overlapping Boolean flags, `occurs_in_type` and `occurs_in_body`.  The
analyzer validates uniqueness.  `type + body - both = all project pairs`.

Percentages are written to `incoming_and_cross_boundary_coverage.csv` with
their numerator, denominator, exact universe, filters, raw artifact, and raw
columns.  Public means environment-public (`is_internal=false` and
`is_private=false`).  Confirmed source-written is the conservative classifier
recorded in `summary.json`; likely and unresolved names are excluded.

    Transitive downstream counts are exact distinct reverse-reachable project
declarations after SCC condensation.  Dependency depths are exact on that
condensation DAG.  Weak components for public/source-written universes are
    computed on induced subgraphs.

    Explicit declaration-to-component membership is recorded in
    `weak_component_memberships.csv.gz` and
    `strong_component_memberships.csv.gz`. Apparent module-level logical SCC
    edges are preserved in `logical_module_scc_edge_evidence.csv` and must be
    interpreted separately from the compiled import graph.

An import lacking a direct logical pair is only a review candidate.  No
incoming declaration is called unused.  Exact graph evidence does not establish
source faithfulness or universal API ease.
"""
    (output / "SCHEMA.md").write_text(schema_text, encoding="utf-8")

    artifact_rows = []
    for path in sorted(output.iterdir()):
        if path.is_file() and path.name != "SHA256SUMS":
            artifact_rows.append(f"{sha256(path)}  {path.name}")
    (output / "SHA256SUMS").write_text("\n".join(artifact_rows) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
