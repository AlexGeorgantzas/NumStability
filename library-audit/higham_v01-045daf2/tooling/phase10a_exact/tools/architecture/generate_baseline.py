#!/usr/bin/env python3
"""Generate a reproducible architecture baseline for NumStability.

The source scan uses only the Python standard library.  Unless
``--skip-declarations`` is passed, the script first builds ``NumStability`` and
then runs ``declaration_dependencies.lean`` to inspect the compiled Lean
environment.  The generated Markdown is intended for humans; the JSON is the
machine-readable source of truth.
"""

from __future__ import annotations

import argparse
import collections
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator, Sequence


SCHEMA_VERSION = 1
PROJECT_PREFIX = "NumStability"
IMPORT_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import[ \t]+([A-Za-z0-9_'.]+)"
)
PROVENANCE_TERMS = (
    "Higham",
    "Chapter",
    "Problem",
    "Source",
    "Closure",
    "Bridge",
    "Actual",
)


class BaselineError(RuntimeError):
    """A user-actionable baseline generation failure."""


@dataclass(frozen=True)
class SourceModule:
    name: str
    path: str
    line_count: int
    nonblank_line_count: int
    byte_count: int
    imports: tuple[str, ...]
    has_module_docstring: bool


class DisjointSet:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))
        self.sizes = [1] * size

    def find(self, item: int) -> int:
        parent = self.parent
        while parent[item] != item:
            parent[item] = parent[parent[item]]
            item = parent[item]
        return item

    def union(self, left: int, right: int) -> None:
        left_root = self.find(left)
        right_root = self.find(right)
        if left_root == right_root:
            return
        if self.sizes[left_root] < self.sizes[right_root]:
            left_root, right_root = right_root, left_root
        self.parent[right_root] = left_root
        self.sizes[left_root] += self.sizes[right_root]

    def largest_component(self, included: Sequence[bool] | None = None) -> int:
        counts: collections.Counter[int] = collections.Counter()
        for item in range(len(self.parent)):
            if included is None or included[item]:
                counts[self.find(item)] += 1
        return max(counts.values(), default=0)


def run(
    command: Sequence[str],
    *,
    cwd: Path,
    check: bool = True,
    capture: bool = True,
) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            list(command),
            cwd=cwd,
            check=check,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE if capture else None,
            stderr=subprocess.PIPE if capture else None,
        )
    except FileNotFoundError as error:
        raise BaselineError(f"required executable not found: {command[0]}") from error
    except subprocess.CalledProcessError as error:
        details = "\n".join(part for part in (error.stdout, error.stderr) if part)
        raise BaselineError(
            f"command failed ({error.returncode}): {' '.join(command)}\n{details}"
        ) from error


def git(root: Path, *args: str) -> str:
    return run(("git", *args), cwd=root).stdout.strip()


def remove_lean_comments(text: str) -> str:
    """Replace nested Lean comments with whitespace while preserving newlines."""

    result: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            result.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            block_depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            newline = text.find("\n", index + 2)
            if newline == -1:
                result.extend(" " * (len(text) - index))
                break
            result.extend(" " * (newline - index))
            result.append("\n")
            index = newline + 1
        else:
            result.append(char)
            if char == '"':
                in_string = True
            index += 1
    return "".join(result)


def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def source_paths(root: Path) -> list[Path]:
    result: list[Path] = []
    umbrella = root / "NumStability.lean"
    if umbrella.is_file():
        result.append(umbrella)
    library = root / "NumStability"
    if library.is_dir():
        result.extend(
            sorted(
                library.rglob("*.lean"),
                key=lambda path: path.relative_to(root).as_posix(),
            )
        )
    return result


def scan_sources(root: Path) -> tuple[dict[str, Any], list[SourceModule]]:
    modules: list[SourceModule] = []
    source_digest = hashlib.sha256()
    for path in source_paths(root):
        relative = path.relative_to(root)
        raw = path.read_bytes()
        text = raw.decode("utf-8-sig", errors="replace")
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        normalized = text.encode("utf-8")
        source_digest.update(relative.as_posix().encode("utf-8"))
        source_digest.update(b"\0")
        source_digest.update(normalized)
        source_digest.update(b"\0")
        uncommented = remove_lean_comments(text)
        imports = tuple(match.group(1) for match in IMPORT_RE.finditer(uncommented))
        lines = text.splitlines()
        modules.append(
            SourceModule(
                name=module_name(relative),
                path=relative.as_posix(),
                line_count=len(lines),
                nonblank_line_count=sum(bool(line.strip()) for line in lines),
                byte_count=len(normalized),
                imports=imports,
                has_module_docstring="/-!" in text,
            )
        )

    by_name = {module.name: module for module in modules}
    if len(by_name) != len(modules):
        raise BaselineError("duplicate Lean module names found in source tree")

    internal_edges: set[tuple[str, str]] = set()
    external_imports: collections.Counter[str] = collections.Counter()
    unresolved_project_imports: collections.Counter[str] = collections.Counter()
    direct_import_count = 0
    for source in modules:
        for target in source.imports:
            direct_import_count += 1
            if target in by_name:
                internal_edges.add((source.name, target))
            elif target == PROJECT_PREFIX or target.startswith(f"{PROJECT_PREFIX}."):
                unresolved_project_imports[target] += 1
            else:
                external_imports[target] += 1

    adjacency: dict[str, set[str]] = {name: set() for name in by_name}
    reverse: dict[str, set[str]] = {name: set() for name in by_name}
    for source, target in internal_edges:
        adjacency[source].add(target)
        reverse[target].add(source)

    components = strongly_connected_components(adjacency)
    cyclic_components = [
        component
        for component in components
        if len(component) > 1
        or (len(component) == 1 and component[0] in adjacency[component[0]])
    ]

    areas = sorted({_module_area(name) for name in by_name})
    area_matrix: dict[str, dict[str, int]] = {
        source: {target: 0 for target in areas} for source in areas
    }
    for source, target in internal_edges:
        area_matrix[_module_area(source)][_module_area(target)] += 1

    direct_files: collections.Counter[str] = collections.Counter()
    for module in modules:
        direct_files[str(Path(module.path).parent).replace("\\", "/")] += 1

    term_counts = {
        term: sum(term.lower() in Path(module.path).stem.lower() for module in modules)
        for term in PROVENANCE_TERMS
    }
    missing_docs = sorted(module.name for module in modules if not module.has_module_docstring)
    largest_modules = sorted(
        modules, key=lambda module: (-module.line_count, module.name)
    )[:20]

    summary: dict[str, Any] = {
        "module_count": len(modules),
        "source_tree_sha256": source_digest.hexdigest(),
        "source_tree_sha256_normalization": (
            "UTF-8 text with BOM removed and CRLF/CR normalized to LF"
        ),
        "line_count": sum(module.line_count for module in modules),
        "nonblank_line_count": sum(module.nonblank_line_count for module in modules),
        "byte_count": sum(module.byte_count for module in modules),
        "direct_import_count": direct_import_count,
        "internal_direct_import_count": len(internal_edges),
        "external_direct_import_count": sum(external_imports.values()),
        "unresolved_project_import_count": sum(unresolved_project_imports.values()),
        "unresolved_project_imports": dict(sorted(unresolved_project_imports.items())),
        "module_docstring_count": len(modules) - len(missing_docs),
        "modules_missing_module_docstring_count": len(missing_docs),
        "modules_missing_module_docstring": missing_docs,
        "filename_provenance_terms": term_counts,
        "import_graph": {
            "edge_count": len(internal_edges),
            "strong_component_count": len(components),
            "cyclic_strong_component_count": len(cyclic_components),
            "cyclic_strong_components": cyclic_components,
            "root_modules_not_imported_by_project": sorted(
                name for name, consumers in reverse.items() if not consumers
            ),
            "leaf_modules_with_no_project_imports": sorted(
                name for name, dependencies in adjacency.items() if not dependencies
            ),
            "top_fan_in": _rank_counts(
                ((name, len(consumers)) for name, consumers in reverse.items()), 20
            ),
            "top_fan_out": _rank_counts(
                ((name, len(dependencies)) for name, dependencies in adjacency.items()), 20
            ),
            "area_matrix": area_matrix,
        },
        "external_imports": dict(sorted(external_imports.items())),
        "largest_modules": [
            {
                "module": module.name,
                "path": module.path,
                "lines": module.line_count,
                "nonblank_lines": module.nonblank_line_count,
            }
            for module in largest_modules
        ],
        "directories_with_most_direct_modules": _rank_counts(direct_files.items(), 20),
    }
    return summary, modules


def audit_tiers(root: Path, modules: Sequence[SourceModule]) -> dict[str, Any] | None:
    """Classify reviewed modules and count explicitly forbidden tier edges."""

    manifest_path = root / "docs" / "architecture" / "tiers.json"
    if not manifest_path.is_file():
        return None
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BaselineError(f"invalid tier manifest {manifest_path}: {error}") from error
    if manifest.get("schema_version") != 1:
        raise BaselineError("unsupported docs/architecture/tiers.json schema version")

    tiers = manifest.get("tiers")
    exact = manifest.get("exact")
    prefixes = manifest.get("prefixes")
    if not isinstance(tiers, list) or not all(isinstance(tier, str) for tier in tiers):
        raise BaselineError("tier manifest `tiers` must be a list of strings")
    if not isinstance(exact, dict) or not all(
        isinstance(name, str) and isinstance(tier, str) for name, tier in exact.items()
    ):
        raise BaselineError("tier manifest `exact` must map module names to tiers")
    if not isinstance(prefixes, list):
        raise BaselineError("tier manifest `prefixes` must be a list")

    allowed = set(tiers)
    if {"reusable", "source"} - allowed:
        raise BaselineError("tier manifest must define `reusable` and `source` tiers")
    for name, tier in exact.items():
        if tier not in allowed:
            raise BaselineError(f"unknown tier {tier!r} for exact module {name}")

    parsed_prefixes: list[tuple[str, str]] = []
    for rule in prefixes:
        if not isinstance(rule, dict):
            raise BaselineError("each tier prefix rule must be an object")
        prefix = rule.get("prefix")
        tier = rule.get("tier")
        if not isinstance(prefix, str) or not isinstance(tier, str):
            raise BaselineError("tier prefix rules require string `prefix` and `tier`")
        if tier not in allowed:
            raise BaselineError(f"unknown tier {tier!r} for prefix {prefix}")
        parsed_prefixes.append((prefix, tier))
    parsed_prefixes.sort(key=lambda item: (-len(item[0]), item[0]))

    by_name = {module.name: module for module in modules}
    missing_exact = sorted(set(exact) - set(by_name))
    if missing_exact:
        raise BaselineError(
            "tier manifest names missing modules: " + ", ".join(missing_exact)
        )

    assignment: dict[str, str] = {}
    for name in sorted(by_name):
        if name in exact:
            assignment[name] = exact[name]
            continue
        for prefix, tier in parsed_prefixes:
            if name == prefix or name.startswith(prefix + "."):
                assignment[name] = tier
                break

    unclassified = sorted(set(by_name) - set(assignment))
    module_counts = collections.Counter(assignment.values())
    edge_matrix = {
        source: {target: 0 for target in tiers}
        for source in tiers
    }
    classified_edge_count = 0
    reusable_to_source_edges: list[dict[str, str]] = []
    reusable_to_mixed_edges: list[dict[str, str]] = []
    for source in modules:
        source_tier = assignment.get(source.name)
        if source_tier is None:
            continue
        for target in sorted(set(source.imports)):
            target_tier = assignment.get(target)
            if target_tier is None:
                continue
            classified_edge_count += 1
            edge_matrix[source_tier][target_tier] += 1
            if source_tier == "reusable" and target_tier == "source":
                reusable_to_source_edges.append(
                    {"source": source.name, "target": target}
                )
            if source_tier == "reusable" and target_tier == "mixed":
                reusable_to_mixed_edges.append(
                    {"source": source.name, "target": target}
                )

    adjacency = {
        module.name: sorted(set(module.imports) & set(by_name)) for module in modules
    }

    def reachable_paths(start: str, target_tier: str) -> list[dict[str, Any]]:
        predecessors: dict[str, str | None] = {start: None}
        queue: collections.deque[str] = collections.deque([start])
        while queue:
            current = queue.popleft()
            for target in adjacency[current]:
                if target not in predecessors:
                    predecessors[target] = current
                    queue.append(target)
        paths: list[dict[str, Any]] = []
        for target in sorted(
            name
            for name, tier in assignment.items()
            if tier == target_tier and name in predecessors
        ):
            path = [target]
            while path[-1] != start:
                predecessor = predecessors[path[-1]]
                if predecessor is None:
                    break
                path.append(predecessor)
            path.reverse()
            paths.append({"source": start, "target": target, "path": path})
        return paths

    reusable_entrypoints = manifest.get("reusable_entrypoints", [])
    if not isinstance(reusable_entrypoints, list) or not all(
        isinstance(name, str) for name in reusable_entrypoints
    ):
        raise BaselineError("tier manifest `reusable_entrypoints` must be a list of strings")
    missing_entrypoints = sorted(set(reusable_entrypoints) - set(by_name))
    if missing_entrypoints:
        raise BaselineError(
            "reusable entry points missing modules: " + ", ".join(missing_entrypoints)
        )
    reusable_modules = sorted(
        {name for name, tier in assignment.items() if tier == "reusable"}
        | set(reusable_entrypoints)
    )
    reusable_to_source_paths = [
        path
        for reusable in reusable_modules
        for path in reachable_paths(reusable, "source")
    ]
    reusable_to_mixed_paths = [
        path
        for reusable in reusable_modules
        for path in reachable_paths(reusable, "mixed")
    ]

    reusable_to_source_edges.sort(key=lambda edge: (edge["source"], edge["target"]))
    reusable_to_mixed_edges.sort(key=lambda edge: (edge["source"], edge["target"]))
    forbidden_edges = [
        *(
            {**edge, "target_tier": "source"}
            for edge in reusable_to_source_edges
        ),
        *(
            {**edge, "target_tier": "mixed"}
            for edge in reusable_to_mixed_edges
        ),
    ]
    forbidden_edges.sort(
        key=lambda edge: (edge["source"], edge["target"], edge["target_tier"])
    )
    classified_count = len(assignment)
    complete = not unclassified
    separation_complete = complete and module_counts.get("mixed", 0) == 0
    return {
        "manifest": manifest_path.relative_to(root).as_posix(),
        "classified_module_count": classified_count,
        "unclassified_module_count": len(unclassified),
        "classification_coverage_percentage": _percentage(
            classified_count, len(modules)
        ),
        "module_counts_by_tier": {
            tier: module_counts.get(tier, 0) for tier in tiers
        },
        "classified_import_edge_count": classified_edge_count,
        "edge_matrix": edge_matrix,
        "reusable_to_source_edge_count": len(reusable_to_source_edges),
        "reusable_to_source_edges": reusable_to_source_edges,
        "reusable_to_mixed_edge_count": len(reusable_to_mixed_edges),
        "reusable_to_mixed_edges": reusable_to_mixed_edges,
        "forbidden_reusable_edge_count": len(forbidden_edges),
        "forbidden_reusable_edges": forbidden_edges,
        "reusable_to_source_reachability_count": len(reusable_to_source_paths),
        "reusable_to_source_paths": reusable_to_source_paths,
        "reusable_to_mixed_reachability_count": len(reusable_to_mixed_paths),
        "reusable_to_mixed_paths": reusable_to_mixed_paths,
        "forbidden_reusable_reachability_count": (
            len(reusable_to_source_paths) + len(reusable_to_mixed_paths)
        ),
        "unclassified_modules": unclassified,
        "classification_complete": complete,
        "tier_separation_complete": separation_complete,
        "reusable_entrypoints": sorted(reusable_entrypoints),
        "physical_source_target_gate_satisfied": (
            separation_complete
            and not reusable_to_source_paths
            and not reusable_to_mixed_paths
        ),
    }


def strongly_connected_components(adjacency: dict[str, set[str]]) -> list[list[str]]:
    sys.setrecursionlimit(max(2000, len(adjacency) * 2 + 100))
    next_index = 0
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    components: list[list[str]] = []

    def visit(node: str) -> None:
        nonlocal next_index
        indices[node] = next_index
        lowlinks[node] = next_index
        next_index += 1
        stack.append(node)
        on_stack.add(node)
        for target in sorted(adjacency[node]):
            if target not in indices:
                visit(target)
                lowlinks[node] = min(lowlinks[node], lowlinks[target])
            elif target in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[target])
        if lowlinks[node] == indices[node]:
            component: list[str] = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == node:
                    break
            components.append(sorted(component))

    for node in sorted(adjacency):
        if node not in indices:
            visit(node)
    return sorted(components, key=lambda component: (-len(component), component))


def _module_area(name: str) -> str:
    parts = name.split(".")
    return parts[1] if len(parts) > 1 else "(root)"


def _rank_counts(items: Iterable[tuple[str, int]], limit: int) -> list[dict[str, Any]]:
    return [
        {"name": name, "count": count}
        for name, count in sorted(items, key=lambda item: (-item[1], item[0]))[:limit]
    ]


def repository_metadata(root: Path, *, probe_lean: bool) -> dict[str, Any]:
    dirty_paths = set(filter(None, git(root, "diff", "--name-only", "HEAD").splitlines()))
    untracked = set(
        filter(None, git(root, "ls-files", "--others", "--exclude-standard").splitlines())
    )
    dirty_paths.update(untracked)
    library_dirty = sorted(
        path
        for path in dirty_paths
        if path == "NumStability.lean" or path.startswith("NumStability/")
    )
    commit = git(root, "rev-parse", "HEAD")
    commit_date = git(root, "show", "-s", "--format=%cI", "HEAD")
    lean_toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    lean_version = (
        run(("lake", "env", "lean", "--version"), cwd=root).stdout.strip()
        if probe_lean
        else None
    )
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(
        (package for package in manifest.get("packages", []) if package.get("name") == "mathlib"),
        {},
    )
    return {
        "commit": commit,
        "commit_date": commit_date,
        "branch": git(root, "branch", "--show-current"),
        "origin": git(root, "remote", "get-url", "origin"),
        "lean_toolchain": lean_toolchain,
        "lean_version": lean_version,
        "mathlib_revision": mathlib.get("rev"),
        "mathlib_input_revision": mathlib.get("inputRev"),
        "library_source_clean": not library_dirty,
        "library_source_dirty_paths": library_dirty,
    }


def extract_declarations(root: Path, *, build: bool, keep_tsv: Path | None) -> dict[str, Any]:
    if build:
        build_result = run(("lake", "build", "NumStability"), cwd=root)
        if build_result.stdout:
            print(build_result.stdout, end="", file=sys.stderr)
        if build_result.stderr:
            print(build_result.stderr, end="", file=sys.stderr)

    extractor = root / "tools" / "architecture" / "declaration_dependencies.lean"
    if keep_tsv is None:
        temporary = tempfile.NamedTemporaryFile(
            prefix="numstability-dependencies-", suffix=".tsv", delete=False
        )
        temporary.close()
        tsv_path = Path(temporary.name)
    else:
        tsv_path = keep_tsv.resolve()
        tsv_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        run(
            (
                "lake",
                "env",
                "lean",
                "--run",
                str(extractor),
                str(tsv_path),
            ),
            cwd=root,
        )
        return summarize_declaration_tsv(tsv_path)
    finally:
        if keep_tsv is None:
            tsv_path.unlink(missing_ok=True)


def summarize_declaration_tsv(path: Path) -> dict[str, Any]:
    names: list[str] = []
    modules: list[str] = []
    kinds: list[str] = []
    visibility: list[str] = []
    name_to_id: dict[str, int] = {}
    signature_edges: set[tuple[int, int]] = set()
    body_edges: set[tuple[int, int]] = set()
    extractor_format: int | None = None

    with path.open(encoding="utf-8") as stream:
        for line_number, raw_line in enumerate(stream, start=1):
            fields = raw_line.rstrip("\n\r").split("\t")
            if fields[:1] == ["format"]:
                if len(fields) == 2 and fields[1] in {"1", "2"}:
                    extractor_format = int(fields[1])
            elif fields[:1] == ["declaration"] and len(fields) == 5:
                name = fields[1]
                if name in name_to_id:
                    raise BaselineError(f"duplicate declaration in {path}:{line_number}: {name}")
                name_to_id[name] = len(names)
                names.append(name)
                modules.append(fields[2])
                kinds.append(fields[3])
                visibility.append(fields[4])
            elif fields[:1] == ["edge"] and len(fields) in {4, 6}:
                try:
                    edge = (name_to_id[fields[2]], name_to_id[fields[3]])
                except KeyError as error:
                    raise BaselineError(
                        f"edge precedes or references an unknown declaration at {path}:{line_number}"
                    ) from error
                if fields[1] == "signature":
                    signature_edges.add(edge)
                elif fields[1] == "body":
                    body_edges.add(edge)
                else:
                    raise BaselineError(f"unknown edge kind at {path}:{line_number}: {fields[1]}")
            else:
                raise BaselineError(f"malformed extractor output at {path}:{line_number}")
    if extractor_format is None:
        raise BaselineError(f"unsupported or missing extractor format marker in {path}")

    union_edges = signature_edges | body_edges
    body_only_edges = body_edges - signature_edges
    public = [item == "public" for item in visibility]
    incoming = [0] * len(names)
    outgoing = [0] * len(names)
    cross_incoming = [0] * len(names)
    signature_incoming = [0] * len(names)
    body_only_incoming = [0] * len(names)
    all_components = DisjointSet(len(names))
    public_components = DisjointSet(len(names))
    for source, target in union_edges:
        outgoing[source] += 1
        incoming[target] += 1
        if modules[source] != modules[target]:
            cross_incoming[target] += 1
        all_components.union(source, target)
        if public[source] and public[target]:
            public_components.union(source, target)
    for _, target in signature_edges:
        signature_incoming[target] += 1
    for _, target in body_only_edges:
        body_only_incoming[target] += 1

    declaration_ids_by_module: dict[str, list[int]] = collections.defaultdict(list)
    for declaration_id, module in enumerate(modules):
        declaration_ids_by_module[module].append(declaration_id)

    endpoint_modules = sorted(
        module
        for module, declaration_ids in declaration_ids_by_module.items()
        if all(cross_incoming[item] == 0 for item in declaration_ids)
    )
    all_leaf_modules = sorted(
        module
        for module, declaration_ids in declaration_ids_by_module.items()
        if all(incoming[item] == 0 for item in declaration_ids)
    )
    public_count = sum(public)
    largest_all = all_components.largest_component()
    largest_public = public_components.largest_component(public)

    visibility_counts = collections.Counter(visibility)
    kind_counts = collections.Counter(kinds)
    cross_signature_edges = sum(
        modules[source] != modules[target] for source, target in signature_edges
    )
    cross_body_edges = sum(modules[source] != modules[target] for source, target in body_edges)
    cross_body_only_edges = sum(
        modules[source] != modules[target] for source, target in body_only_edges
    )
    cross_union_edges = sum(modules[source] != modules[target] for source, target in union_edges)

    return {
        "format_version": extractor_format,
        "declaration_count": len(names),
        "module_count": len(declaration_ids_by_module),
        "visibility_counts": dict(sorted(visibility_counts.items())),
        "kind_counts": dict(sorted(kind_counts.items())),
        "edge_counts": {
            "signature": len(signature_edges),
            "body_or_proof": len(body_edges),
            "signature_and_body_overlap": len(signature_edges & body_edges),
            "body_or_proof_only": len(body_only_edges),
            "union": len(union_edges),
            "cross_module_signature": cross_signature_edges,
            "cross_module_body_or_proof": cross_body_edges,
            "cross_module_body_or_proof_only": cross_body_only_edges,
            "cross_module_union": cross_union_edges,
        },
        "graph_metrics": {
            "apparent_leaves_all": sum(value == 0 for value in incoming),
            "apparent_leaves_public": sum(
                public[item] and incoming[item] == 0 for item in range(len(names))
            ),
            "project_foundational_all": sum(value == 0 for value in outgoing),
            "project_isolated_all": sum(
                incoming[item] == 0 and outgoing[item] == 0 for item in range(len(names))
            ),
            "project_isolated_public": sum(
                public[item] and incoming[item] == 0 and outgoing[item] == 0
                for item in range(len(names))
            ),
            "public_referenced_somewhere": sum(
                public[item] and incoming[item] > 0 for item in range(len(names))
            ),
            "public_referenced_from_another_module": sum(
                public[item] and cross_incoming[item] > 0 for item in range(len(names))
            ),
            "public_referenced_from_signature": sum(
                public[item] and signature_incoming[item] > 0 for item in range(len(names))
            ),
            "public_referenced_only_from_body_or_proof": sum(
                public[item]
                and signature_incoming[item] == 0
                and body_only_incoming[item] > 0
                for item in range(len(names))
            ),
            "largest_weak_component_all": largest_all,
            "largest_weak_component_all_percentage": _percentage(largest_all, len(names)),
            "largest_weak_component_public": largest_public,
            "largest_weak_component_public_percentage": _percentage(
                largest_public, public_count
            ),
            "public_referenced_somewhere_percentage": _percentage(
                sum(public[item] and incoming[item] > 0 for item in range(len(names))),
                public_count,
            ),
            "public_cross_module_utilization_percentage": _percentage(
                sum(public[item] and cross_incoming[item] > 0 for item in range(len(names))),
                public_count,
            ),
        },
        "module_endpoint_metrics": {
            "modules_containing_declarations": len(declaration_ids_by_module),
            "modules_with_no_cross_module_consumers_count": len(endpoint_modules),
            "modules_with_no_cross_module_consumers_percentage": _percentage(
                len(endpoint_modules), len(declaration_ids_by_module)
            ),
            "modules_whose_declarations_are_all_apparent_leaves_count": len(all_leaf_modules),
            "modules_whose_declarations_are_all_apparent_leaves_percentage": _percentage(
                len(all_leaf_modules), len(declaration_ids_by_module)
            ),
            "modules_whose_declarations_are_all_apparent_leaves": all_leaf_modules,
        },
    }


def _percentage(numerator: int, denominator: int) -> float:
    return round(100.0 * numerator / denominator, 3) if denominator else 0.0


def render_markdown(data: dict[str, Any]) -> str:
    metadata = data["metadata"]
    source = data["source"]
    declarations = data.get("declarations")
    lines = [
        "# NumStability architecture baseline",
        "",
        "This file is generated by `tools/architecture/generate_baseline.py`. Do not edit it by hand.",
        "",
        "## Capture",
        "",
        f"- Commit: `{metadata['commit']}`",
        f"- Commit date: `{metadata['commit_date']}`",
        f"- Branch: `{metadata['branch']}`",
        f"- Origin: `{metadata['origin']}`",
        f"- Lean: `{metadata['lean_toolchain']}`",
        f"- Mathlib revision: `{metadata['mathlib_revision']}`",
        f"- Library source clean at capture: `{str(metadata['library_source_clean']).lower()}`",
    ]
    if metadata["library_source_dirty_paths"]:
        lines.extend(
            [
                "- Dirty library paths included in this worktree capture:",
                *[f"  - `{path}`" for path in metadata["library_source_dirty_paths"]],
            ]
        )
    lines.extend(
        [
            "",
            "## Source and import graph",
            "",
            "| Measure | Result |",
            "| --- | ---: |",
            f"| Lean modules | {source['module_count']:,} |",
            f"| Source lines | {source['line_count']:,} |",
            f"| Nonblank source lines | {source['nonblank_line_count']:,} |",
            f"| Direct imports | {source['direct_import_count']:,} |",
            f"| Internal direct-import edges | {source['internal_direct_import_count']:,} |",
            f"| External direct imports | {source['external_direct_import_count']:,} |",
            f"| Import cycles | {source['import_graph']['cyclic_strong_component_count']:,} |",
            f"| Modules with a module docstring | {source['module_docstring_count']:,} |",
            f"| Modules missing a module docstring | {source['modules_missing_module_docstring_count']:,} |",
            "",
            "### Largest source modules",
            "",
            "| Module | Lines | Nonblank lines |",
            "| --- | ---: | ---: |",
        ]
    )
    for module in source["largest_modules"][:15]:
        lines.append(
            f"| `{module['module']}` | {module['lines']:,} | {module['nonblank_lines']:,} |"
        )
    lines.extend(
        [
            "",
            "### Import fan-in",
            "",
            "| Module | Direct project consumers |",
            "| --- | ---: |",
        ]
    )
    for item in source["import_graph"]["top_fan_in"][:15]:
        lines.append(f"| `{item['name']}` | {item['count']:,} |")

    tier_audit = source.get("tier_audit")
    if tier_audit is not None:
        lines.extend(
            [
                "",
                "## Executable tier audit",
                "",
                f"Manifest: `{tier_audit['manifest']}`",
                "",
                "| Measure | Result |",
                "| --- | ---: |",
                f"| Classified modules | {tier_audit['classified_module_count']:,} |",
                f"| Unclassified modules | {tier_audit['unclassified_module_count']:,} |",
                f"| Classification coverage | {tier_audit['classification_coverage_percentage']:.3f}% |",
                f"| Classified import edges | {tier_audit['classified_import_edge_count']:,} |",
                f"| Forbidden reusable-to-source edges | {tier_audit['reusable_to_source_edge_count']:,} |",
                f"| Forbidden reusable-to-mixed edges | {tier_audit['reusable_to_mixed_edge_count']:,} |",
                f"| Reusable/source reachable pairs | {tier_audit['reusable_to_source_reachability_count']:,} |",
                f"| Reusable/mixed reachable pairs | {tier_audit['reusable_to_mixed_reachability_count']:,} |",
                f"| Classification complete | `{str(tier_audit['classification_complete']).lower()}` |",
                f"| Tier separation complete (100% classified and no `mixed` modules) | `{str(tier_audit['tier_separation_complete']).lower()}` |",
                f"| Physical source-target gate satisfied | `{str(tier_audit['physical_source_target_gate_satisfied']).lower()}` |",
                "",
                "A zero forbidden-edge count is conclusive only at 100% classification coverage "
                "with no mixed modules. The full unclassified queue and tier-edge matrix are retained in JSON.",
            ]
        )
        lines.extend(
            [
                "",
                "### Classified modules by role",
                "",
                "| Role | Modules |",
                "| --- | ---: |",
                *[
                    f"| `{tier}` | {tier_audit['module_counts_by_tier'][tier]:,} |"
                    for tier in sorted(tier_audit["module_counts_by_tier"])
                ],
            ]
        )
        if tier_audit["forbidden_reusable_edges"]:
            lines.extend(
                [
                    "",
                    "### Forbidden classified edges",
                    "",
                    *[
                        f"- `{edge['source']}` imports `{edge['target']}` ({edge['target_tier']})"
                        for edge in tier_audit["forbidden_reusable_edges"]
                    ],
                ]
            )
        reachable = [
            *(
                {**item, "target_tier": "source"}
                for item in tier_audit["reusable_to_source_paths"]
            ),
            *(
                {**item, "target_tier": "mixed"}
                for item in tier_audit["reusable_to_mixed_paths"]
            ),
        ]
        if reachable:
            lines.extend(
                [
                    "",
                    "### Forbidden reachable dependencies",
                    "",
                    *[
                        f"- `{item['source']}` reaches `{item['target']}` ({item['target_tier']}) via "
                        + " -> ".join(f"`{module}`" for module in item["path"])
                        for item in reachable[:50]
                    ],
                ]
            )

    if declarations is None:
        lines.extend(
            [
                "",
                "## Compiled declaration graph",
                "",
                "Not captured (`--skip-declarations`).",
            ]
        )
    else:
        edges = declarations["edge_counts"]
        graph = declarations["graph_metrics"]
        endpoints = declarations["module_endpoint_metrics"]
        public_count = declarations["visibility_counts"].get("public", 0)
        lines.extend(
            [
                "",
                "## Compiled declaration graph",
                "",
                "An edge `A → B` means that the elaborated signature or body/proof of `A` directly references `B`.",
                "Signature edges and body/proof edges are reported separately; their union is used for leaf and connectivity metrics.",
                "",
                "| Measure | Result |",
                "| --- | ---: |",
                f"| Uniquely owned declarations | {declarations['declaration_count']:,} |",
                f"| Public declarations | {public_count:,} |",
                f"| Signature edges | {edges['signature']:,} |",
                f"| Body/proof edges | {edges['body_or_proof']:,} |",
                f"| Body/proof-only edges | {edges['body_or_proof_only']:,} |",
                f"| Union edges | {edges['union']:,} |",
                f"| Cross-module signature edges | {edges['cross_module_signature']:,} |",
                f"| Cross-module body/proof-only edges | {edges['cross_module_body_or_proof_only']:,} |",
                f"| Cross-module union edges | {edges['cross_module_union']:,} |",
                f"| Apparent public leaves | {graph['apparent_leaves_public']:,} |",
                f"| Public isolated declarations | {graph['project_isolated_public']:,} |",
                f"| Largest weak component, all declarations | {graph['largest_weak_component_all_percentage']:.3f}% |",
                f"| Largest weak component, public declarations | {graph['largest_weak_component_public_percentage']:.3f}% |",
                f"| Public declarations referenced somewhere | {graph['public_referenced_somewhere_percentage']:.3f}% |",
                f"| Public declarations referenced from another module | {graph['public_cross_module_utilization_percentage']:.3f}% |",
                f"| Public declarations referenced only from a body/proof | {graph['public_referenced_only_from_body_or_proof']:,} |",
                "",
                "### Module endpoints",
                "",
                f"Of {endpoints['modules_containing_declarations']:,} modules containing declarations, "
                f"{endpoints['modules_with_no_cross_module_consumers_count']:,} have no declaration consumed from another module. "
                f"In {endpoints['modules_whose_declarations_are_all_apparent_leaves_count']:,} modules, every declaration is an apparent leaf.",
            ]
        )
        if endpoints["modules_whose_declarations_are_all_apparent_leaves"]:
            lines.extend(
                [
                    "",
                    *[
                        f"- `{module}`"
                        for module in endpoints[
                            "modules_whose_declarations_are_all_apparent_leaves"
                        ]
                    ],
                ]
            )

    lines.extend(
        [
            "",
            "## Interpretation guardrails",
            "",
            "- An apparent leaf or endpoint is a review candidate, not evidence that code is dead or should be deleted.",
            "- Cross-module utilization is not a target to maximize: splitting a file can raise it without improving reuse.",
            "- The signature graph is the better indicator of conceptual API coupling; body/proof-only edges mostly describe implementation coupling.",
            "- Weak-component coverage measures connectedness, not quality or reuse.",
            "- Source imports describe build architecture, while declaration edges describe elaborated logical dependencies. Both are needed.",
            "",
        ]
    )
    return "\n".join(lines)


def write_output(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8", newline="\n")


def check_capture(json_path: Path, markdown_path: Path, current: dict[str, Any]) -> bool:
    """Check stable measurements without treating capture-time Git data as stable."""

    if not json_path.is_file() or not markdown_path.is_file():
        print(f"missing committed baseline pair: {json_path}, {markdown_path}", file=sys.stderr)
        return False
    try:
        raw_json = json_path.read_text(encoding="utf-8")
        committed = json.loads(raw_json)
    except (OSError, json.JSONDecodeError) as error:
        print(f"invalid committed baseline {json_path}: {error}", file=sys.stderr)
        return False

    okay = True
    canonical_json = (
        json.dumps(committed, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    )
    if raw_json != canonical_json:
        print(f"non-canonical JSON formatting: {json_path}", file=sys.stderr)
        okay = False

    for key in ("schema_version", "source", "declarations"):
        if committed.get(key) != current.get(key):
            print(f"out of date baseline field `{key}`: {json_path}", file=sys.stderr)
            okay = False
    for key in ("lean_toolchain", "mathlib_revision"):
        if committed.get("metadata", {}).get(key) != current.get("metadata", {}).get(key):
            print(f"out of date baseline metadata `{key}`: {json_path}", file=sys.stderr)
            okay = False

    try:
        expected_markdown = render_markdown(committed)
        actual_markdown = markdown_path.read_text(encoding="utf-8")
    except (KeyError, OSError, TypeError) as error:
        print(f"cannot render committed baseline pair: {error}", file=sys.stderr)
        return False
    if actual_markdown != expected_markdown:
        print(f"Markdown does not match committed JSON: {markdown_path}", file=sys.stderr)
        okay = False
    return okay


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("docs/architecture/baselines"),
        help="output directory relative to the repository root",
    )
    parser.add_argument(
        "--name",
        default=dt.date.today().isoformat(),
        help="baseline filename stem (default: today's ISO date)",
    )
    parser.add_argument(
        "--skip-declarations",
        action="store_true",
        help="generate only source and import metrics",
    )
    parser.add_argument(
        "--strict-source",
        action="store_true",
        help=(
            "require the tier manifest and fail on unresolved imports, cycles, "
            "or reusable-to-source/mixed reachability"
        ),
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="do not run `lake build NumStability` before inspecting oleans",
    )
    parser.add_argument(
        "--keep-dependency-tsv",
        type=Path,
        help="retain the extractor's potentially large raw TSV at this path",
    )
    parser.add_argument(
        "--dependency-tsv",
        type=Path,
        help="summarize an existing extractor TSV instead of running Lean again",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify stable measurements and the committed JSON/Markdown pair",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv or sys.argv[1:])
    root = Path(__file__).resolve().parents[2]
    os.chdir(root)
    try:
        metadata = repository_metadata(root, probe_lean=not args.skip_declarations)
        source, modules = scan_sources(root)
        tier_audit = audit_tiers(root, modules)
        if tier_audit is not None:
            source["tier_audit"] = tier_audit
        if args.strict_source:
            failures: list[str] = []
            if tier_audit is None:
                failures.append("missing docs/architecture/tiers.json")
            unresolved = source["unresolved_project_import_count"]
            cycles = source["import_graph"]["cyclic_strong_component_count"]
            if unresolved:
                failures.append(f"{unresolved} unresolved project import(s)")
            if cycles:
                failures.append(f"{cycles} cyclic import component(s)")
            if tier_audit and tier_audit["forbidden_reusable_reachability_count"]:
                failures.append(
                    f"{tier_audit['forbidden_reusable_reachability_count']} "
                    "classified reusable-to-source/mixed reachable pair(s)"
                )
            if failures:
                raise BaselineError("source graph check failed: " + "; ".join(failures))
        declarations = None
        if not args.skip_declarations:
            if args.dependency_tsv is not None:
                declarations = summarize_declaration_tsv(args.dependency_tsv.resolve())
            else:
                declarations = extract_declarations(
                    root,
                    build=not args.no_build,
                    keep_tsv=args.keep_dependency_tsv,
                )
        data = {
            "schema_version": SCHEMA_VERSION,
            "metadata": metadata,
            "source": source,
            "declarations": declarations,
        }
        output_dir = args.output_dir
        if not output_dir.is_absolute():
            output_dir = root / output_dir
        json_path = output_dir / f"{args.name}.json"
        markdown_path = output_dir / f"{args.name}.md"
        if args.check:
            okay = check_capture(json_path, markdown_path, data)
        else:
            json_content = json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
            markdown_content = render_markdown(data)
            write_output(json_path, json_content)
            write_output(markdown_path, markdown_content)
            okay = True
            for path in (json_path, markdown_path):
                try:
                    print(path.relative_to(root))
                except ValueError:
                    print(path)
        return 0 if okay else 1
    except BaselineError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
