#!/usr/bin/env python3
"""Summarize the predeclared NumStability public-consumer probes.

Schema: numstability-public-api-probes/v1.  This script never touches the
isolated source tree; all outputs are written beside this script.
"""

from __future__ import annotations

import csv
import gzip
import hashlib
import json
import math
import re
from collections import defaultdict, deque
from datetime import datetime, timezone
from pathlib import Path


AUDIT_ROOT = Path(
    "<library-repo>/"
    "tmp/library_audit/higham_v01-045daf2"
)
WORKTREE = AUDIT_ROOT / "_worktree"
PROBES = AUDIT_ROOT / "probes"
STATIC = AUDIT_ROOT / "static_architecture"
SCHEMA_VERSION = "numstability-public-api-probes/v1"
COMMIT = "045daf28056a6e4358d5de7c22c7a9d7acc2e80e"


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_real_seconds(status_row: dict[str, str]) -> float:
    time_field = status_row["time_log"]
    path = Path(status_row["stdout_stderr_log"] if time_field == "embedded_in_stdout_log" else time_field)
    text = path.read_text(encoding="utf-8")
    matches = re.findall(r"^real\s+([0-9.]+)\s*$", text, flags=re.MULTILINE)
    if not matches:
        raise ValueError(f"no real timing in {path}")
    return float(matches[-1])


def nearest_rank(values: list[float], probability: float) -> float:
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def closure(start: str, adjacency: dict[str, set[str]]) -> set[str]:
    seen = {start}
    queue: deque[str] = deque([start])
    while queue:
        current = queue.popleft()
        for target in adjacency.get(current, set()):
            if target not in seen:
                seen.add(target)
                queue.append(target)
    return seen


def has_adjacent_docstring(lines: list[str], declaration_line: int) -> bool:
    """Conservative source check for a `/-- ... -/` immediately above a declaration."""
    index = declaration_line - 2
    while index >= 0 and not lines[index].strip():
        index -= 1
    if index < 0 or not lines[index].rstrip().endswith("-/"):
        return False
    while index >= 0:
        stripped = lines[index].lstrip()
        if stripped.startswith("/--"):
            return True
        if re.match(r"^(def|abbrev|structure|class|theorem|lemma|opaque|axiom|inductive)\b", stripped):
            return False
        index -= 1
    return False


manifest = read_csv(PROBES / "PREDECLARED_SAMPLE.csv")
metadata = {row["probe_id"]: row for row in read_csv(PROBES / "PROBE_METADATA.csv")}

declarations_artifact = AUDIT_ROOT / "raw" / "declarations.csv.gz"
with gzip.open(declarations_artifact, "rt", newline="", encoding="utf-8") as handle:
    environment_declarations = {row["name"]: row for row in csv.DictReader(handle)}

# run_status.tsv is tab-delimited.
with (PROBES / "run_status.tsv").open(newline="", encoding="utf-8") as handle:
    status_rows = list(csv.DictReader(handle, delimiter="\t"))
status_by_key = {(row["stem"][:3], row["phase"]): row for row in status_rows}

with (PROBES / "run_commands.tsv").open(newline="", encoding="utf-8") as handle:
    command_rows = list(csv.DictReader(handle, delimiter="\t"))
command_by_key = {(row["stem"][:3], row["phase"]): row["command"] for row in command_rows}

import_rows = read_csv(STATIC / "source_imports.csv")
adjacency: dict[str, set[str]] = defaultdict(set)
for row in import_rows:
    if row["is_project_module"].lower() == "true":
        adjacency[row["importer_module"]].add(row["imported_module"])

compatibility_modules = set()
compatibility_path = STATIC / "compatibility_shim_candidates.csv"
if compatibility_path.exists():
    compatibility_rows = read_csv(compatibility_path)
    for row in compatibility_rows:
        module = row.get("module") or row.get("module_name")
        if module:
            compatibility_modules.add(module)

direct_dependencies_artifact = AUDIT_ROOT / "raw" / "direct_dependencies.csv.gz"
selected_name_to_probe = {row["declaration"]: row["probe_id"] for row in manifest}
type_edges_by_source: dict[str, list[dict[str, str]]] = defaultdict(list)
selected_type_edge_rows: list[dict[str, str]] = []
with gzip.open(direct_dependencies_artifact, "rt", newline="", encoding="utf-8") as handle:
    for edge in csv.DictReader(handle):
        if (
            edge["source"] in selected_name_to_probe
            and edge["target_scope"] == "project"
            and edge["occurs_in_type"] == "true"
        ):
            target_meta = environment_declarations[edge["target"]]
            enriched = {
                "probe_id": selected_name_to_probe[edge["source"]],
                **edge,
                "target_kind": target_meta["kind"],
                "target_is_internal": target_meta["is_internal"],
                "target_is_private": target_meta["is_private"],
                "target_has_body": target_meta["has_body"],
                "target_is_source_layer": str(edge["target_module"].startswith("NumStability.Source")).lower(),
                "target_module_is_static_compatibility_candidate": str(edge["target_module"] in compatibility_modules).lower(),
            }
            type_edges_by_source[edge["source"]].append(enriched)
            selected_type_edge_rows.append(enriched)

closure_rows: list[dict[str, object]] = []
result_rows: list[dict[str, object]] = []
check_times: list[float] = []
client_times: list[float] = []

for sample in manifest:
    probe_id = sample["probe_id"]
    meta = metadata[probe_id]
    env_row = environment_declarations[sample["declaration"]]
    check = status_by_key[(probe_id, "check")]
    client = status_by_key[(probe_id, "client")]
    check_time = parse_real_seconds(check)
    client_time = parse_real_seconds(client)
    check_times.append(check_time)
    client_times.append(client_time)

    source_path = WORKTREE / sample["source_file"]
    source_lines = source_path.read_text(encoding="utf-8").splitlines()
    source_line = int(sample["source_line"])
    short_name = sample["declaration"].split(".")[-1]
    source_line_validated = 1 <= source_line <= len(source_lines) and short_name in source_lines[source_line - 1]
    declaration_line_text = source_lines[source_line - 1].strip() if 1 <= source_line <= len(source_lines) else ""
    adjacent_docstring = has_adjacent_docstring(source_lines, source_line)

    check_log = Path(check["stdout_stderr_log"])
    client_log = Path(client["stdout_stderr_log"])
    check_text = check_log.read_text(encoding="utf-8")
    check_olean = Path(check["output_olean"])
    check_ilean = Path(check["output_ilean"])
    client_olean = Path(client["output_olean"])
    client_ilean = Path(client["output_ilean"])
    visibility_pass = (
        int(check["exit_status"]) == 0
        and sample["declaration"] in check_text
        and check_olean.exists()
        and check_ilean.exists()
    )
    client_pass = (
        int(client["exit_status"]) == 0
        and client_olean.exists()
        and client_ilean.exists()
    )

    imported_closure = closure(sample["narrow_import"], adjacency)
    source_closure = sorted(m for m in imported_closure if m.startswith("NumStability.Source"))
    is_compatibility = sample["narrow_import"] in compatibility_modules
    type_edges = type_edges_by_source[sample["declaration"]]
    private_internal_type_targets = sum(
        edge["target_is_internal"] == "true" or edge["target_is_private"] == "true"
        for edge in type_edges
    )
    source_layer_type_targets = sum(edge["target_is_source_layer"] == "true" for edge in type_edges)
    compatibility_type_targets = sum(
        edge["target_module_is_static_compatibility_candidate"] == "true" for edge in type_edges
    )
    closure_rows.append(
        {
            "probe_id": probe_id,
            "narrow_import": sample["narrow_import"],
            "reachable_project_modules_including_import": len(imported_closure),
            "reachable_source_modules": len(source_closure),
            "source_modules": ";".join(source_closure),
            "direct_project_imports": len(adjacency.get(sample["narrow_import"], set())),
            "static_compatibility_candidate": str(is_compatibility).lower(),
            "semantics": "Static source-import transitive closure; not elaborated declaration reachability.",
        }
    )

    check_src = PROBES / "src" / f"{check['stem']}.lean"
    client_src = PROBES / "src" / f"{client['stem']}.lean"
    result_rows.append(
        {
            **sample,
            "authorship_classification": "source_written_by_exact_source_inspection",
            "environment_visibility_evidence": "independent narrow-import #check",
            "environment_kind": env_row["kind"],
            "environment_is_internal": env_row["is_internal"],
            "environment_is_private": env_row["is_private"],
            "environment_has_body": env_row["has_body"],
            "environment_type_direct_count_all_scopes": env_row["type_direct_count"],
            "environment_body_direct_count_all_scopes": env_row["body_direct_count"],
            "source_line_validated": str(source_line_validated).lower(),
            "source_declaration_line_text": declaration_line_text,
            "has_adjacent_source_docstring": str(adjacent_docstring).lower(),
            "source_import_closure_count": len(imported_closure),
            "source_layer_modules_in_closure": len(source_closure),
            "compatibility_candidate_module": str(is_compatibility).lower(),
            "direct_project_type_dependency_count": len(type_edges),
            "direct_private_or_internal_type_dependency_count": private_internal_type_targets,
            "direct_source_layer_type_dependency_count": source_layer_type_targets,
            "direct_static_compatibility_type_dependency_count": compatibility_type_targets,
            "check_status": "pass" if visibility_pass else "fail",
            "check_exit_status": check["exit_status"],
            "check_real_seconds": f"{check_time:.2f}",
            "check_fresh_output": check["fresh_output"],
            "check_command": command_by_key[(probe_id, "check")],
            "check_source": str(check_src),
            "check_source_sha256": sha256(check_src),
            "check_log": str(check_log),
            "check_log_sha256": sha256(check_log),
            "check_olean": str(check_olean),
            "check_olean_sha256": sha256(check_olean) if check_olean.exists() else "",
            "client_status": "pass" if client_pass else "fail",
            "client_exit_status": client["exit_status"],
            "client_real_seconds": f"{client_time:.2f}",
            "client_fresh_output": client["fresh_output"],
            "client_command": command_by_key[(probe_id, "client")],
            "client_source": str(client_src),
            "client_source_sha256": sha256(client_src),
            "client_log": str(client_log),
            "client_log_sha256": sha256(client_log),
            "client_olean": str(client_olean),
            "client_olean_sha256": sha256(client_olean) if client_olean.exists() else "",
            "dependency_cache_class": "fresh probe output; cached isolated-worktree imported dependencies",
            "required_namespace_or_qualification": meta["required_namespace_or_qualification"],
            "assumptions_and_typeclasses": meta["assumptions_and_typeclasses"],
            "helper_lemmas_or_client_steps": meta["helper_lemmas_or_client_steps"],
            "normalized_statement": meta["normalized_statement"],
            "observed_friction": meta["observed_friction"],
            "friction_level": meta["friction_level"],
        }
    )

result_path = PROBES / "results.csv"
with result_path.open("w", newline="", encoding="utf-8") as handle:
    writer = csv.DictWriter(handle, fieldnames=list(result_rows[0]))
    writer.writeheader()
    writer.writerows(result_rows)

selected_environment_path = PROBES / "selected_declaration_environment_metadata.csv"
selected_environment_rows = [environment_declarations[row["declaration"]] for row in manifest]
with selected_environment_path.open("w", newline="", encoding="utf-8") as handle:
    writer = csv.DictWriter(handle, fieldnames=list(selected_environment_rows[0]))
    writer.writeheader()
    writer.writerows(selected_environment_rows)

selected_type_edges_path = PROBES / "selected_api_direct_project_type_dependencies.csv"
with selected_type_edges_path.open("w", newline="", encoding="utf-8") as handle:
    writer = csv.DictWriter(handle, fieldnames=list(selected_type_edge_rows[0]))
    writer.writeheader()
    writer.writerows(sorted(selected_type_edge_rows, key=lambda row: (row["probe_id"], row["target"])))

closure_path = PROBES / "narrow_import_closure.csv"
with closure_path.open("w", newline="", encoding="utf-8") as handle:
    writer = csv.DictWriter(handle, fieldnames=list(closure_rows[0]))
    writer.writeheader()
    writer.writerows(closure_rows)

# Compact excerpt of public roots and two misleadingly broad domain umbrellas.
entry_rows = read_csv(STATIC / "entry_points.csv")
entry_by_module = {row["module"]: row for row in entry_rows}
entry_modules = [
    "NumStability",
    "NumStability.Core",
    "NumStability.FloatingPoint",
    "NumStability.Analysis",
    "NumStability.Algorithms",
    "NumStability.Source",
    "NumStability.Source.Higham",
    "NumStability.All",
    "NumStability.Higham",
    "NumStability.Algorithms.Summation",
    "NumStability.Algorithms.LinearSystems.LeastSquares",
]
entry_excerpt: list[dict[str, str]] = []
for module in entry_modules:
    row = entry_by_module.get(module)
    if row is None:
        continue
    entry_excerpt.append(
        {
            "module": module,
            "entry_kind": row["entry_kind"],
            "declaration_free_static": row["declaration_free_static"],
            "compatibility_candidate_static": row["compatibility_candidate_static"],
            "direct_internal_import_count": row["direct_internal_import_count"],
            "reachable_project_module_count_including_entry": row["reachable_project_module_count_including_entry"],
            "reachable_declaration_bearing_module_count_including_entry": row["reachable_declaration_bearing_module_count_including_entry"],
            "reachable_static_declaration_starter_count": row["reachable_static_declaration_starter_count"],
            "reachable_Source_modules": row["reachable_Source_modules"],
            "reachability_semantics": row["reachability_semantics"],
        }
    )
with (PROBES / "entrypoint_reachability_excerpt.csv").open("w", newline="", encoding="utf-8") as handle:
    writer = csv.DictWriter(handle, fieldnames=list(entry_excerpt[0]))
    writer.writeheader()
    writer.writerows(entry_excerpt)

visibility_passes = sum(row["check_status"] == "pass" for row in result_rows)
client_passes = sum(row["client_status"] == "pass" for row in result_rows)
source_clean = sum(row["source_layer_modules_in_closure"] == 0 for row in result_rows)
source_line_passes = sum(row["source_line_validated"] == "true" for row in result_rows)
documented = sum(row["has_adjacent_source_docstring"] == "true" for row in result_rows)
noncompat = sum(row["compatibility_candidate_module"] == "false" for row in result_rows)
environment_public = sum(
    row["environment_is_internal"] == "false" and row["environment_is_private"] == "false"
    for row in result_rows
)
with_bodies = sum(row["environment_has_body"] == "true" for row in result_rows)
type_edge_count = len(selected_type_edge_rows)
type_edges_nonprivate = sum(
    row["target_is_internal"] == "false" and row["target_is_private"] == "false"
    for row in selected_type_edge_rows
)
type_edges_nonsource = sum(row["target_is_source_layer"] == "false" for row in selected_type_edge_rows)
type_edges_noncompat = sum(
    row["target_module_is_static_compatibility_candidate"] == "false"
    for row in selected_type_edge_rows
)
clean_type_surfaces = sum(
    row["direct_private_or_internal_type_dependency_count"] == 0
    and row["direct_source_layer_type_dependency_count"] == 0
    and row["direct_static_compatibility_type_dependency_count"] == 0
    for row in result_rows
)
n = len(result_rows)

summary = {
    "schema_version": SCHEMA_VERSION,
    "commit": COMMIT,
    "generated_utc": datetime.now(timezone.utc).isoformat(),
    "mode": "audit_read_only",
    "sample": {
        "selection": "predeclared stratified canonical public sample",
        "declaration_universe": "15 exact source-inspected declarations outside Source/Higham, private/internal, generated, and static compatibility-candidate modules",
        "count": n,
        "manifest": str(PROBES / "PREDECLARED_SAMPLE.csv"),
        "manifest_sha256": sha256(PROBES / "PREDECLARED_SAMPLE.csv"),
    },
    "headline_metrics": {
        "visibility_success": {
            "numerator": visibility_passes,
            "denominator": n,
            "percentage": 100.0 * visibility_passes / n,
            "formula": "passing independent #check compilations / predeclared probes",
            "raw_artifact": str(result_path),
            "raw_column": "check_status",
        },
        "client_theorem_success": {
            "numerator": client_passes,
            "denominator": n,
            "percentage": 100.0 * client_passes / n,
            "formula": "passing fresh-output client theorem compilations / predeclared probes",
            "raw_artifact": str(result_path),
            "raw_column": "client_status",
        },
        "source_free_narrow_import_closure": {
            "numerator": source_clean,
            "denominator": n,
            "percentage": 100.0 * source_clean / n,
            "formula": "probe imports whose static transitive source-import closure contains zero NumStability.Source modules / predeclared imports",
            "raw_artifact": str(closure_path),
            "raw_column": "reachable_source_modules",
        },
        "exact_source_line_validation": {
            "numerator": source_line_passes,
            "denominator": n,
            "percentage": 100.0 * source_line_passes / n,
            "formula": "manifest source lines containing the exact declaration basename / predeclared declarations",
            "raw_artifact": str(result_path),
            "raw_column": "source_line_validated",
        },
        "outside_static_compatibility_candidates": {
            "numerator": noncompat,
            "denominator": n,
            "percentage": 100.0 * noncompat / n,
            "formula": "owning imports absent from static compatibility-candidate module set / predeclared imports",
            "raw_artifact": str(result_path),
            "raw_column": "compatibility_candidate_module",
        },
        "selected_declarations_with_adjacent_docstrings": {
            "numerator": documented,
            "denominator": n,
            "percentage": 100.0 * documented / n,
            "formula": "selected declaration introducers with a conservatively detected immediately preceding /-- docstring / predeclared declarations",
            "raw_artifact": str(result_path),
            "raw_column": "has_adjacent_source_docstring",
        },
        "compiled_environment_public": {
            "numerator": environment_public,
            "denominator": n,
            "percentage": 100.0 * environment_public / n,
            "formula": "selected environment declarations with is_internal=false and is_private=false / predeclared declarations",
            "raw_artifact": str(selected_environment_path),
            "raw_columns": ["is_internal", "is_private"],
        },
        "selected_declarations_with_bodies": {
            "numerator": with_bodies,
            "denominator": n,
            "percentage": 100.0 * with_bodies / n,
            "formula": "selected environment declarations with has_body=true / predeclared declarations",
            "raw_artifact": str(selected_environment_path),
            "raw_column": "has_body",
        },
        "selected_type_surfaces_without_private_internal_source_or_compat_targets": {
            "numerator": clean_type_surfaces,
            "denominator": n,
            "percentage": 100.0 * clean_type_surfaces / n,
            "formula": "selected declaration types with zero direct project targets that are private, internal, Source-layer, or static compatibility candidates / predeclared declarations",
            "raw_artifact": str(result_path),
            "raw_columns": [
                "direct_private_or_internal_type_dependency_count",
                "direct_source_layer_type_dependency_count",
                "direct_static_compatibility_type_dependency_count"
            ],
        },
        "direct_project_type_edges_to_public_targets": {
            "numerator": type_edges_nonprivate,
            "denominator": type_edge_count,
            "percentage": 100.0 * type_edges_nonprivate / type_edge_count,
            "formula": "direct project type-dependency rows whose target has is_internal=false and is_private=false / all selected direct project type-dependency rows",
            "raw_artifact": str(selected_type_edges_path),
            "raw_columns": ["target_is_internal", "target_is_private"],
        },
        "direct_project_type_edges_outside_source_layer": {
            "numerator": type_edges_nonsource,
            "denominator": type_edge_count,
            "percentage": 100.0 * type_edges_nonsource / type_edge_count,
            "formula": "direct project type-dependency rows whose target module is outside NumStability.Source / all selected direct project type-dependency rows",
            "raw_artifact": str(selected_type_edges_path),
            "raw_column": "target_is_source_layer",
        },
        "direct_project_type_edges_outside_static_compatibility_modules": {
            "numerator": type_edges_noncompat,
            "denominator": type_edge_count,
            "percentage": 100.0 * type_edges_noncompat / type_edge_count,
            "formula": "direct project type-dependency rows whose target module is not a static compatibility candidate / all selected direct project type-dependency rows",
            "raw_artifact": str(selected_type_edges_path),
            "raw_column": "target_module_is_static_compatibility_candidate",
        },
    },
    "timing": {
        "classification": "fresh probe outputs; cached imported dependencies; not clean library compilation",
        "check_seconds": {
            "min": min(check_times),
            "median_nearest_rank": nearest_rank(check_times, 0.5),
            "p95_nearest_rank": nearest_rank(check_times, 0.95),
            "max": max(check_times),
            "sum": sum(check_times),
        },
        "client_seconds": {
            "min": min(client_times),
            "median_nearest_rank": nearest_rank(client_times, 0.5),
            "p95_nearest_rank": nearest_rank(client_times, 0.95),
            "max": max(client_times),
            "sum": sum(client_times),
        },
        "percentile_definition": "nearest-rank: sorted[ceil(p*n)-1]",
    },
    "validation": {
        "known_visible_check_exit": 0,
        "known_visible_bad_client_exit": 1,
        "interpretation": "The harness distinguishes visibility from an ill-typed external theorem.",
        "raw_artifact": str(PROBES / "VALIDATION_RESULTS.csv"),
    },
    "evidence_dependencies": {
        "source_import_graph": str(STATIC / "source_imports.csv"),
        "source_import_graph_sha256": sha256(STATIC / "source_imports.csv"),
        "entrypoint_metrics": str(STATIC / "entry_points.csv"),
        "entrypoint_metrics_sha256": sha256(STATIC / "entry_points.csv"),
        "compatibility_candidates": str(compatibility_path),
        "compatibility_candidates_sha256": sha256(compatibility_path),
        "compiled_declaration_metadata": str(declarations_artifact),
        "compiled_declaration_metadata_sha256": sha256(declarations_artifact),
        "compiled_direct_dependencies": str(direct_dependencies_artifact),
        "compiled_direct_dependencies_sha256": sha256(direct_dependencies_artifact),
    },
    "limitations": [
        "The stratified sample is not random and does not estimate library-wide public API success.",
        "A successful #check proves visibility only.",
        "A successful client theorem proves usability only for that exact import, statement, assumptions, and Lean environment.",
        "Static source-import closure is not an elaborated logical dependency or declaration-visibility graph.",
        "The client examples mostly forward a declared theorem; they test importability, name resolution, parameter elaboration, and stated assumptions, not ergonomic proof discovery from scratch.",
    ],
}

with (PROBES / "summary.json").open("w", encoding="utf-8") as handle:
    json.dump(summary, handle, indent=2, sort_keys=True)
    handle.write("\n")

# Hash every stable probe artifact except the checksum file itself and build
# outputs' Apple metadata, if any. Re-running after report edits refreshes it.
checksum_path = PROBES / "SHA256SUMS"
files = sorted(
    path for path in PROBES.rglob("*")
    if path.is_file() and path != checksum_path and path.name != ".DS_Store"
)
with checksum_path.open("w", encoding="utf-8") as handle:
    for path in files:
        handle.write(f"{sha256(path)}  {path.relative_to(PROBES)}\n")

print(json.dumps({
    "schema_version": SCHEMA_VERSION,
    "probes": n,
    "visibility_passes": visibility_passes,
    "client_passes": client_passes,
    "source_free_imports": source_clean,
    "source_line_validations": source_line_passes,
    "noncompat_imports": noncompat,
    "adjacent_docstrings": documented,
    "environment_public": environment_public,
    "with_bodies": with_bodies,
    "direct_project_type_edges": type_edge_count,
    "clean_type_surfaces": clean_type_surfaces,
}, sort_keys=True))
