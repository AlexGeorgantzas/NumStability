#!/usr/bin/env python3
"""Audit direct project declarations exposed by public source-written types.

Edge orientation is consumer -> dependency.  This add-on is deliberately
limited to direct elaborated type edges; it does not infer that a flagged edge
is an API defect.
"""

from __future__ import annotations

import csv
import gzip
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path


SCHEMA_VERSION = "numstability-public-type-exposure/1.0.0"
CANONICAL_LAYERS = {"Algorithms", "Analysis", "FloatingPoint"}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read_csv(path: Path, *, compressed: bool = False) -> list[dict[str, str]]:
    opener = gzip.open if compressed else open
    with opener(path, "rt", encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream))


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, object]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def transitive_closure(graph: dict[str, set[str]], start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        node = stack.pop()
        for target in graph.get(node, set()):
            if target not in seen:
                seen.add(target)
                stack.append(target)
    return seen


def classify_edge(
    source_layer: str,
    target_layer: str,
    target_public: bool,
    target_authorship: str,
    target_reserved: bool,
    target_compatibility_candidate: bool,
) -> dict[str, bool]:
    """Return review signals, not defect classifications."""
    nonpublic = not target_public
    generated_or_unresolved_nonpublic = (
        nonpublic and target_authorship != "confirmed_source_written"
    )
    source_written_nonpublic = (
        nonpublic and target_authorship == "confirmed_source_written"
    )
    canonical_to_source = (
        source_layer in CANONICAL_LAYERS and target_layer == "Source"
    )
    to_examples = source_layer != "Examples" and target_layer == "Examples"
    return {
        "nonpublic_target": nonpublic,
        "generated_or_authorship_unresolved_target": target_authorship
        != "confirmed_source_written",
        "reserved_target": target_reserved,
        "generated_or_unresolved_nonpublic_target": generated_or_unresolved_nonpublic,
        "confirmed_source_written_nonpublic_target": source_written_nonpublic,
        "canonical_to_source": canonical_to_source,
        "to_static_compatibility_candidate": target_compatibility_candidate,
        "to_examples_candidate": to_examples,
    }


def toy_validation() -> None:
    ordinary = classify_edge(
        "Algorithms", "Analysis", True, "confirmed_source_written", False, False
    )
    assert not any(ordinary.values())
    generated = classify_edge(
        "Analysis", "Analysis", False, "internal_no_direct_range", False, False
    )
    assert generated["nonpublic_target"]
    assert generated["generated_or_authorship_unresolved_target"]
    assert generated["generated_or_unresolved_nonpublic_target"]
    assert not generated["confirmed_source_written_nonpublic_target"]
    private_source = classify_edge(
        "Algorithms", "Algorithms", False, "confirmed_source_written", False, False
    )
    assert private_source["confirmed_source_written_nonpublic_target"]
    source_leak = classify_edge(
        "FloatingPoint", "Source", True, "confirmed_source_written", False, False
    )
    assert source_leak["canonical_to_source"]
    assert not source_leak["generated_or_authorship_unresolved_target"]
    assert not classify_edge(
        "Source", "Source", True, "confirmed_source_written", False, False
    )["canonical_to_source"]
    assert classify_edge(
        "Analysis", "Analysis", True, "confirmed_source_written", False, True
    )["to_static_compatibility_candidate"]
    assert classify_edge(
        "Algorithms", "Examples", True, "confirmed_source_written", False, False
    )["to_examples_candidate"]
    assert classify_edge(
        "Analysis", "Analysis", True, "lean_reserved_generated", True, False
    )["reserved_target"]


def main() -> None:
    toy_validation()
    script = Path(__file__).resolve()
    audit_root = script.parent.parent
    metrics_dir = audit_root / "current_graph" / "metrics"
    origins_path = metrics_dir / "declaration_origins_and_authorship.csv"
    type_edges_path = metrics_dir / "type_project_dependencies.csv.gz"
    modules_path = audit_root / "static_architecture" / "modules.csv"
    entry_points_path = audit_root / "static_architecture" / "entry_points.csv"
    source_imports_path = audit_root / "static_architecture" / "source_imports.csv"
    compiled_imports_path = audit_root / "raw" / "module_imports.csv.gz"
    existing_exposure_path = metrics_dir / "public_entrypoint_exposure.csv"

    origins_rows = read_csv(origins_path)
    origin = {row["name"]: row for row in origins_rows}
    assert len(origin) == len(origins_rows), "duplicate declaration metadata rows"
    modules = {row["module"]: row for row in read_csv(modules_path)}
    type_edges = read_csv(type_edges_path, compressed=True)

    source_universe = {
        name
        for name, row in origin.items()
        if row["is_public"] == "true"
        and row["authorship_class"] == "confirmed_source_written"
    }
    environment_public_universe = {
        name for name, row in origin.items() if row["is_public"] == "true"
    }
    assert len(source_universe) == 47_890
    assert len(environment_public_universe) == 58_120
    assert all(row["occurs_in_type"] == "true" for row in type_edges)
    assert len({(row["source"], row["target"]) for row in type_edges}) == len(type_edges)
    assert all(row["source"] in origin and row["target"] in origin for row in type_edges)

    # Complete aggregate-entry exposure.  The root extraction observes 439/479
    # entry modules in its compiled module graph.  For the 40 declaration-free
    # entry modules not observed there, use their static source-import closure;
    # this fallback is validated against compiled closure on every observed
    # entry and rejected if a declaration-bearing closure module is absent from
    # the compiled declaration-ownership universe.
    compiled_import_graph: dict[str, set[str]] = defaultdict(set)
    for row in read_csv(compiled_imports_path, compressed=True):
        if row["target_scope"] == "project":
            compiled_import_graph[row["source_module"]].add(row["target_module"])
    static_import_graph: dict[str, set[str]] = defaultdict(set)
    for row in read_csv(source_imports_path):
        if row["is_project_module"] == "true":
            static_import_graph[row["importer_module"]].add(row["imported_module"])
    compiled_module_nodes = set(compiled_import_graph)
    for targets in compiled_import_graph.values():
        compiled_module_nodes.update(targets)
    declaration_owner_modules = {row["module"] for row in origins_rows}
    entry_points = read_csv(entry_points_path)
    observed_entries = {
        row["module"] for row in entry_points if row["module"] in compiled_module_nodes
    }
    closure_mismatches = []
    for entry in sorted(observed_entries):
        compiled_closure = transitive_closure(compiled_import_graph, entry)
        static_closure = transitive_closure(static_import_graph, entry)
        if compiled_closure != static_closure:
            closure_mismatches.append(entry)
    assert not closure_mismatches

    universe_names = {
        "all_project_environment": set(origin),
        "environment_public": environment_public_universe,
        "confirmed_source_written_public": source_universe,
    }
    owner_counts: dict[str, Counter[str]] = {}
    for universe, names in universe_names.items():
        owner_counts[universe] = Counter(origin[name]["module"] for name in names)

    existing_exposure = {
        (row["entry_module"], row["universe"]): int(row["reachable_declarations"])
        for row in read_csv(existing_exposure_path)
    }
    complete_entry_exposure_rows: list[dict[str, object]] = []
    fallback_entries: list[str] = []
    for entry_row in sorted(entry_points, key=lambda row: row["module"]):
        entry = entry_row["module"]
        if entry in compiled_module_nodes:
            closure = {entry} | transitive_closure(compiled_import_graph, entry)
            basis = "compiled transitive project-module import closure plus entry module"
            status = "compiled_root_environment"
        else:
            assert entry_row["declaration_free_static"] == "true"
            closure = {entry} | transitive_closure(static_import_graph, entry)
            missing_declaration_bearing = [
                module
                for module in closure
                if int(
                    modules.get(module, {}).get("static_declaration_starter_count", "0")
                    or 0
                )
                > 0
                and module not in declaration_owner_modules
            ]
            assert not missing_declaration_bearing
            fallback_entries.append(entry)
            basis = "validated static source-import closure plus compiled declaration ownership"
            status = "declaration_free_entry_not_observed_in_root_compiled_module_graph"
        for universe, names in universe_names.items():
            reachable = sum(owner_counts[universe][module] for module in closure)
            denominator = len(names)
            complete_entry_exposure_rows.append(
                {
                    "entry_module": entry,
                    "entry_kind": entry_row["entry_kind"],
                    "entry_source_path": entry_row["source_path"],
                    "entry_seen_in_root_compiled_module_graph": str(
                        entry in compiled_module_nodes
                    ).lower(),
                    "closure_basis": basis,
                    "reachable_project_modules_including_entry": len(closure),
                    "universe": universe,
                    "reachable_declarations": reachable,
                    "universe_declarations": denominator,
                    "percent": round(100 * reachable / denominator, 6),
                    "coverage_status": status,
                    "validation_note": "Module reachability is not practical usability; for 40 declaration-free fallback entries, static and compiled closures agree on all 439 observed entry points and every declaration-bearing fallback-closure module has compiled ownership data.",
                    "raw_artifacts": "static_architecture/entry_points.csv; raw/module_imports.csv.gz; static_architecture/source_imports.csv; current_graph/metrics/declaration_origins_and_authorship.csv",
                    "raw_columns": "module,entry_kind,declaration_free_static; source_module,target_module,target_scope; importer_module,imported_module,is_project_module; name,module,is_public,authorship_class",
                }
            )
    compared_existing_rows = 0
    superseded_zero_rows = 0
    for key, expected in existing_exposure.items():
        if key[0] not in compiled_module_nodes:
            assert expected == 0
            superseded_zero_rows += 1
            continue
        actual = next(
            int(row["reachable_declarations"])
            for row in complete_entry_exposure_rows
            if (row["entry_module"], row["universe"]) == key
        )
        assert actual == expected, (key, actual, expected)
        compared_existing_rows += 1
    complete_entry_exposure_output = metrics_dir / "public_entrypoint_exposure_all.csv"
    write_csv(
        complete_entry_exposure_output,
        list(complete_entry_exposure_rows[0]),
        complete_entry_exposure_rows,
    )

    considered = [row for row in type_edges if row["source"] in source_universe]
    environment_public_considered = [
        row for row in type_edges if row["source"] in environment_public_universe
    ]
    environment_public_nonpublic = [
        row
        for row in environment_public_considered
        if origin[row["target"]]["is_public"] != "true"
    ]

    environment_public_nonpublic_rows: list[dict[str, object]] = []
    for edge in environment_public_nonpublic:
        source_meta = origin[edge["source"]]
        target_meta = origin[edge["target"]]
        environment_public_nonpublic_rows.append(
            {
                "source": edge["source"],
                "source_module": edge["source_module"],
                "source_kind": source_meta["kind"],
                "source_layer": edge["source_layer"],
                "source_authorship_class": source_meta["authorship_class"],
                "source_confirmed_source_written": str(
                    source_meta["authorship_class"] == "confirmed_source_written"
                ).lower(),
                "target": edge["target"],
                "target_module": edge["target_module"],
                "target_kind": target_meta["kind"],
                "target_layer": edge["target_layer"],
                "target_is_internal": target_meta["is_internal"],
                "target_is_private": target_meta["is_private"],
                "target_is_reserved_name": target_meta["is_reserved_name"],
                "target_authorship_class": target_meta["authorship_class"],
                "occurs_in_body_also": edge["occurs_in_body"],
                "raw_artifact": "current_graph/metrics/type_project_dependencies.csv.gz",
                "raw_columns": "source,target,source_module,target_module,source_layer,target_layer,occurs_in_type,occurs_in_body",
                "interpretation": "review candidate; a nonpublic direct type target is not automatically an unusable API",
            }
        )
    environment_public_nonpublic_rows.sort(
        key=lambda row: (str(row["source"]), str(row["target"]))
    )
    write_csv(
        metrics_dir / "environment_public_type_nonpublic_exposure_edges.csv",
        list(environment_public_nonpublic_rows[0]),
        environment_public_nonpublic_rows,
    )
    candidate_edges: list[dict[str, object]] = []
    per_source: dict[str, dict[str, object]] = {}
    target_authorship_nonpublic_edges: Counter[str] = Counter()
    target_kind_nonpublic_edges: Counter[str] = Counter()

    all_type_edge_count: Counter[str] = Counter(row["source"] for row in considered)

    for edge in considered:
        source_meta = origin[edge["source"]]
        target_meta = origin[edge["target"]]
        target_module_meta = modules.get(edge["target_module"])
        target_compatibility_candidate = bool(
            target_module_meta
            and target_module_meta["compatibility_candidate_static"] == "true"
        )
        flags = classify_edge(
            edge["source_layer"],
            edge["target_layer"],
            target_meta["is_public"] == "true",
            target_meta["authorship_class"],
            target_meta["is_reserved_name"] == "true",
            target_compatibility_candidate,
        )
        if not any(flags.values()):
            continue

        reasons = [name for name, enabled in flags.items() if enabled]
        candidate_edges.append(
            {
                "source": edge["source"],
                "source_module": edge["source_module"],
                "source_kind": source_meta["kind"],
                "source_layer": edge["source_layer"],
                "source_domain": edge["source_domain"],
                "source_chapter": edge["source_chapter"],
                "target": edge["target"],
                "target_module": edge["target_module"],
                "target_kind": target_meta["kind"],
                "target_layer": edge["target_layer"],
                "target_domain": edge["target_domain"],
                "target_chapter": edge["target_chapter"],
                "target_is_public": target_meta["is_public"],
                "target_is_internal": target_meta["is_internal"],
                "target_is_private": target_meta["is_private"],
                "target_is_reserved_name": target_meta["is_reserved_name"],
                "target_authorship_class": target_meta["authorship_class"],
                "target_module_static_compatibility_candidate": str(
                    target_compatibility_candidate
                ).lower(),
                "occurs_in_body_also": edge["occurs_in_body"],
                "exposure_nonpublic_target": str(flags["nonpublic_target"]).lower(),
                "exposure_generated_or_authorship_unresolved_target": str(
                    flags["generated_or_authorship_unresolved_target"]
                ).lower(),
                "exposure_reserved_target": str(flags["reserved_target"]).lower(),
                "exposure_generated_or_unresolved_nonpublic_target": str(
                    flags["generated_or_unresolved_nonpublic_target"]
                ).lower(),
                "exposure_confirmed_source_written_nonpublic_target": str(
                    flags["confirmed_source_written_nonpublic_target"]
                ).lower(),
                "exposure_canonical_to_source": str(flags["canonical_to_source"]).lower(),
                "exposure_to_static_compatibility_candidate": str(
                    flags["to_static_compatibility_candidate"]
                ).lower(),
                "exposure_to_examples_candidate": str(
                    flags["to_examples_candidate"]
                ).lower(),
                "candidate_reasons": ";".join(reasons),
                "raw_artifact": "current_graph/metrics/type_project_dependencies.csv.gz",
                "raw_columns": "source,target,source_module,target_module,source_layer,target_layer,occurs_in_type,occurs_in_body",
            }
        )
        if flags["nonpublic_target"]:
            target_authorship_nonpublic_edges[target_meta["authorship_class"]] += 1
            target_kind_nonpublic_edges[target_meta["kind"]] += 1

        agg = per_source.setdefault(
            edge["source"],
            {
                "source": edge["source"],
                "source_module": edge["source_module"],
                "source_kind": source_meta["kind"],
                "source_layer": edge["source_layer"],
                "source_domain": edge["source_domain"],
                "source_chapter": edge["source_chapter"],
                "nonpublic_target_edges": 0,
                "nonpublic_targets": set(),
                "generated_or_unresolved_nonpublic_target_edges": 0,
                "generated_or_authorship_unresolved_target_edges": 0,
                "reserved_target_edges": 0,
                "confirmed_source_written_nonpublic_target_edges": 0,
                "canonical_to_source_edges": 0,
                "source_layer_targets": set(),
                "static_compatibility_candidate_edges": 0,
                "examples_candidate_edges": 0,
                "candidate_reasons": set(),
            },
        )
        if flags["nonpublic_target"]:
            agg["nonpublic_target_edges"] += 1
            agg["nonpublic_targets"].add(edge["target"])
        if flags["generated_or_unresolved_nonpublic_target"]:
            agg["generated_or_unresolved_nonpublic_target_edges"] += 1
        if flags["generated_or_authorship_unresolved_target"]:
            agg["generated_or_authorship_unresolved_target_edges"] += 1
        if flags["reserved_target"]:
            agg["reserved_target_edges"] += 1
        if flags["confirmed_source_written_nonpublic_target"]:
            agg["confirmed_source_written_nonpublic_target_edges"] += 1
        if flags["canonical_to_source"]:
            agg["canonical_to_source_edges"] += 1
            agg["source_layer_targets"].add(edge["target"])
        if flags["to_static_compatibility_candidate"]:
            agg["static_compatibility_candidate_edges"] += 1
        if flags["to_examples_candidate"]:
            agg["examples_candidate_edges"] += 1
        agg["candidate_reasons"].update(reasons)

    candidate_edges.sort(key=lambda row: (str(row["source"]), str(row["target"])))
    edge_fields = list(candidate_edges[0])
    edge_output = metrics_dir / "public_type_exposure_edges.csv"
    write_csv(edge_output, edge_fields, candidate_edges)

    declaration_rows: list[dict[str, object]] = []
    for source, agg in sorted(per_source.items()):
        declaration_rows.append(
            {
                "source": source,
                "source_module": agg["source_module"],
                "source_kind": agg["source_kind"],
                "source_layer": agg["source_layer"],
                "source_domain": agg["source_domain"],
                "source_chapter": agg["source_chapter"],
                "total_direct_project_type_edges": all_type_edge_count[source],
                "nonpublic_target_edges": agg["nonpublic_target_edges"],
                "distinct_nonpublic_targets": len(agg["nonpublic_targets"]),
                "generated_or_unresolved_nonpublic_target_edges": agg[
                    "generated_or_unresolved_nonpublic_target_edges"
                ],
                "generated_or_authorship_unresolved_target_edges": agg[
                    "generated_or_authorship_unresolved_target_edges"
                ],
                "reserved_target_edges": agg["reserved_target_edges"],
                "confirmed_source_written_nonpublic_target_edges": agg[
                    "confirmed_source_written_nonpublic_target_edges"
                ],
                "canonical_to_source_edges": agg["canonical_to_source_edges"],
                "distinct_source_layer_targets": len(agg["source_layer_targets"]),
                "static_compatibility_candidate_edges": agg[
                    "static_compatibility_candidate_edges"
                ],
                "examples_candidate_edges": agg["examples_candidate_edges"],
                "candidate_reasons": ";".join(sorted(agg["candidate_reasons"])),
                "interpretation": "review candidate; direct elaborated type exposure is not by itself an API defect",
            }
        )
    declaration_output = metrics_dir / "public_type_exposure_declarations.csv"
    write_csv(declaration_output, list(declaration_rows[0]), declaration_rows)

    def edge_count(flag: str) -> int:
        return sum(row[flag] == "true" for row in candidate_edges)

    def source_count(flag: str) -> int:
        return len({row["source"] for row in candidate_edges if row[flag] == "true"})

    nonpublic_targets = {
        row["target"]
        for row in candidate_edges
        if row["exposure_nonpublic_target"] == "true"
    }
    source_targets = {
        row["target"]
        for row in candidate_edges
        if row["exposure_canonical_to_source"] == "true"
    }
    environment_public_nonpublic_sources = {
        row["source"] for row in environment_public_nonpublic
    }
    environment_public_nonpublic_targets = {
        row["target"] for row in environment_public_nonpublic
    }
    environment_public_nonpublic_target_authorship = Counter(
        origin[row["target"]]["authorship_class"]
        for row in environment_public_nonpublic
    )
    environment_public_nonpublic_private_edges = sum(
        origin[row["target"]]["is_private"] == "true"
        for row in environment_public_nonpublic
    )
    environment_public_nonpublic_both_edges = sum(
        row["occurs_in_body"] == "true" for row in environment_public_nonpublic
    )
    confirmed_nonpublic_rows = [
        row
        for row in candidate_edges
        if row["exposure_nonpublic_target"] == "true"
    ]
    confirmed_nonpublic_private_edges = sum(
        row["target_is_private"] == "true" for row in confirmed_nonpublic_rows
    )
    confirmed_nonpublic_both_edges = sum(
        row["occurs_in_body_also"] == "true" for row in confirmed_nonpublic_rows
    )
    canonical_source_universe = {
        name
        for name in source_universe
        if modules[origin[name]["module"]]["effective_architectural_layer"]
        in CANONICAL_LAYERS
    }
    canonical_nonpublic_rows = [
        row
        for row in confirmed_nonpublic_rows
        if row["source"] in canonical_source_universe
    ]
    generated_or_unresolved_rows = [
        row
        for row in candidate_edges
        if row["exposure_generated_or_authorship_unresolved_target"] == "true"
    ]
    reserved_rows = [
        row
        for row in candidate_edges
        if row["exposure_reserved_target"] == "true"
    ]
    canonical_generated_or_unresolved_rows = [
        row
        for row in generated_or_unresolved_rows
        if row["source"] in canonical_source_universe
    ]
    canonical_source_rows = [
        row
        for row in candidate_edges
        if row["exposure_canonical_to_source"] == "true"
    ]
    canonical_candidate_rows = [
        row for row in candidate_edges if row["source"] in canonical_source_universe
    ]
    canonical_nonpublic_generated_overlap_rows = [
        row
        for row in canonical_candidate_rows
        if row["exposure_nonpublic_target"] == "true"
        and row["exposure_generated_or_authorship_unresolved_target"] == "true"
    ]
    summary = {
        "schema_version": SCHEMA_VERSION,
        "edge_orientation": "consumer -> dependency",
        "source_universe": {
            "name": "confirmed_source_written_public",
            "filter": "is_public=true and authorship_class=confirmed_source_written",
            "declarations": len(source_universe),
        },
        "environment_public_source_universe": {
            "name": "environment_public",
            "filter": "is_public=true; generated and authorship-unresolved names retained",
            "declarations": len(environment_public_universe),
        },
        "canonical_source_written_public_universe": {
            "filter": "confirmed_source_written_public and effective layer in Algorithms, Analysis, or FloatingPoint",
            "declarations": len(canonical_source_universe),
        },
        "edge_universe": {
            "name": "direct_project_type_pairs_from_source_universe",
            "filter": "source in source universe and occurs_in_type=true; one row per unique ordered project pair",
            "all_project_type_pairs": len(type_edges),
            "pairs_from_source_universe": len(considered),
        },
        "review_signals": {
            "environment_public_source_declarations_with_nonpublic_target": len(
                environment_public_nonpublic_sources
            ),
            "environment_public_edges_to_nonpublic_target": len(
                environment_public_nonpublic
            ),
            "environment_public_distinct_nonpublic_targets": len(
                environment_public_nonpublic_targets
            ),
            "environment_public_nonpublic_edges_also_in_body": environment_public_nonpublic_both_edges,
            "environment_public_nonpublic_type_only_edges": len(
                environment_public_nonpublic
            )
            - environment_public_nonpublic_both_edges,
            "environment_public_edges_to_private_target": environment_public_nonpublic_private_edges,
            "source_declarations_with_nonpublic_target": source_count(
                "exposure_nonpublic_target"
            ),
            "edges_to_nonpublic_target": edge_count("exposure_nonpublic_target"),
            "distinct_nonpublic_targets": len(nonpublic_targets),
            "source_written_public_nonpublic_edges_also_in_body": confirmed_nonpublic_both_edges,
            "source_written_public_nonpublic_type_only_edges": len(
                confirmed_nonpublic_rows
            )
            - confirmed_nonpublic_both_edges,
            "source_written_public_edges_to_private_target": confirmed_nonpublic_private_edges,
            "source_declarations_with_generated_or_unresolved_nonpublic_target": source_count(
                "exposure_generated_or_unresolved_nonpublic_target"
            ),
            "edges_to_generated_or_unresolved_nonpublic_target": edge_count(
                "exposure_generated_or_unresolved_nonpublic_target"
            ),
            "source_declarations_with_generated_or_authorship_unresolved_target": source_count(
                "exposure_generated_or_authorship_unresolved_target"
            ),
            "edges_to_generated_or_authorship_unresolved_target": edge_count(
                "exposure_generated_or_authorship_unresolved_target"
            ),
            "distinct_generated_or_authorship_unresolved_targets": len(
                {row["target"] for row in generated_or_unresolved_rows}
            ),
            "source_declarations_with_reserved_target": source_count(
                "exposure_reserved_target"
            ),
            "edges_to_reserved_target": edge_count("exposure_reserved_target"),
            "distinct_reserved_targets": len(
                {row["target"] for row in reserved_rows}
            ),
            "source_declarations_with_confirmed_source_written_nonpublic_target": source_count(
                "exposure_confirmed_source_written_nonpublic_target"
            ),
            "edges_to_confirmed_source_written_nonpublic_target": edge_count(
                "exposure_confirmed_source_written_nonpublic_target"
            ),
            "canonical_source_written_public_declarations_with_nonpublic_target": len(
                {row["source"] for row in canonical_nonpublic_rows}
            ),
            "canonical_edges_to_nonpublic_target": len(canonical_nonpublic_rows),
            "canonical_distinct_nonpublic_targets": len(
                {row["target"] for row in canonical_nonpublic_rows}
            ),
            "canonical_source_written_public_declarations_with_generated_or_authorship_unresolved_target": len(
                {row["source"] for row in canonical_generated_or_unresolved_rows}
            ),
            "canonical_edges_to_generated_or_authorship_unresolved_target": len(
                canonical_generated_or_unresolved_rows
            ),
            "canonical_distinct_generated_or_authorship_unresolved_targets": len(
                {row["target"] for row in canonical_generated_or_unresolved_rows}
            ),
            "canonical_source_declarations_in_nonpublic_and_generated_overlap": len(
                {row["source"] for row in canonical_nonpublic_generated_overlap_rows}
            ),
            "canonical_edges_in_nonpublic_and_generated_overlap": len(
                canonical_nonpublic_generated_overlap_rows
            ),
            "canonical_source_declarations_with_Source_target": source_count(
                "exposure_canonical_to_source"
            ),
            "canonical_to_Source_edges": edge_count("exposure_canonical_to_source"),
            "distinct_Source_targets_from_canonical": len(source_targets),
            "canonical_source_declarations_with_any_review_signal": len(
                {row["source"] for row in canonical_candidate_rows}
            ),
            "canonical_candidate_edge_union": len(canonical_candidate_rows),
            "source_declarations_with_static_compatibility_target": source_count(
                "exposure_to_static_compatibility_candidate"
            ),
            "edges_to_static_compatibility_target": edge_count(
                "exposure_to_static_compatibility_candidate"
            ),
            "source_declarations_with_Examples_target": source_count(
                "exposure_to_examples_candidate"
            ),
            "edges_to_Examples_target": edge_count("exposure_to_examples_candidate"),
            "source_declarations_with_any_review_signal": len(per_source),
            "candidate_edges_union": len(candidate_edges),
        },
        "complete_entrypoint_exposure": {
            "entry_modules": len(entry_points),
            "root_entries": sum(
                row["entry_kind"] == "root_entry" for row in entry_points
            ),
            "documented_aggregates": sum(
                row["entry_kind"] == "documented_aggregate" for row in entry_points
            ),
            "All_aggregates": sum(
                row["entry_kind"] == "all_aggregate" for row in entry_points
            ),
            "rows_three_universes_each": len(complete_entry_exposure_rows),
            "entries_using_compiled_import_closure": len(observed_entries),
            "declaration_free_entries_using_validated_static_fallback": len(
                fallback_entries
            ),
            "observed_entry_static_compiled_closure_mismatches": len(
                closure_mismatches
            ),
            "preexisting_observed_entry_rows_reproduced_exactly": compared_existing_rows,
            "preexisting_unobserved_zero_rows_superseded_by_validated_static_fallback": superseded_zero_rows,
        },
        "environment_public_nonpublic_edge_target_authorship_distribution": dict(
            sorted(environment_public_nonpublic_target_authorship.items())
        ),
        "nonpublic_edge_target_authorship_distribution": dict(
            sorted(target_authorship_nonpublic_edges.items())
        ),
        "nonpublic_edge_target_kind_distribution": dict(
            sorted(target_kind_nonpublic_edges.items())
        ),
        "definitions": {
            "nonpublic_target": "target is environment-private or environment-internal under the v2 visibility fields",
            "generated_or_unresolved_nonpublic_target": "nonpublic target whose authorship_class is not confirmed_source_written",
            "generated_or_authorship_unresolved_target": "target of any visibility whose authorship_class is not confirmed_source_written; this is a generated-or-unresolved review signal, not proof of generation",
            "reserved_target": "target has Environment.isReservedName=true; kept separate from the broader generated-or-authorship-unresolved signal",
            "confirmed_source_written_nonpublic_target": "nonpublic target whose source range/token passes the conservative source-origin classifier",
            "canonical_to_source": "source layer is Algorithms, Analysis, or FloatingPoint and target layer is Source",
            "static_compatibility_candidate": "target owner module is marked compatibility_candidate_static=true by the static module classifier",
            "to_examples_candidate": "source is not Examples and target layer is Examples",
        },
        "interpretation": [
            "Every row is a direct elaborated type dependency, not a textual match or import edge.",
            "A review signal is not proof of an API defect: generated proof helpers can be benign elaboration artifacts, and a Source dependency may be intentional ownership debt.",
            "The scan does not pretty-print user-visible signatures or measure transitive unfolding, namespace discoverability, or external compatibility.",
        ],
        "inputs": {
            "current_graph/metrics/type_project_dependencies.csv.gz": sha256(type_edges_path),
            "current_graph/metrics/declaration_origins_and_authorship.csv": sha256(
                origins_path
            ),
            "static_architecture/modules.csv": sha256(modules_path),
            "static_architecture/entry_points.csv": sha256(entry_points_path),
            "static_architecture/source_imports.csv": sha256(source_imports_path),
            "raw/module_imports.csv.gz": sha256(compiled_imports_path),
            "current_graph/metrics/public_entrypoint_exposure.csv": sha256(
                existing_exposure_path
            ),
        },
        "tool": {
            "path": "current_graph/analyze_public_type_exposure.py",
            "sha256": sha256(script),
        },
        "outputs": {
            "environment_public_nonpublic_edge_rows": "current_graph/metrics/environment_public_type_nonpublic_exposure_edges.csv",
            "edge_rows": "current_graph/metrics/public_type_exposure_edges.csv",
            "declaration_rows": "current_graph/metrics/public_type_exposure_declarations.csv",
            "complete_entrypoint_exposure": "current_graph/metrics/public_entrypoint_exposure_all.csv",
            "validation_log": "current_graph/public_type_exposure_validation.log",
        },
        "validation": {
            "toy_cases_passed": 8,
            "source_universe_expected_47890": len(source_universe) == 47_890,
            "all_type_rows_marked_occurs_in_type": all(
                row["occurs_in_type"] == "true" for row in type_edges
            ),
            "type_pairs_unique": len(
                {(row["source"], row["target"]) for row in type_edges}
            )
            == len(type_edges),
            "all_edge_endpoints_have_metadata": all(
                row["source"] in origin and row["target"] in origin
                for row in type_edges
            ),
            "candidate_rows_have_at_least_one_signal": all(
                row["candidate_reasons"] for row in candidate_edges
            ),
            "canonical_Source_signal_disjoint_from_nonpublic_and_generated_signals": not any(
                row["exposure_canonical_to_source"] == "true"
                and (
                    row["exposure_nonpublic_target"] == "true"
                    or row["exposure_generated_or_authorship_unresolved_target"]
                    == "true"
                )
                for row in canonical_candidate_rows
            ),
            "static_and_compiled_closures_match_for_observed_entries": not closure_mismatches,
            "all_preexisting_observed_entrypoint_exposure_rows_reproduced": compared_existing_rows
            + superseded_zero_rows
            == len(existing_exposure),
        },
    }

    summary_output = metrics_dir / "public_type_exposure_summary.json"
    summary_output.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    validation_output = audit_root / "current_graph" / "public_type_exposure_validation.log"
    validation_output.write_text(
        "\n".join(
            [
                f"schema_version={SCHEMA_VERSION}",
                "command=python3 current_graph/analyze_public_type_exposure.py",
                "toy_cases=8/8 PASS",
                f"source_universe={len(source_universe)}",
                f"type_pairs_from_source_universe={len(considered)}",
                f"candidate_edge_union={len(candidate_edges)}",
                f"candidate_source_union={len(per_source)}",
                f"entry_modules={len(entry_points)}",
                f"entry_exposure_rows={len(complete_entry_exposure_rows)}",
                f"entry_compiled_closure={len(observed_entries)}",
                f"entry_validated_static_fallback={len(fallback_entries)}",
                f"preexisting_observed_entry_rows_reproduced={compared_existing_rows}",
                f"preexisting_unobserved_zero_rows_superseded={superseded_zero_rows}",
                "all_validations=PASS",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps(summary["review_signals"], sort_keys=True))


if __name__ == "__main__":
    main()
