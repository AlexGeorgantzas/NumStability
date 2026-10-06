#!/usr/bin/env python3
"""Attach exact filters and provenance to every reuse-coverage percentage."""

from __future__ import annotations

import csv
import gzip
import hashlib
import json
from pathlib import Path


SCHEMA_VERSION = "numstability-coverage-metric-contract/1.0.0"

UNIVERSES = {
    "all_project_environment": (
        lambda row: True,
        "all rows; owner module is NumStability or NumStability.*",
    ),
    "environment_public": (
        lambda row: row["is_public"] == "true",
        "is_public=true, equivalently is_internal=false and is_private=false",
    ),
    "confirmed_source_written_public": (
        lambda row: row["is_public"] == "true"
        and row["authorship_class"] == "confirmed_source_written",
        "is_public=true and authorship_class=confirmed_source_written; the latter requires nonreserved name, direct Lean selection range, and exact selected source token matching the terminal name or namespace-qualified suffix",
    ),
}

METRICS = {
    "at_least_one_incoming_project_reference": (
        lambda row: int(row["direct_project_consumer_count"]) >= 1,
        "direct_project_consumer_count >= 1",
    ),
    "used_by_at_least_one_different_module": (
        lambda row: row["used_by_different_module"] == "true",
        "used_by_different_module=true; at least one direct project consumer has a different owner module",
    ),
    "used_by_at_least_one_different_layer": (
        lambda row: row["used_by_different_layer"] == "true",
        "used_by_different_layer=true; at least one direct project consumer has a different path-derived layer",
    ),
    "used_by_multiple_consumer_modules": (
        lambda row: row["used_by_multiple_modules"] == "true",
        "used_by_multiple_modules=true; direct project consumers occupy at least two owner modules",
    ),
    "used_by_multiple_consumer_domains": (
        lambda row: row["used_by_multiple_domains"] == "true",
        "used_by_multiple_domains=true; direct project consumers occupy at least two audit-classified domains",
    ),
    "no_incoming_project_edge": (
        lambda row: row["no_incoming_project_edge"] == "true",
        "no_incoming_project_edge=true, equivalently direct_project_consumer_count=0",
    ),
    "no_outgoing_project_edge": (
        lambda row: row["no_outgoing_project_edge"] == "true",
        "no_outgoing_project_edge=true, equivalently direct_project_dependency_count=0",
    ),
    "neither_incoming_nor_outgoing_project_edge": (
        lambda row: row["isolated_in_project_graph"] == "true",
        "isolated_in_project_graph=true; no incoming and no outgoing direct project pair",
    ),
    "participates_in_nontrivial_multistep_chain": (
        lambda row: int(row["dependency_depth_scc_condensation"]) >= 2
        or int(row["downstream_depth_scc_condensation"]) >= 2,
        "dependency_depth_scc_condensation >= 2 OR downstream_depth_scc_condensation >= 2",
    ),
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main() -> None:
    script = Path(__file__).resolve()
    audit_root = script.parent.parent
    metrics_dir = audit_root / "current_graph" / "metrics"
    coverage_path = metrics_dir / "incoming_and_cross_boundary_coverage.csv"
    declaration_metrics_path = metrics_dir / "declaration_metrics.csv.gz"
    authorship_path = metrics_dir / "declaration_origins_and_authorship.csv"
    raw_declarations_path = audit_root / "raw" / "declarations.csv.gz"
    raw_dependencies_path = audit_root / "raw" / "direct_dependencies.csv.gz"
    raw_metadata_path = audit_root / "raw" / "declaration_metadata.csv"
    raw_origins_path = audit_root / "raw" / "declaration_origins.csv"

    with coverage_path.open(encoding="utf-8", newline="") as stream:
        coverage_rows = list(csv.DictReader(stream))
    with gzip.open(
        declaration_metrics_path, "rt", encoding="utf-8", newline=""
    ) as stream:
        declarations = list(csv.DictReader(stream))
    assert len(declarations) == 77_246
    assert len(coverage_rows) == len(UNIVERSES) * len(METRICS) == 27

    enhanced: list[dict[str, object]] = []
    for row in coverage_rows:
        universe_predicate, universe_filter = UNIVERSES[row["universe"]]
        metric_predicate, metric_filter = METRICS[row["metric"]]
        members = [declaration for declaration in declarations if universe_predicate(declaration)]
        numerator = sum(metric_predicate(declaration) for declaration in members)
        denominator = len(members)
        percent = 100 * numerator / denominator
        assert numerator == int(row["numerator"]), row
        assert denominator == int(row["denominator"]), row
        assert abs(percent - float(row["percent"])) < 0.000001, row
        enhanced.append(
            {
                "universe": row["universe"],
                "metric": row["metric"],
                "numerator": numerator,
                "denominator": denominator,
                "percent": row["percent"],
                "percentage_formula": "100 * numerator / denominator",
                "exact_universe_filter": universe_filter,
                "exact_metric_filter": metric_filter,
                "consumer_and_dependency_universe": "all_project_environment; direct pairs require both endpoints project-owned",
                "materialized_artifact": "current_graph/metrics/declaration_metrics.csv.gz",
                "materialized_columns": "name,module,is_public,is_internal,is_private,authorship_class,is_confirmed_source_written,direct_project_dependency_count,direct_project_consumer_count,used_by_different_module,used_by_different_layer,used_by_multiple_modules,used_by_multiple_domains,no_incoming_project_edge,no_outgoing_project_edge,isolated_in_project_graph,dependency_depth_scc_condensation,downstream_depth_scc_condensation",
                "authorship_artifact": "current_graph/metrics/declaration_origins_and_authorship.csv",
                "authorship_columns": "name,module,is_public,is_internal,is_private,is_reserved_name,has_direct_selection_range,selection_source_token,authorship_class,classifier_evidence",
                "underlying_raw_artifacts": "raw/declarations.csv.gz; raw/direct_dependencies.csv.gz; raw/declaration_metadata.csv; raw/declaration_origins.csv; selected source files under the audited NumStability tree",
                "underlying_raw_columns": "name,module,kind,is_internal,is_private,has_body; source,target,target_scope,source_module,target_module,occurs_in_type,occurs_in_body; name,range_start_line,range_start_column,range_end_line,range_end_column,selection_start_line,selection_start_column,selection_end_line,selection_end_column,is_reserved_name; name,is_reserved_name,equation_parent; exact selected source token",
                "interpretation": "Directional formal-consumption metric; no-incoming is not redundancy, and multi-step participation is not source faithfulness or API quality.",
            }
        )

    output_path = metrics_dir / "incoming_and_cross_boundary_coverage_contract.csv"
    with output_path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=list(enhanced[0]), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(enhanced)

    summary = {
        "schema_version": SCHEMA_VERSION,
        "edge_orientation": "consumer -> dependency",
        "rows": len(enhanced),
        "universes": {name: definition for name, (_, definition) in UNIVERSES.items()},
        "metrics": {name: definition for name, (_, definition) in METRICS.items()},
        "validation": {
            "coverage_rows_recomputed_exactly": len(enhanced),
            "expected_rows": 27,
            "all_percentages_match_within_1e_6_percentage_points": True,
            "declaration_universe_rows": len(declarations),
        },
        "inputs": {
            "current_graph/metrics/incoming_and_cross_boundary_coverage.csv": sha256(
                coverage_path
            ),
            "current_graph/metrics/declaration_metrics.csv.gz": sha256(
                declaration_metrics_path
            ),
            "current_graph/metrics/declaration_origins_and_authorship.csv": sha256(
                authorship_path
            ),
            "raw/declarations.csv.gz": sha256(raw_declarations_path),
            "raw/direct_dependencies.csv.gz": sha256(raw_dependencies_path),
            "raw/declaration_metadata.csv": sha256(raw_metadata_path),
            "raw/declaration_origins.csv": sha256(raw_origins_path),
        },
        "tool": {
            "path": "current_graph/build_coverage_metric_contract.py",
            "sha256": sha256(script),
        },
        "output": "current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv",
    }
    summary_path = metrics_dir / "incoming_and_cross_boundary_coverage_contract_summary.json"
    summary_path.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    validation_path = audit_root / "current_graph" / "coverage_contract_validation.log"
    validation_path.write_text(
        "\n".join(
            [
                f"schema_version={SCHEMA_VERSION}",
                "command=python3 current_graph/build_coverage_metric_contract.py",
                f"coverage_rows={len(enhanced)}",
                f"declaration_rows={len(declarations)}",
                "all_numerators_denominators_percentages=PASS",
                "all_validations=PASS",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps(summary["validation"], sort_keys=True))


if __name__ == "__main__":
    main()
