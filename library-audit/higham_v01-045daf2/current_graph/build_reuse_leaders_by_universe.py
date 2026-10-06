#!/usr/bin/env python3
"""Build universe-specific reuse/reach rankings from frozen graph metrics."""

from __future__ import annotations

import csv
import gzip
import hashlib
import json
from pathlib import Path


SCHEMA_VERSION = "numstability-reuse-leaders/1.0.0"
TOP_N = 100
RANKINGS = {
    "direct_fan_in": (
        "direct_project_consumer_count",
        "number of distinct project declarations with a direct edge to the ranked declaration",
    ),
    "transitive_downstream_consumers": (
        "transitive_downstream_consumer_count",
        "number of distinct reverse-reachable project consumer declarations, excluding self",
    ),
    "downstream_consumer_modules": (
        "transitive_downstream_module_count",
        "number of distinct owner modules among transitive downstream consumers",
    ),
    "downstream_consumer_layers": (
        "transitive_downstream_layer_count",
        "number of audit-classified layers among transitive downstream consumers",
    ),
    "downstream_consumer_domains": (
        "transitive_downstream_domain_count",
        "number of audit-classified domains among transitive downstream consumers",
    ),
    "downstream_consumer_chapters": (
        "transitive_downstream_chapter_count",
        "number of audit-classified chapters among transitive downstream consumers",
    ),
    "downstream_depth": (
        "downstream_depth_scc_condensation",
        "longest reverse-consumer path length in the SCC condensation DAG",
    ),
    "reused_low_in_hierarchy_product": (
        "derived",
        "transitive_downstream_consumer_count * (1 + downstream_depth_scc_condensation)",
    ),
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def metric_value(row: dict[str, str], metric: str) -> int:
    column = RANKINGS[metric][0]
    if column == "derived":
        return int(row["transitive_downstream_consumer_count"]) * (
            1 + int(row["downstream_depth_scc_condensation"])
        )
    return int(row[column])


def toy_validation() -> None:
    rows = [
        {
            "name": "a",
            "direct_project_consumer_count": "2",
            "transitive_downstream_consumer_count": "5",
            "transitive_downstream_module_count": "2",
            "transitive_downstream_layer_count": "1",
            "transitive_downstream_domain_count": "2",
            "transitive_downstream_chapter_count": "0",
            "downstream_depth_scc_condensation": "3",
        },
        {
            "name": "b",
            "direct_project_consumer_count": "2",
            "transitive_downstream_consumer_count": "6",
            "transitive_downstream_module_count": "3",
            "transitive_downstream_layer_count": "2",
            "transitive_downstream_domain_count": "3",
            "transitive_downstream_chapter_count": "1",
            "downstream_depth_scc_condensation": "1",
        },
    ]
    assert metric_value(rows[0], "reused_low_in_hierarchy_product") == 20
    assert metric_value(rows[1], "reused_low_in_hierarchy_product") == 12
    ranked = sorted(rows, key=lambda row: (-metric_value(row, "direct_fan_in"), row["name"]))
    assert [row["name"] for row in ranked] == ["a", "b"]
    assert metric_value(rows[1], "transitive_downstream_consumers") == 6


def main() -> None:
    toy_validation()
    script = Path(__file__).resolve()
    audit_root = script.parent.parent
    metrics_dir = audit_root / "current_graph" / "metrics"
    declaration_metrics_path = metrics_dir / "declaration_metrics.csv.gz"
    legacy_leaders_path = metrics_dir / "reuse_leaders.csv"
    with gzip.open(
        declaration_metrics_path, "rt", encoding="utf-8", newline=""
    ) as stream:
        declarations = list(csv.DictReader(stream))
    assert len(declarations) == 77_246
    assert len({row["name"] for row in declarations}) == len(declarations)

    universes = {
        "all_project_environment": lambda row: True,
        "environment_public": lambda row: row["is_public"] == "true",
        "confirmed_source_written": lambda row: row["is_confirmed_source_written"]
        == "true",
        "confirmed_source_written_public": lambda row: row["is_public"] == "true"
        and row["is_confirmed_source_written"] == "true",
    }
    expected_sizes = {
        "all_project_environment": 77_246,
        "environment_public": 58_120,
        "confirmed_source_written": 49_573,
        "confirmed_source_written_public": 47_890,
    }

    output_rows: list[dict[str, object]] = []
    for universe, predicate in universes.items():
        members = [row for row in declarations if predicate(row)]
        assert len(members) == expected_sizes[universe]
        for rank_metric, (source_column, formula) in RANKINGS.items():
            ranked = sorted(
                members,
                key=lambda row: (-metric_value(row, rank_metric), row["name"]),
            )[:TOP_N]
            for rank, row in enumerate(ranked, 1):
                output_rows.append(
                    {
                        "universe": universe,
                        "universe_declarations": len(members),
                        "consumer_universe": "all_project_environment",
                        "rank_metric": rank_metric,
                        "rank": rank,
                        "value": metric_value(row, rank_metric),
                        "metric_source_column_or_formula": formula,
                        "name": row["name"],
                        "module": row["module"],
                        "kind": row["kind"],
                        "authorship_class": row["authorship_class"],
                        "is_public": row["is_public"],
                        "layer": row["layer"],
                        "domain": row["domain"],
                        "chapter": row["chapter"],
                        "direct_fan_in": row["direct_project_consumer_count"],
                        "direct_fan_out": row["direct_project_dependency_count"],
                        "transitive_downstream_consumers": row[
                            "transitive_downstream_consumer_count"
                        ],
                        "downstream_modules": row[
                            "transitive_downstream_module_count"
                        ],
                        "downstream_layers": row[
                            "transitive_downstream_layer_count"
                        ],
                        "downstream_domains": row[
                            "transitive_downstream_domain_count"
                        ],
                        "downstream_chapters": row[
                            "transitive_downstream_chapter_count"
                        ],
                        "downstream_depth": row[
                            "downstream_depth_scc_condensation"
                        ],
                        "dependency_depth": row[
                            "dependency_depth_scc_condensation"
                        ],
                        "raw_artifact": "current_graph/metrics/declaration_metrics.csv.gz",
                        "raw_columns": "name,module,kind,authorship_class,is_public,is_confirmed_source_written,direct_project_consumer_count,direct_project_dependency_count,transitive_downstream_consumer_count,transitive_downstream_module_count,transitive_downstream_layer_count,transitive_downstream_domain_count,transitive_downstream_chapter_count,downstream_depth_scc_condensation,dependency_depth_scc_condensation",
                    }
                )

    output_path = metrics_dir / "reuse_leaders_by_universe.csv"
    with output_path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=list(output_rows[0]), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(output_rows)

    # The five overlapping all-project rankings must exactly reproduce the
    # earlier analyzer's 500-row leader table.
    with legacy_leaders_path.open(encoding="utf-8", newline="") as stream:
        legacy = list(csv.DictReader(stream))
    produced_index = {
        (row["rank_metric"], str(row["rank"])): row
        for row in output_rows
        if row["universe"] == "all_project_environment"
    }
    for old in legacy:
        new = produced_index[(old["rank_metric"], old["rank"])]
        assert new["name"] == old["name"]
        assert str(new["value"]) == old["value"]

    summary = {
        "schema_version": SCHEMA_VERSION,
        "edge_orientation": "consumer -> dependency",
        "ranked_declaration_universes": expected_sizes,
        "consumer_universe": "all_project_environment for every direct and transitive consumer count",
        "top_n_per_metric_and_universe": TOP_N,
        "rankings": {
            name: {"source_column": column, "formula_or_definition": definition}
            for name, (column, definition) in RANKINGS.items()
        },
        "reused_low_in_hierarchy_product": {
            "formula": "transitive_downstream_consumer_count * (1 + downstream_depth_scc_condensation)",
            "interpretation": "ranking heuristic for declarations combining broad reverse reach with a long reverse-consumer chain",
            "limitations": [
                "It is not a cohesion score and must not be aggregated across the library.",
                "The multiplicative scale conflates two different properties and is dominated by large reach values.",
                "Depth is measured on the SCC condensation graph and layers/domains are not part of the formula.",
                "A high value shows internal consumption, not public API quality or source faithfulness.",
            ],
        },
        "validation": {
            "toy_product_and_tie_break_cases_passed": 3,
            "declaration_rows_unique": True,
            "universe_sizes_match_inventory": True,
            "legacy_all_project_ranking_rows_reproduced": len(legacy),
            "expected_legacy_rows": 500,
        },
        "input": {
            "path": "current_graph/metrics/declaration_metrics.csv.gz",
            "sha256": sha256(declaration_metrics_path),
        },
        "tool": {
            "path": "current_graph/build_reuse_leaders_by_universe.py",
            "sha256": sha256(script),
        },
        "output": "current_graph/metrics/reuse_leaders_by_universe.csv",
        "output_rows": len(output_rows),
    }
    summary_path = metrics_dir / "reuse_leaders_by_universe_summary.json"
    summary_path.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    validation_path = audit_root / "current_graph" / "reuse_leaders_validation.log"
    validation_path.write_text(
        "\n".join(
            [
                f"schema_version={SCHEMA_VERSION}",
                "command=python3 current_graph/build_reuse_leaders_by_universe.py",
                "toy_cases=3/3 PASS",
                f"declarations={len(declarations)}",
                f"legacy_rows_reproduced={len(legacy)}",
                f"output_rows={len(output_rows)}",
                "all_validations=PASS",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps({"output_rows": len(output_rows), "universes": expected_sizes}))


if __name__ == "__main__":
    main()
