#!/usr/bin/env python3
"""Render a compact Markdown audit report from reproducible baseline artifacts."""

from __future__ import annotations

import argparse
import csv
import json
import statistics
from pathlib import Path


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def markdown_cell(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def table(headers: list[str], rows: list[list[object]]) -> list[str]:
    result = [
        "| " + " | ".join(map(markdown_cell, headers)) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    result.extend(
        "| " + " | ".join(map(markdown_cell, row)) + " |" for row in rows
    )
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--metrics", type=Path, required=True)
    parser.add_argument("--review", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    baseline = json.loads((args.baseline / "baseline.json").read_text(encoding="utf-8"))
    summary = json.loads((args.metrics / "summary.json").read_text(encoding="utf-8"))
    files = read_csv(args.baseline / "files.csv")
    modules = read_csv(args.metrics / "module_metrics.csv")
    counts = summary["counts"]
    connected = summary["connected_component_coverage"]
    usage = summary["usage_rates"]
    comparison = summary["module_import_vs_declaration_use"]
    commit = baseline["git_commit"]["output"]
    build = baseline["full_build"]

    lines = [
        "# NumStability library baseline audit",
        "",
        f"Commit: `{commit}`",
        "",
        "## Reproducibility baseline",
        "",
    ]
    lines.extend(
        table(
            ["Measure", "Value"],
            [
                ["Lean toolchain", baseline["lean_toolchain"]],
                ["Mathlib revision", baseline["mathlib_revision"]],
                ["Lean source files", baseline["file_statistics"]["lean_file_count"]],
                ["Lean source lines", baseline["file_statistics"]["line_count"]],
                ["Source-level direct imports", baseline["file_statistics"]["source_direct_import_count"]],
                ["Full `lake build` return code", build.get("return_code", "not run")],
                ["Incremental full-build wall time", build.get("duration_seconds", "not run")],
                ["Library source worktree status", baseline["library_source_status"]["output"] or "clean"],
            ],
        )
    )
    lines.extend(
        [
            "",
            "The recorded full build is explicitly an incremental build using the artifacts present at baseline time. Independent per-module timings compile each source into a fresh temporary output artifact.",
            "",
            "## Declaration graph",
            "",
        ]
    )
    lines.extend(
        table(
            ["Measure", "Value"],
            [
                ["All declarations", counts["declarations"]],
                ["Public declarations", counts["public_declarations"]],
                ["Direct NumStability declaration edges", counts["project_direct_edges"]],
                ["Cross-module declaration edges", counts["cross_module_declaration_edges"]],
                ["Project modules in compiled graph", counts["project_modules_in_compiled_graph"]],
                ["Project modules containing declarations", counts["project_modules_with_declarations"]],
                ["Apparent public leaves", counts["public_apparent_leaves"]],
                ["Public isolated declarations", counts["public_isolated_declarations"]],
                ["Largest weak component, all declarations", f'{connected["largest_weak_component_percent"]}%'],
                ["Largest weak component, public declarations", f'{connected["public_largest_weak_component_percent"]}%'],
                ["Public declarations referenced anywhere in project", f'{usage["public_declarations_with_any_incoming_project_reference_percent"]}%'],
                ["Public declarations referenced from another module", f'{usage["public_declarations_used_outside_their_module_percent"]}%'],
            ],
        )
    )
    lines.extend(
        [
            "",
            "The connected-component percentage and reuse percentage answer different questions. Membership in one large undirected component does not mean that a declaration is used elsewhere, and it especially does not mean that it is used across a module boundary.",
            "",
            "## Import-versus-use comparison",
            "",
        ]
    )
    lines.extend(
        table(
            ["Measure", "Count"],
            [
                ["Direct project imports", counts["direct_project_import_edges"]],
                ["Direct imports without a direct logical declaration edge", comparison["direct_imports_without_direct_declaration_use"]],
                ["Declaration module pairs supplied through transitive imports", comparison["declaration_module_pairs_without_direct_import"]],
            ],
        )
    )

    largest_files = sorted(files, key=lambda row: int(row["line_count"]), reverse=True)[:15]
    lines.extend(["", "## Largest source files", ""])
    lines.extend(
        table(
            ["Module", "Lines", "Direct imports"],
            [
                [row["module"], row["line_count"], row["direct_import_count"]]
                for row in largest_files
            ],
        )
    )

    eligible_modules = [
        row for row in modules if int(row["public_declaration_count"]) >= 20
    ]
    lowest_utilization = sorted(
        eligible_modules,
        key=lambda row: (
            float(row["public_outside_module_utilization_percent"]),
            -int(row["public_declaration_count"]),
            row["module"],
        ),
    )[:20]
    lines.extend(
        [
            "",
            "## Lowest public cross-module utilization",
            "",
            "Only modules with at least 20 public declarations are shown. Zero utilization is not a deletion verdict; it marks a module for endpoint/redundancy review.",
            "",
        ]
    )
    lines.extend(
        table(
            ["Module", "Public declarations", "Used outside module", "Utilization"],
            [
                [
                    row["module"],
                    row["public_declaration_count"],
                    row["public_declarations_used_outside_module"],
                    f'{row["public_outside_module_utilization_percent"]}%',
                ]
                for row in lowest_utilization
            ],
        )
    )

    timing_path = args.baseline / "module_compile_times.csv"
    lines.extend(["", "## Compilation timings", ""])
    if timing_path.exists():
        timings = read_csv(timing_path)
        successful = [row for row in timings if row["return_code"] == "0"]
        durations = sorted(float(row["duration_seconds"]) for row in successful)
        p90_index = int(0.9 * (len(durations) - 1)) if durations else 0
        slowest = sorted(
            successful, key=lambda row: float(row["duration_seconds"]), reverse=True
        )[:20]
        lines.append(
            f"Recorded {len(timings)} of {baseline['file_statistics']['lean_file_count']} module timings."
        )
        lines.append("")
        if durations:
            lines.extend(
                table(
                    ["Measure", "Seconds"],
                    [
                        ["Median", round(statistics.median(durations), 6)],
                        ["90th percentile (nearest rank in sorted baseline)", round(durations[p90_index], 6)],
                        ["Maximum", round(max(durations), 6)],
                    ],
                )
            )
        lines.extend(["", "### Slowest modules", ""])
        lines.extend(
            table(
                ["Module", "Seconds"],
                [[row["module"], row["duration_seconds"]] for row in slowest],
            )
        )
    else:
        lines.append("Independent per-module timing has not been run yet.")

    if args.review is not None:
        leaf_review_path = args.review / "leaf_review.csv"
        duplicate_path = args.review / "possible_duplicate_statements.csv"
        lines.extend(["", "## Review queues", ""])
        if leaf_review_path.exists():
            leaf_rows = read_csv(leaf_review_path)
            classifications: dict[str, int] = {}
            for row in leaf_rows:
                classification = row["classification"]
                classifications[classification] = classifications.get(classification, 0) + 1
            lines.extend(
                table(
                    ["Leaf classification", "Count"],
                    [[name, count] for name, count in sorted(classifications.items())],
                )
            )
        if duplicate_path.exists():
            duplicate_rows = read_csv(duplicate_path)
            duplicate_groups = {row["group_id"] for row in duplicate_rows}
            lines.extend(
                [
                    "",
                    f"Exact structural statement matching produced {len(duplicate_groups)} candidate groups containing {len(duplicate_rows)} public declarations. These include intentional aliases and require human review.",
                ]
            )

    lines.extend(["", "## Interpretation limits", ""])
    lines.extend(f"- {limitation}" for limitation in summary["limitations"])
    lines.extend(
        [
            "",
            "## Publication-safe statement",
            "",
            "Report connectedness, internal reference coverage, and cross-module utilization as separate metrics. Do not describe largest-component coverage as the percentage of the library that is reused or builds upon itself.",
            "",
        ]
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
