#!/usr/bin/env python3
"""Compare two NumStability declaration-audit snapshots."""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from pathlib import Path


def csv_rows(path: Path):
    with path.open(newline="", encoding="utf-8") as handle:
        yield from csv.DictReader(handle)


def declarations(raw: Path) -> dict[str, dict[str, str]]:
    return {row["name"]: row for row in csv_rows(raw / "declarations.csv")}


def is_public(row: dict[str, str]) -> bool:
    return row["is_internal"] == "false" and row["is_private"] == "false"


def public_project_edges(
    raw: Path, public_names: set[str]
) -> set[tuple[str, str]]:
    result: set[tuple[str, str]] = set()
    for row in csv_rows(raw / "direct_dependencies.csv"):
        if (
            row["target_scope"] == "project"
            and row["source"] in public_names
            and row["target"] in public_names
        ):
            result.add((row["source"], row["target"]))
    return result


def module_imports(raw: Path) -> set[tuple[str, str]]:
    return {
        (row["source_module"], row["target_module"])
        for row in csv_rows(raw / "module_imports.csv")
        if row["target_scope"] == "project"
    }


def module_metrics(metrics: Path, prefix: str | None) -> dict[str, int | float]:
    rows = list(csv_rows(metrics / "module_metrics.csv"))
    if prefix is not None:
        rows = [row for row in rows if row["module"].startswith(prefix)]
    public_count = sum(int(row["public_declaration_count"]) for row in rows)
    public_used_outside = sum(
        int(row["public_declarations_used_outside_module"]) for row in rows
    )
    return {
        "modules": len(rows),
        "declarations": sum(int(row["declaration_count"]) for row in rows),
        "public_declarations": public_count,
        "apparent_leaves": sum(int(row["apparent_leaf_count"]) for row in rows),
        "public_apparent_leaves": sum(
            int(row["public_apparent_leaf_count"]) for row in rows
        ),
        "isolated_declarations": sum(int(row["isolated_count"]) for row in rows),
        "public_declarations_used_outside_module": public_used_outside,
        "public_outside_module_utilization_percent": round(
            100 * public_used_outside / public_count, 4
        )
        if public_count
        else 0.0,
    }


def delta(before: dict, after: dict) -> dict[str, int | float]:
    return {key: after[key] - before[key] for key in before}


def edge_examples(edges: set[tuple[str, str]], limit: int = 25) -> list[dict[str, str]]:
    return [
        {"source": source, "target": target}
        for source, target in sorted(edges)[:limit]
    ]


def render_markdown(result: dict) -> str:
    api = result["public_api"]
    logical = result["stable_public_logical_edges"]
    imports = result["project_module_imports"]
    scope = result["scope_metrics"]
    assignments = result["public_module_assignments"]
    lines = [
        "# Declaration-audit comparison",
        "",
        "## Compatibility",
        "",
        f"- Public declarations removed: {api['removed_count']}",
        f"- Public declarations added: {api['added_count']}",
        f"- Stable public declarations moved between modules: {assignments['changed_count']}",
        f"- Stable public logical dependency edges removed: {logical['removed_count']}",
        f"- Stable public logical dependency edges added: {logical['added_count']}",
        "",
        "## Module graph",
        "",
        f"- Direct project imports removed: {imports['removed_count']}",
        f"- Direct project imports added: {imports['added_count']}",
        "",
        "## Scoped metrics",
        "",
        "| Metric | Before | After | Delta |",
        "| --- | ---: | ---: | ---: |",
    ]
    for key, before_value in scope["before"].items():
        lines.append(
            f"| `{key}` | {before_value} | {scope['after'][key]} | {scope['delta'][key]} |"
        )
    if api["added"]:
        lines.extend(["", "### Added public declarations", ""])
        lines.extend(f"- `{name}`" for name in api["added"])
    if api["removed"]:
        lines.extend(["", "### Removed public declarations", ""])
        lines.extend(f"- `{name}`" for name in api["removed"])
    lines.extend(
        [
            "",
            "Cross-module utilization is sensitive to file boundaries. An increase after",
            "splitting a module does not by itself establish new semantic reuse; consult the",
            "stable public logical-edge diff above.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--before-raw", type=Path, required=True)
    parser.add_argument("--before-metrics", type=Path, required=True)
    parser.add_argument("--after-raw", type=Path, required=True)
    parser.add_argument("--after-metrics", type=Path, required=True)
    parser.add_argument("--module-prefix")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--markdown", type=Path)
    args = parser.parse_args()

    before_declarations = declarations(args.before_raw)
    after_declarations = declarations(args.after_raw)
    before_public = {
        name for name, row in before_declarations.items() if is_public(row)
    }
    after_public = {
        name for name, row in after_declarations.items() if is_public(row)
    }
    stable_public = before_public & after_public

    assignment_changes = [
        {
            "name": name,
            "before_module": before_declarations[name]["module"],
            "after_module": after_declarations[name]["module"],
        }
        for name in sorted(stable_public)
        if before_declarations[name]["module"] != after_declarations[name]["module"]
    ]
    assignment_pairs = Counter(
        (row["before_module"], row["after_module"])
        for row in assignment_changes
    )

    before_edges = public_project_edges(args.before_raw, before_public)
    after_edges = public_project_edges(args.after_raw, after_public)
    removed_edges = before_edges - after_edges
    added_edges = after_edges - before_edges
    before_stable_edges = {
        edge for edge in before_edges
        if edge[0] in stable_public and edge[1] in stable_public
    }
    after_stable_edges = {
        edge for edge in after_edges
        if edge[0] in stable_public and edge[1] in stable_public
    }
    removed_stable_edges = before_stable_edges - after_stable_edges
    added_stable_edges = after_stable_edges - before_stable_edges
    before_imports = module_imports(args.before_raw)
    after_imports = module_imports(args.after_raw)
    removed_imports = before_imports - after_imports
    added_imports = after_imports - before_imports

    before_scope = module_metrics(args.before_metrics, args.module_prefix)
    after_scope = module_metrics(args.after_metrics, args.module_prefix)
    result = {
        "schema_version": 1,
        "module_prefix": args.module_prefix,
        "public_api": {
            "before_count": len(before_public),
            "after_count": len(after_public),
            "removed_count": len(before_public - after_public),
            "added_count": len(after_public - before_public),
            "removed": sorted(before_public - after_public),
            "added": sorted(after_public - before_public),
        },
        "public_module_assignments": {
            "changed_count": len(assignment_changes),
            "by_module_pair": [
                {"before_module": pair[0], "after_module": pair[1], "count": count}
                for pair, count in sorted(assignment_pairs.items())
            ],
            "changes": assignment_changes,
        },
        "public_logical_edges": {
            "before_count": len(before_edges),
            "after_count": len(after_edges),
            "removed_count": len(removed_edges),
            "added_count": len(added_edges),
            "removed_examples": edge_examples(removed_edges),
            "added_examples": edge_examples(added_edges),
        },
        "stable_public_logical_edges": {
            "before_count": len(before_stable_edges),
            "after_count": len(after_stable_edges),
            "removed_count": len(removed_stable_edges),
            "added_count": len(added_stable_edges),
            "removed_examples": edge_examples(removed_stable_edges),
            "added_examples": edge_examples(added_stable_edges),
        },
        "project_module_imports": {
            "before_count": len(before_imports),
            "after_count": len(after_imports),
            "removed_count": len(removed_imports),
            "added_count": len(added_imports),
            "removed": edge_examples(removed_imports),
            "added": edge_examples(added_imports),
        },
        "scope_metrics": {
            "before": before_scope,
            "after": after_scope,
            "delta": delta(before_scope, after_scope),
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    if args.markdown is not None:
        args.markdown.parent.mkdir(parents=True, exist_ok=True)
        args.markdown.write_text(render_markdown(result), encoding="utf-8")
    print(json.dumps({
        "public_removed": result["public_api"]["removed_count"],
        "public_added": result["public_api"]["added_count"],
        "stable_public_edges_removed": result["stable_public_logical_edges"]["removed_count"],
        "stable_public_edges_added": result["stable_public_logical_edges"]["added_count"],
        "module_imports_removed": result["project_module_imports"]["removed_count"],
        "module_imports_added": result["project_module_imports"]["added_count"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
