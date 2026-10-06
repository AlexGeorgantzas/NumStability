#!/usr/bin/env python3
"""Build persistent duplicate/canonical and isolated-declaration review tables.

The script only prioritizes evidence.  It never labels a declaration redundant,
source-backed, generated, or removable without a human review.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path


TRUE = "true"
MANUAL_CANONICAL_FIELDS = [
    "source_anchor",
    "pdf_file",
    "printed_page",
    "book_statement_match",
    "member_role",
    "canonical_replacement",
    "disposition",
    "review_status",
    "review_notes",
]
MANUAL_ISOLATE_FIELDS = [
    "source_anchor",
    "pdf_file",
    "printed_page",
    "book_statement_match",
    "isolate_role",
    "disposition",
    "review_status",
    "review_notes",
]
GENERATED_NAME_RE = re.compile(r"(?:^|\.)(?:eq_\d+|congr_simp)$")
DECLARATION_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe)[ \t]+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.?!]*)"
)


def require_columns(path: Path, fieldnames: list[str] | None, required: set[str]) -> None:
    missing = required.difference(fieldnames or [])
    if missing:
        raise ValueError(f"{path}: missing required columns {sorted(missing)}")


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            raise ValueError(f"{path}: CSV has no header")
        return list(reader)


def read_previous(path: Path | None) -> dict[str, dict[str, str]]:
    if path is None or not path.exists():
        return {}
    rows = read_csv(path)
    if rows and "name" not in rows[0]:
        raise ValueError(f"{path}: previous review must contain a name column")
    return {row["name"]: row for row in rows}


def terminal_name(name: str) -> str:
    return name.rsplit(".", maxsplit=1)[-1]


def source_declaration_paths(
    source_root: Path | None, candidate_names: set[str]
) -> dict[str, set[str]]:
    """Return a conservative source-text signal keyed by full declaration name.

    Lean's graph CSV currently has no source-range/generated flag.  Matching an
    explicit declaration header is therefore a review signal, not proof of
    authorship.  Paths are emitted so a reviewer can confirm each match.
    """
    if source_root is None:
        return {}
    if not source_root.is_dir():
        raise ValueError(f"source root does not exist: {source_root}")

    names_by_terminal: dict[str, set[str]] = defaultdict(set)
    for name in candidate_names:
        names_by_terminal[terminal_name(name)].add(name)

    matches: dict[str, set[str]] = defaultdict(set)
    for path in sorted(source_root.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        declared = {match.group(1) for match in DECLARATION_RE.finditer(text)}
        for short_name in declared.intersection(names_by_terminal):
            for full_name in names_by_terminal[short_name]:
                matches[full_name].add(str(path))
    return matches


def stable_group_key(rows: list[dict[str, str]]) -> str:
    payload = "\0".join(
        [rows[0].get("type_hash", ""), *sorted(row["name"] for row in rows)]
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def has_cycle(names: set[str], outgoing: dict[str, set[str]]) -> bool:
    state: dict[str, int] = {}

    def visit(name: str) -> bool:
        mark = state.get(name, 0)
        if mark == 1:
            return True
        if mark == 2:
            return False
        state[name] = 1
        for target in outgoing[name].intersection(names):
            if visit(target):
                return True
        state[name] = 2
        return False

    return any(visit(name) for name in names if state.get(name, 0) == 0)


def forwarding_evidence(
    rows: list[dict[str, str]],
    peer_body_out: dict[str, set[str]],
    peer_in: dict[str, set[str]],
    reserved_by_name: dict[str, str],
) -> tuple[str, str, str]:
    names = {row["name"] for row in rows}
    nonreserved = {
        name for name in names if reserved_by_name.get(name, "unknown") != TRUE
    }
    reserved_count = sum(reserved_by_name.get(name) == TRUE for name in names)
    edge_count = sum(len(peer_body_out[name].intersection(names)) for name in names)
    if not nonreserved:
        return ("reserved_only", "", "F_reserved_only")
    if reserved_count:
        return ("mixed_reserved_nonreserved", "", "E_mixed_reserved_nonreserved")
    if edge_count == 0:
        return ("no_same_statement_body_edge", "", "D_no_same_statement_body_edge")
    if has_cycle(names, peer_body_out):
        return ("cycle", "", "C_ambiguous_forwarding_graph")
    sinks = sorted(
        name
        for name in nonreserved
        if not peer_body_out[name].intersection(names) and peer_in[name].intersection(names)
    )
    if len(sinks) == 1:
        return ("unique_nonreserved_sink", sinks[0], "B_unique_nonreserved_sink")
    if len(sinks) > 1:
        return ("multiple_sinks", "", "C_ambiguous_forwarding_graph")
    return ("body_edges_without_sink", "", "C_ambiguous_forwarding_graph")


def manual_values(
    previous: dict[str, dict[str, str]],
    name: str,
    fields: list[str],
    current_group_key: str = "",
) -> dict[str, str]:
    old = previous.get(name, {})
    if (
        current_group_key
        and old.get("group_key")
        and old["group_key"] != current_group_key
    ):
        values = {field: "" for field in fields}
        values["review_status"] = "needs_rereview_group_changed"
        values["review_notes"] = "Exact-statement group membership or hash changed."
        return values
    values = {field: old.get(field, "") for field in fields}
    if not values.get("review_status"):
        values["review_status"] = "unreviewed"
    return values


def authorship_signal(
    name: str, reserved_by_name: dict[str, str], source_paths: dict[str, set[str]]
) -> str:
    reserved = reserved_by_name.get(name, "unknown")
    if reserved == TRUE:
        return "compiler_reserved"
    if source_paths.get(name):
        return "explicit_source_text_match"
    if reserved == "false":
        return "nonreserved_unknown"
    return "unknown"


def write_csv(path: Path, fields: list[str], rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--duplicates", type=Path, required=True)
    parser.add_argument("--metrics", type=Path, required=True)
    parser.add_argument("--dependencies", type=Path, required=True)
    parser.add_argument("--origins", type=Path)
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--snapshot-commit", default="")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--previous-canonical", type=Path)
    parser.add_argument("--previous-isolates", type=Path)
    args = parser.parse_args()

    duplicate_rows = read_csv(args.duplicates)
    metric_rows = read_csv(args.metrics)
    origin_rows = read_csv(args.origins) if args.origins is not None else []
    require_columns(
        args.duplicates,
        list(duplicate_rows[0]) if duplicate_rows else [],
        {"group_id", "group_size", "name", "module", "kind"},
    )
    require_columns(
        args.metrics,
        list(metric_rows[0]) if metric_rows else [],
        {
            "name",
            "module",
            "kind",
            "is_internal",
            "is_private",
            "direct_project_dependency_count",
            "incoming_project_reference_count",
            "is_apparent_leaf",
            "is_project_isolated",
            "is_used_outside_module",
        },
    )
    if args.origins is not None:
        require_columns(
            args.origins,
            list(origin_rows[0]) if origin_rows else [],
            {"name", "module", "is_reserved_name"},
        )

    metrics = {row["name"]: row for row in metric_rows}
    reserved_by_name = {
        row["name"]: row["is_reserved_name"] for row in origin_rows
    }
    equation_parent_by_name = {
        row["name"]: row.get("equation_parent", "") for row in origin_rows
    }
    groups: dict[str, list[dict[str, str]]] = defaultdict(list)
    member_group: dict[str, str] = {}
    for row in duplicate_rows:
        group_id = row["group_id"]
        if row["name"] in member_group:
            raise ValueError(f"duplicate candidate appears in multiple groups: {row['name']}")
        groups[group_id].append(row)
        member_group[row["name"]] = group_id
    group_key_by_id: dict[str, str] = {}
    for group_id, rows in groups.items():
        declared_sizes = {row["group_size"] for row in rows}
        hashes = {row.get("type_hash", "") for row in rows}
        equivalence_ids = {row.get("type_equivalence_id", "") for row in rows}
        if declared_sizes != {str(len(rows))}:
            raise ValueError(f"group {group_id}: inconsistent group_size")
        if len(hashes) != 1 or len(equivalence_ids) != 1:
            raise ValueError(f"group {group_id}: inconsistent exact-statement identity")
        group_key_by_id[group_id] = stable_group_key(rows)

    public_isolates = [
        row
        for row in metric_rows
        if row["is_internal"] != TRUE
        and row["is_private"] != TRUE
        and row["is_project_isolated"] == TRUE
    ]
    candidate_names = set(member_group).union(row["name"] for row in public_isolates)
    source_paths = source_declaration_paths(args.source_root, candidate_names)

    peer_body_out: dict[str, set[str]] = defaultdict(set)
    peer_type_out: dict[str, set[str]] = defaultdict(set)
    peer_in: dict[str, set[str]] = defaultdict(set)
    same_statement_body_edges: list[dict[str, str]] = []
    duplicate_member_users: list[dict[str, str]] = []
    with args.dependencies.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        require_columns(
            args.dependencies,
            reader.fieldnames,
            {"source", "target", "target_scope", "occurs_in_type", "occurs_in_body"},
        )
        for edge in reader:
            if edge["target_scope"] != "project" or edge["source"] == edge["target"]:
                continue
            target_group_id = member_group.get(edge["target"])
            if target_group_id is not None:
                duplicate_member_users.append(
                    {
                        "group_key": group_key_by_id[target_group_id],
                        "target_name": edge["target"],
                        "source_name": edge["source"],
                        "source_module": edge.get("source_module", ""),
                        "occurs_in_type": edge["occurs_in_type"],
                        "occurs_in_body": edge["occurs_in_body"],
                        "same_module": edge.get("same_module", ""),
                    }
                )
            group_id = member_group.get(edge["source"])
            if group_id is None or member_group.get(edge["target"]) != group_id:
                continue
            if edge["occurs_in_body"] == TRUE:
                peer_body_out[edge["source"]].add(edge["target"])
                same_statement_body_edges.append(
                    {
                        "group_key": group_key_by_id[group_id],
                        "source_name": edge["source"],
                        "target_name": edge["target"],
                        "same_module": edge.get("same_module", ""),
                    }
                )
            if edge["occurs_in_type"] == TRUE:
                peer_type_out[edge["source"]].add(edge["target"])
            peer_in[edge["target"]].add(edge["source"])

    previous_canonical = read_previous(
        args.previous_canonical
        or (args.output_dir / "canonical_member_review.csv")
    )
    previous_isolates = read_previous(
        args.previous_isolates or (args.output_dir / "isolated_review.csv")
    )
    canonical_rows: list[dict[str, str]] = []
    group_rows: list[dict[str, str]] = []

    for group_id, rows in groups.items():
        rows = sorted(rows, key=lambda row: (row["module"], row["name"]))
        enriched = [(row, metrics.get(row["name"], {})) for row in rows]
        has_peer_body = any(peer_body_out[row["name"]] for row in rows)
        group_key = group_key_by_id[group_id]
        forwarding_shape, canonical_hint, evidence_bucket = forwarding_evidence(
            rows, peer_body_out, peer_in, reserved_by_name
        )
        has_nonreserved_isolate = any(
            metric.get("is_project_isolated") == TRUE
            and (
                reserved_by_name.get(row["name"]) == "false"
                or bool(source_paths.get(row["name"]))
            )
            for row, metric in enriched
        )
        if has_nonreserved_isolate:
            evidence_bucket = "A_nonreserved_isolate_in_exact_group"
        group_rows.append(
            {
                "snapshot_commit": args.snapshot_commit,
                "group_id": group_id,
                "group_key": group_key,
                "type_hash": rows[0].get("type_hash", ""),
                "type_equivalence_id": rows[0].get("type_equivalence_id", ""),
                "group_size": str(len(rows)),
                "module_count": str(len({row["module"] for row in rows})),
                "nonreserved_member_count": str(
                    sum(reserved_by_name.get(row["name"]) == "false" for row in rows)
                ),
                "reserved_member_count": str(
                    sum(reserved_by_name.get(row["name"]) == TRUE for row in rows)
                ),
                "unknown_origin_member_count": str(
                    sum(row["name"] not in reserved_by_name for row in rows)
                ),
                "leaf_member_count": str(
                    sum(metric.get("is_apparent_leaf") == TRUE for _, metric in enriched)
                ),
                "isolated_member_count": str(
                    sum(metric.get("is_project_isolated") == TRUE for _, metric in enriched)
                ),
                "used_outside_module_member_count": str(
                    sum(metric.get("is_used_outside_module") == TRUE for _, metric in enriched)
                ),
                "explicit_source_member_count": str(
                    sum(bool(source_paths.get(row["name"])) for row in rows)
                ),
                "generated_name_signal_member_count": str(
                    sum(bool(GENERATED_NAME_RE.search(row["name"])) for row in rows)
                ),
                "has_direct_peer_body_edge": str(has_peer_body).lower(),
                "has_direct_peer_type_edge": str(
                    any(peer_type_out[row["name"]] for row in rows)
                ).lower(),
                "same_statement_body_edge_count": str(
                    sum(len(peer_body_out[row["name"]]) for row in rows)
                ),
                "forwarding_shape": forwarding_shape,
                "canonical_hint": canonical_hint,
                "evidence_bucket": evidence_bucket,
                "members": " | ".join(row["name"] for row in rows),
            }
        )
        for row, metric in enriched:
            name = row["name"]
            canonical_rows.append(
                {
                    "snapshot_commit": args.snapshot_commit,
                    "group_id": group_id,
                    "group_key": group_key,
                    "group_size": str(len(rows)),
                    "evidence_bucket": evidence_bucket,
                    "forwarding_shape": forwarding_shape,
                    "canonical_hint": canonical_hint,
                    "name": name,
                    "module": row["module"],
                    "kind": row["kind"],
                    "incoming_project_reference_count": metric.get(
                        "incoming_project_reference_count", ""
                    ),
                    "direct_project_dependency_count": metric.get(
                        "direct_project_dependency_count", ""
                    ),
                    "is_apparent_leaf": metric.get("is_apparent_leaf", ""),
                    "is_project_isolated": metric.get("is_project_isolated", ""),
                    "is_used_outside_module": metric.get("is_used_outside_module", ""),
                    "cross_module_incoming_count": metric.get(
                        "cross_module_incoming_count", ""
                    ),
                    "direct_peer_body_targets": " | ".join(sorted(peer_body_out[name])),
                    "direct_peer_type_targets": " | ".join(sorted(peer_type_out[name])),
                    "direct_peer_users": " | ".join(sorted(peer_in[name])),
                    "generated_name_signal": str(
                        bool(GENERATED_NAME_RE.search(name))
                    ).lower(),
                    "is_reserved_name": reserved_by_name.get(name, "unknown"),
                    "equation_parent": equation_parent_by_name.get(name, ""),
                    "authorship_signal": authorship_signal(
                        name, reserved_by_name, source_paths
                    ),
                    "explicit_source_declaration_signal": str(
                        bool(source_paths.get(name))
                    ).lower(),
                    "source_paths": " | ".join(sorted(source_paths.get(name, set()))),
                    **manual_values(
                        previous_canonical,
                        name,
                        MANUAL_CANONICAL_FIELDS,
                        group_key,
                    ),
                }
            )

    canonical_rows.sort(
        key=lambda row: (row["evidence_bucket"], row["group_key"], row["name"])
    )
    group_rows.sort(key=lambda row: (row["evidence_bucket"], row["group_key"]))

    isolate_rows: list[dict[str, str]] = []
    for metric in public_isolates:
        name = metric["name"]
        isolate_rows.append(
            {
                "snapshot_commit": args.snapshot_commit,
                "name": name,
                "module": metric["module"],
                "kind": metric["kind"],
                "incoming_project_reference_count": metric[
                    "incoming_project_reference_count"
                ],
                "direct_project_dependency_count": metric[
                    "direct_project_dependency_count"
                ],
                "exact_statement_group_id": member_group.get(name, ""),
                "exact_statement_group_key": group_key_by_id.get(
                    member_group.get(name, ""), ""
                ),
                "is_reserved_name": reserved_by_name.get(name, "unknown"),
                "equation_parent": equation_parent_by_name.get(name, ""),
                "authorship_signal": authorship_signal(
                    name, reserved_by_name, source_paths
                ),
                "generated_name_signal": str(
                    bool(GENERATED_NAME_RE.search(name))
                ).lower(),
                "explicit_source_declaration_signal": str(
                    bool(source_paths.get(name))
                ).lower(),
                "source_paths": " | ".join(sorted(source_paths.get(name, set()))),
                **manual_values(previous_isolates, name, MANUAL_ISOLATE_FIELDS),
            }
        )
    isolate_rows.sort(
        key=lambda row: (
            row["is_reserved_name"] == TRUE,
            row["explicit_source_declaration_signal"] != TRUE,
            row["module"],
            row["name"],
        )
    )

    group_fields = [
        "snapshot_commit",
        "group_id",
        "group_key",
        "type_hash",
        "type_equivalence_id",
        "group_size",
        "module_count",
        "nonreserved_member_count",
        "reserved_member_count",
        "unknown_origin_member_count",
        "leaf_member_count",
        "isolated_member_count",
        "used_outside_module_member_count",
        "explicit_source_member_count",
        "generated_name_signal_member_count",
        "has_direct_peer_body_edge",
        "has_direct_peer_type_edge",
        "same_statement_body_edge_count",
        "forwarding_shape",
        "canonical_hint",
        "evidence_bucket",
        "members",
    ]
    canonical_fields = [
        "snapshot_commit",
        "group_id",
        "group_key",
        "group_size",
        "evidence_bucket",
        "forwarding_shape",
        "canonical_hint",
        "name",
        "module",
        "kind",
        "incoming_project_reference_count",
        "direct_project_dependency_count",
        "is_apparent_leaf",
        "is_project_isolated",
        "is_used_outside_module",
        "cross_module_incoming_count",
        "direct_peer_body_targets",
        "direct_peer_type_targets",
        "direct_peer_users",
        "generated_name_signal",
        "is_reserved_name",
        "equation_parent",
        "authorship_signal",
        "explicit_source_declaration_signal",
        "source_paths",
        *MANUAL_CANONICAL_FIELDS,
    ]
    isolate_fields = [
        "snapshot_commit",
        "name",
        "module",
        "kind",
        "incoming_project_reference_count",
        "direct_project_dependency_count",
        "exact_statement_group_id",
        "exact_statement_group_key",
        "is_reserved_name",
        "equation_parent",
        "authorship_signal",
        "generated_name_signal",
        "explicit_source_declaration_signal",
        "source_paths",
        *MANUAL_ISOLATE_FIELDS,
    ]
    write_csv(args.output_dir / "exact_statement_groups.csv", group_fields, group_rows)
    write_csv(
        args.output_dir / "canonical_member_review.csv", canonical_fields, canonical_rows
    )
    write_csv(args.output_dir / "isolated_review.csv", isolate_fields, isolate_rows)
    write_csv(
        args.output_dir / "nonreserved_isolated_declarations.csv",
        isolate_fields,
        [row for row in isolate_rows if row["is_reserved_name"] == "false"],
    )
    write_csv(
        args.output_dir / "reserved_isolated_declarations.csv",
        isolate_fields,
        [row for row in isolate_rows if row["is_reserved_name"] == TRUE],
    )
    write_csv(
        args.output_dir / "unknown_origin_isolated_declarations.csv",
        isolate_fields,
        [row for row in isolate_rows if row["is_reserved_name"] == "unknown"],
    )
    write_csv(
        args.output_dir / "same_statement_body_edges.csv",
        ["group_key", "source_name", "target_name", "same_module"],
        sorted(
            same_statement_body_edges,
            key=lambda row: (row["group_key"], row["source_name"], row["target_name"]),
        ),
    )
    write_csv(
        args.output_dir / "duplicate_member_users.csv",
        [
            "group_key",
            "target_name",
            "source_name",
            "source_module",
            "occurs_in_type",
            "occurs_in_body",
            "same_module",
        ],
        sorted(
            duplicate_member_users,
            key=lambda row: (row["group_key"], row["target_name"], row["source_name"]),
        ),
    )

    summary = {
        "snapshot_commit": args.snapshot_commit,
        "exact_statement_groups": len(groups),
        "exact_statement_members": len(duplicate_rows),
        "groups_with_direct_peer_body_edge": sum(
            row["has_direct_peer_body_edge"] == TRUE for row in group_rows
        ),
        "groups_without_direct_peer_body_edge": sum(
            row["has_direct_peer_body_edge"] != TRUE for row in group_rows
        ),
        "same_statement_body_edges": len(same_statement_body_edges),
        "duplicate_member_incoming_edges": len(duplicate_member_users),
        "public_isolated_declarations": len(public_isolates),
        "nonreserved_public_isolated_declarations": sum(
            row["is_reserved_name"] == "false" for row in isolate_rows
        ),
        "reserved_public_isolated_declarations": sum(
            row["is_reserved_name"] == TRUE for row in isolate_rows
        ),
        "unknown_origin_public_isolated_declarations": sum(
            row["is_reserved_name"] == "unknown" for row in isolate_rows
        ),
        "isolates_with_explicit_source_declaration_signal": sum(
            row["explicit_source_declaration_signal"] == TRUE for row in isolate_rows
        ),
        "isolates_with_generated_name_signal": sum(
            row["generated_name_signal"] == TRUE for row in isolate_rows
        ),
        "origin_csv_supplied": args.origins is not None,
        "evidence_buckets": {
            bucket: sum(row["evidence_bucket"] == bucket for row in group_rows)
            for bucket in sorted({row["evidence_bucket"] for row in group_rows})
        },
        "interpretation": [
            "Exact statement equality is not semantic redundancy.",
            "Direct peer edges suggest delegation but do not prove an alias is intentional.",
            "Reserved-name, source-text, and generated-name fields are evidence, not final roles.",
            "All exact-statement groups are retained; generated members never delete a group.",
            "No row is eligible for deletion without book/API review and explicit approval.",
        ],
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
