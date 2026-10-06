#!/usr/bin/env python3
"""Produce conservative source and compiled-environment proof-hygiene evidence."""

from __future__ import annotations

import csv
import gzip
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path


AUDIT = Path(__file__).resolve().parents[1]
ROOT = AUDIT / "_worktree"
RAW = AUDIT / "raw"
OUT = AUDIT / "hygiene"
METADATA = RAW / "declaration_metadata.csv"
DECLARATIONS = RAW / "declarations.csv.gz"
DEPENDENCIES = RAW / "direct_dependencies.csv.gz"
LEXER_PATH = AUDIT / "static_architecture" / "static_architecture.py"

SCHEMA = "numstability.proof-hygiene.v1"

SOURCE_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "sorryAx": re.compile(r"\bsorryAx\b"),
    "axiom_word": re.compile(r"\baxioms?\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "opaque": re.compile(r"\bopaque\b"),
    "placeholder_marker": re.compile(r"\b(?:placeholder|todo|fixme|dummy|unimplemented)\b", re.I),
}


def load_lexer():
    spec = importlib.util.spec_from_file_location("static_architecture", LEXER_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def module_for(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def write_csv(path: Path, rows: list[dict], fields: list[str]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def scan_source() -> tuple[list[dict], Counter]:
    lexer = load_lexer()
    rows: list[dict] = []
    counts: Counter = Counter()
    paths = sorted((ROOT / "NumStability").rglob("*.lean")) + [ROOT / "NumStability.lean"]
    for path in paths:
        state = lexer.LexState()
        rel = str(path.relative_to(ROOT))
        module = module_for(path)
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(keepends=True), 1):
            _code, classes, state = lexer.lex_line(line, state)
            for term, pattern in SOURCE_PATTERNS.items():
                for match in pattern.finditer(line):
                    pos = match.start()
                    cls = classes[pos] if pos < len(classes) else "C"
                    location = {"C": "code", "M": "comment", "S": "string"}[cls]
                    command_class = ""
                    stripped = line.strip()
                    if term == "axiom_word" and location == "code":
                        if re.match(r"^(?:@\[[^]]*\]\s*)*axioms?\b", stripped):
                            command_class = "axiom_declaration_command"
                        elif "#print axioms" in stripped:
                            command_class = "print_axioms_diagnostic_command"
                        else:
                            command_class = "other_code_use_of_axiom_word"
                    elif term == "native_decide" and location == "code":
                        command_class = "native_decide_tactic"
                    elif term == "opaque" and location == "code":
                        command_class = "opaque_keyword_not_automatically_a_placeholder"
                    counts[(term, location, command_class)] += 1
                    rows.append({
                        "module": module,
                        "source_path": rel,
                        "line": line_no,
                        "term": term,
                        "matched_text": match.group(0),
                        "location_class": location,
                        "command_class": command_class,
                        "source_excerpt": stripped[:500],
                    })
        if state.block_depth or state.in_string:
            raise RuntimeError(f"unbalanced lexical state in {rel}: {state}")
    return rows, counts


def classify_bodyless(row: dict[str, str]) -> tuple[str, str]:
    kind = row["kind"]
    name = row["name"]
    if kind in {"constructor", "recursor", "inductive"}:
        return "expected_environment_declaration", f"{kind} declarations have no value body in this inventory"
    if kind == "axiom" and "._native.native_decide.ax_" in name:
        return "lean_generated_native_decide_axiom", "generated internal helper for a source native_decide proof"
    if kind == "axiom":
        return "review_project_axiom", "project-owned axiom not recognized as a native_decide helper"
    return "unexpected_bodyless_review", "kind normally expected to carry a value/proof body"


def placeholder_rows() -> list[dict]:
    # These are not inferred from weak bodies.  They are declarations explicitly
    # described as legacy placeholders by their own source documentation.
    rel = Path("NumStability/Algorithms/FastMatMul/Internal/LegacyBounds.lean")
    path = ROOT / rel
    text = path.read_text(encoding="utf-8").splitlines()
    names = {
        "StrassenErrorBound": "structure",
        "WinogradInnerProductError": "structure",
        "BilinearAlgorithmError": "structure",
        "ThreeMMethodError": "structure",
    }
    rows: list[dict] = []
    for i, line in enumerate(text, 1):
        for name, kind in names.items():
            if re.match(rf"^\s*{kind}\s+{re.escape(name)}\b", line):
                rows.append({
                    "name": f"NumStability.{name}",
                    "module": "NumStability.Algorithms.FastMatMul.Internal.LegacyBounds",
                    "source_path": str(rel),
                    "line": i,
                    "kind": kind,
                    "classification": "explicitly_documented_legacy_placeholder_interface",
                    "reason": (
                        "The declaration's doc comment explicitly calls it a legacy placeholder; "
                        "this is an API/content-quality signal, not a missing proof or an axiom."
                    ),
                })
    return rows


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    source_rows, source_counts = scan_source()
    write_csv(
        OUT / "source_proof_hygiene_occurrences.csv",
        source_rows,
        ["module", "source_path", "line", "term", "matched_text", "location_class", "command_class", "source_excerpt"],
    )
    code_rows = [r for r in source_rows if r["location_class"] == "code"]
    write_csv(
        OUT / "source_proof_hygiene_code_occurrences.csv",
        code_rows,
        ["module", "source_path", "line", "term", "matched_text", "location_class", "command_class", "source_excerpt"],
    )

    with METADATA.open(newline="", encoding="utf-8") as handle:
        metadata_rows = list(csv.DictReader(handle))
    with gzip.open(DECLARATIONS, "rt", newline="", encoding="utf-8") as handle:
        declarations = list(csv.DictReader(handle))
    by_name = {r["name"]: r for r in metadata_rows}

    unsafe_rows = [r for r in metadata_rows if r["is_unsafe"] == "true"]
    partial_rows = []
    for r in metadata_rows:
        if r["is_partial"] != "true":
            continue
        enriched = dict(r)
        if r["is_internal"] == "true" and r["name"].endswith("._unsafe_rec"):
            enriched["classification"] = "lean_generated_internal_partial_recursion_helper"
            enriched["classification_explanation"] = (
                "Lean-generated internal _unsafe_rec implementation helper; not an explicitly "
                "source-written public partial declaration and not a proof placeholder"
            )
        else:
            enriched["classification"] = "partial_declaration_requiring_review"
            enriched["classification_explanation"] = "compiled declaration carries the partial flag"
        partial_rows.append(enriched)
    bodyless: list[dict] = []
    axiom_rows: list[dict] = []
    for row in declarations:
        if row["has_body"] != "true":
            classification, explanation = classify_bodyless(row)
            enriched = dict(row)
            enriched.update({"classification": classification, "classification_explanation": explanation})
            bodyless.append(enriched)
            if row["kind"] == "axiom":
                axiom_rows.append(enriched)

    write_csv(
        OUT / "compiled_bodyless_declarations.csv",
        bodyless,
        list(bodyless[0].keys()) if bodyless else ["name"],
    )
    write_csv(
        OUT / "compiled_project_axioms.csv",
        axiom_rows,
        list(axiom_rows[0].keys()) if axiom_rows else ["name"],
    )
    write_csv(
        OUT / "compiled_unsafe_declarations.csv",
        unsafe_rows,
        list(metadata_rows[0].keys()),
    )
    write_csv(
        OUT / "compiled_partial_declarations.csv",
        partial_rows,
        list(partial_rows[0].keys()) if partial_rows else list(metadata_rows[0].keys()),
    )

    axiom_names = {r["name"] for r in axiom_rows}
    axiom_edges: list[dict] = []
    sorry_edges: list[dict] = []
    dependency_edge_total = 0
    with gzip.open(DEPENDENCIES, "rt", newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            dependency_edge_total += 1
            target = row["target"]
            if target in axiom_names:
                axiom_edges.append(row)
            if target == "sorryAx" or target.endswith(".sorryAx"):
                sorry_edges.append(row)
    dep_fields = [
        "source", "source_module", "target", "target_module", "target_scope",
        "occurs_in_type", "occurs_in_body", "same_module",
    ]
    write_csv(OUT / "compiled_project_axiom_dependency_edges.csv", axiom_edges, dep_fields)
    write_csv(OUT / "compiled_sorryAx_dependency_edges.csv", sorry_edges, dep_fields)

    placeholders = placeholder_rows()
    write_csv(
        OUT / "placeholder_like_source_declarations.csv",
        placeholders,
        ["name", "module", "source_path", "line", "kind", "classification", "reason"],
    )

    bodyless_counts = Counter(r["classification"] for r in bodyless)
    axiom_consumer_counts = Counter(r["target"] for r in axiom_edges)
    source_code = Counter(r["term"] for r in code_rows)
    summary = {
        "schema_version": SCHEMA,
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "universes": {
            "compiled_project_owned_declarations": len(declarations),
            "compiled_metadata_rows": len(metadata_rows),
            "all_direct_dependency_edges_project_to_project_or_external": dependency_edge_total,
            "source_files": len(list((ROOT / "NumStability").rglob("*.lean"))) + 1,
        },
        "compiled": {
            "bodyless_total": len(bodyless),
            "bodyless_by_classification": dict(sorted(bodyless_counts.items())),
            "axiom_kind_total": len(axiom_rows),
            "recognized_generated_native_decide_axioms": sum(
                r["classification"] == "lean_generated_native_decide_axiom" for r in axiom_rows
            ),
            "unrecognized_project_axioms_requiring_review": sum(
                r["classification"] == "review_project_axiom" for r in axiom_rows
            ),
            "unsafe_declarations": len(unsafe_rows),
            "partial_declarations": len(partial_rows),
            "generated_internal_partial_recursion_helpers": sum(
                r["classification"] == "lean_generated_internal_partial_recursion_helper" for r in partial_rows
            ),
            "other_partial_declarations_requiring_review": sum(
                r["classification"] == "partial_declaration_requiring_review" for r in partial_rows
            ),
            "direct_dependency_edges_to_sorryAx": len(sorry_edges),
            "direct_dependency_edges_to_project_owned_axioms": len(axiom_edges),
            "distinct_project_declarations_directly_using_project_owned_axioms": len({r["source"] for r in axiom_edges}),
            "axiom_direct_consumer_counts": dict(sorted(axiom_consumer_counts.items())),
        },
        "source_lexical": {
            "all_occurrences_by_term_and_location": {
                "|".join(k): v for k, v in sorted(source_counts.items())
            },
            "code_occurrences_by_term": dict(sorted(source_code.items())),
            "axiom_declaration_commands": sum(
                r["command_class"] == "axiom_declaration_command" for r in code_rows
            ),
            "print_axioms_diagnostic_commands": sum(
                r["command_class"] == "print_axioms_diagnostic_command" for r in code_rows
            ),
            "explicitly_documented_legacy_placeholder_interfaces": len(placeholders),
        },
        "interpretation": {
            "opaque": "Opacity is not treated as evidence of a placeholder.",
            "native_decide": (
                "Generated native_decide axiom helpers are separated from explicit source axiom commands. "
                "They are trusted-code evidence, not proof holes and not source-introduced mathematical assumptions."
            ),
            "source_matches": "Comment and string matches are not counted as source proof commands.",
            "dependency_scope": "sorryAx and project-axiom counts use direct elaborated dependency rows.",
        },
        "raw_artifacts": {
            "metadata": str(METADATA.relative_to(AUDIT)),
            "declarations": str(DECLARATIONS.relative_to(AUDIT)),
            "dependencies": str(DEPENDENCIES.relative_to(AUDIT)),
            "source_occurrences": "hygiene/source_proof_hygiene_occurrences.csv",
        },
    }
    (OUT / "proof_hygiene_summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    result_rows = [
        {
            "check": "source_sorry_commands", "numerator": source_code.get("sorry", 0),
            "denominator": summary["universes"]["source_files"], "universe": "all NumStability Lean source files",
            "filters": "lexically located in code, excluding comments and strings",
            "artifact": "hygiene/source_proof_hygiene_code_occurrences.csv", "column": "term=sorry",
        },
        {
            "check": "source_admit_commands", "numerator": source_code.get("admit", 0),
            "denominator": summary["universes"]["source_files"], "universe": "all NumStability Lean source files",
            "filters": "lexically located in code, excluding comments and strings",
            "artifact": "hygiene/source_proof_hygiene_code_occurrences.csv", "column": "term=admit",
        },
        {
            "check": "source_sorryAx_references", "numerator": source_code.get("sorryAx", 0),
            "denominator": summary["universes"]["source_files"], "universe": "all NumStability Lean source files",
            "filters": "lexically located in code, excluding comments and strings",
            "artifact": "hygiene/source_proof_hygiene_code_occurrences.csv", "column": "term=sorryAx",
        },
        {
            "check": "source_axiom_declaration_commands", "numerator": summary["source_lexical"]["axiom_declaration_commands"],
            "denominator": summary["universes"]["source_files"], "universe": "all NumStability Lean source files",
            "filters": "code lines whose introducer is axiom or axioms; excludes #print axioms",
            "artifact": "hygiene/source_proof_hygiene_code_occurrences.csv", "column": "command_class=axiom_declaration_command",
        },
        {
            "check": "compiled_edges_to_sorryAx", "numerator": len(sorry_edges),
            "denominator": dependency_edge_total, "universe": "all extracted direct dependency edges from project declarations to project or external declarations",
            "filters": "target equals sorryAx or ends with .sorryAx",
            "artifact": "hygiene/compiled_sorryAx_dependency_edges.csv", "column": "target",
        },
        {
            "check": "compiled_unsafe_declarations", "numerator": len(unsafe_rows),
            "denominator": len(metadata_rows), "universe": "all project-owned compiled environment declarations",
            "filters": "DeclarationInfo.isUnsafe=true",
            "artifact": "hygiene/compiled_unsafe_declarations.csv", "column": "is_unsafe",
        },
        {
            "check": "source_native_decide_tactics", "numerator": source_code.get("native_decide", 0),
            "denominator": summary["universes"]["source_files"], "universe": "all NumStability Lean source files",
            "filters": "native_decide token lexically located in code, excluding comments and strings",
            "artifact": "hygiene/source_proof_hygiene_code_occurrences.csv", "column": "term=native_decide",
        },
        {
            "check": "compiled_generated_native_decide_axioms", "numerator": sum(r["classification"] == "lean_generated_native_decide_axiom" for r in axiom_rows),
            "denominator": len(declarations), "universe": "all project-owned compiled environment declarations",
            "filters": "kind=axiom and generated name contains ._native.native_decide.ax_",
            "artifact": "hygiene/compiled_project_axioms.csv", "column": "classification",
        },
        {
            "check": "compiled_unrecognized_project_axioms", "numerator": sum(r["classification"] == "review_project_axiom" for r in axiom_rows),
            "denominator": len(declarations), "universe": "all project-owned compiled environment declarations",
            "filters": "kind=axiom excluding recognized native_decide generated helpers",
            "artifact": "hygiene/compiled_project_axioms.csv", "column": "classification",
        },
        {
            "check": "compiled_unexpected_bodyless_declarations", "numerator": sum(r["classification"] == "unexpected_bodyless_review" for r in bodyless),
            "denominator": len(declarations), "universe": "all project-owned compiled environment declarations",
            "filters": "has_body=false excluding constructors, recursors, inductives, and recognized native_decide axiom helpers",
            "artifact": "hygiene/compiled_bodyless_declarations.csv", "column": "classification",
        },
        {
            "check": "compiled_generated_internal_partial_recursion_helpers", "numerator": sum(r["classification"] == "lean_generated_internal_partial_recursion_helper" for r in partial_rows),
            "denominator": len(declarations), "universe": "all project-owned compiled environment declarations",
            "filters": "is_partial=true, is_internal=true, generated name suffix ._unsafe_rec",
            "artifact": "hygiene/compiled_partial_declarations.csv", "column": "classification",
        },
        {
            "check": "compiled_other_partial_declarations_requiring_review", "numerator": sum(r["classification"] == "partial_declaration_requiring_review" for r in partial_rows),
            "denominator": len(declarations), "universe": "all project-owned compiled environment declarations",
            "filters": "is_partial=true excluding recognized internal ._unsafe_rec generated helpers",
            "artifact": "hygiene/compiled_partial_declarations.csv", "column": "classification",
        },
        {
            "check": "explicitly_documented_legacy_placeholder_interfaces", "numerator": len(placeholders),
            "denominator": len(declarations), "universe": "all project-owned compiled environment declarations",
            "filters": "source declaration explicitly described as a legacy placeholder in its doc comment; conservative lexical review",
            "artifact": "hygiene/placeholder_like_source_declarations.csv", "column": "classification",
        },
    ]
    write_csv(
        OUT / "proof_hygiene_results.csv",
        result_rows,
        ["check", "numerator", "denominator", "universe", "filters", "artifact", "column"],
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
