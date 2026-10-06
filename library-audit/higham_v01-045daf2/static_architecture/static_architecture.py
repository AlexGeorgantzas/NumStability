#!/usr/bin/env python3
"""Reproducible static architecture inventory for NumStability.

Schema: numstability-static-architecture/1.0.0

This tool intentionally analyzes source text and source import commands only.
It does not claim that an import is an elaborated declaration dependency.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import re
import sys
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path


SCHEMA_VERSION = "numstability-static-architecture/1.0.0"
ROOT_ENTRY_MODULES = {
    "NumStability",
    "NumStability.All",
    "NumStability.Algorithms",
    "NumStability.Analysis",
    "NumStability.FloatingPoint",
    "NumStability.Source",
    "NumStability.Source.Higham",
    "NumStability.Higham",
    "NumStability.Core",
}
TOP_UMBRELLAS = {
    "NumStability",
    "NumStability.All",
    "NumStability.Algorithms",
    "NumStability.Analysis",
    "NumStability.FloatingPoint",
    "NumStability.Source",
    "NumStability.Source.Higham",
    "NumStability.Higham",
}
WORKFLOW_TERMS = (
    "actual", "final", "remaining", "whole", "bridge", "closure", "batch",
)
HYGIENE_TERMS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "sorryAx": re.compile(r"\bsorryAx\b"),
    "axiom_command": re.compile(r"\baxioms?\b"),
    "unsafe_keyword": re.compile(r"\bunsafe\b"),
    "placeholder_word": re.compile(r"\b(?:placeholder|todo|fixme|dummy|unimplemented)\b", re.I),
}
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|local)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|axioms?|constants?|structure|class|inductive|instance|example)\b"
)
COMMAND_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?P<kind>syntax|macro_rules|macro|elab_rules|elab|notation|infixl|infixr|infix|prefix|postfix|"
    r"scoped\s+notation|initialize|register_option|attribute)\b"
)
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.'«»]+)\s*$")


@dataclass
class LexState:
    block_depth: int = 0
    in_string: bool = False
    escaped: bool = False


def lex_line(line: str, state: LexState) -> tuple[str, list[str], LexState]:
    """Return code-only text and per-character C(comment-free)/M(comment)/S(string)."""
    out = list(" " * len(line))
    classes = ["C"] * len(line)
    i = 0
    while i < len(line):
        if state.block_depth:
            classes[i] = "M"
            if line.startswith("/-", i):
                classes[i] = classes[i + 1] = "M"
                state.block_depth += 1
                i += 2
            elif line.startswith("-/", i):
                classes[i] = classes[i + 1] = "M"
                state.block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if state.in_string:
            classes[i] = "S"
            if state.escaped:
                state.escaped = False
            elif line[i] == "\\":
                state.escaped = True
            elif line[i] == '"':
                state.in_string = False
            i += 1
            continue
        if line.startswith("--", i):
            for j in range(i, len(line)):
                classes[j] = "M"
            break
        if line.startswith("/-", i):
            classes[i] = classes[i + 1] = "M"
            state.block_depth = 1
            i += 2
            continue
        if line[i] == '"':
            classes[i] = "S"
            state.in_string = True
            i += 1
            continue
        out[i] = line[i]
        i += 1
    return "".join(out), classes, state


def module_for_path(rel: str) -> str:
    if rel == "NumStability.lean":
        return "NumStability"
    return rel[:-5].replace("/", ".")


def physical_layer(rel: str) -> str:
    if rel == "NumStability.lean" or (rel.startswith("NumStability/") and rel.count("/") == 1):
        return "Root"
    parts = rel.split("/")
    if len(parts) >= 2 and parts[1] in {"Examples", "Source", "Algorithms", "Analysis", "FloatingPoint", "Upstream"}:
        return parts[1]
    return "Other"


def effective_layer(module: str, physical: str) -> str:
    if module == "NumStability" or module.startswith("NumStability.All"):
        return "Root"
    if module == "NumStability.Higham" or module.startswith("NumStability.Higham."):
        return "SourceCompat"
    if physical == "Root":
        for layer in ("Examples", "Source", "Algorithms", "Analysis", "FloatingPoint"):
            if module == f"NumStability.{layer}":
                return layer
    return physical


def chapter_guess(module: str) -> tuple[str, str]:
    m = re.search(r"(?:^|\.)(Chapter)(\d{2})(?:\.|$)", module)
    if m:
        return m.group(2), "canonical_ChapterNN"
    m = re.search(r"(?:^|\.)(?:HighamChapter|Chapter|Ch)(\d{1,2})(?:\.|[A-Z_]|$)", module)
    if m:
        return m.group(1).zfill(2), "noncanonical_name_signal"
    m = re.search(r"Higham(\d{1,2})(?:\.|[A-Z_]|$)", module)
    if m:
        return m.group(1).zfill(2), "embedded_name_signal"
    return "", ""


DOMAIN_RULES = [
    ("SymmetricIndefinite", r"SymmetricIndefinite|BunchKaufman|BlockLDLT|Aasen|RookPivot|SkewSymmetric"),
    ("LeastSquares", r"LeastSquares|MinimumNorm|Underdetermined|Seminormal"),
    ("MatrixEquations", r"MatrixEquations|Sylvester|Lyapunov"),
    ("Cholesky", r"Cholesky|PositiveSemidefinite|PositiveDefinite"),
    ("LU", r"(?:^|\.)(?:LU|LUSolve|Doolittle|GaussianElimination|BlockLU|TridiagonalLU)(?:\.|$)|LUFactor|Pivot"),
    ("QR", r"(?:^|\.)(?:QR|Householder|GramSchmidt|Givens)(?:\.|$)|QRSolve"),
    ("Summation", r"Summation|Compensated|Kahan|Neumaier|Priest|InsertionSum|PairwiseSum|TreeSum"),
    ("DotProduct", r"DotProduct|DotProd|BlockDot|MatVec|OuterProduct"),
    ("MatrixMultiplication", r"MatMul|MatrixProduct|FastMatMul|MatSeqProduct"),
    ("Norms", r"NormEstimation|MatrixNorm|VectorNorm|OperatorNorm|Norm2|PNorm|OneNorm|TwoNorm|Condition"),
    ("Perturbation", r"(?:^|\.)(?:Perturbation|BackwardError|ForwardError|Residual|Stability)(?:\.|$)|PerturbationTheory|ErrorBound"),
    ("FloatingPoint", r"FloatingPoint|Rounding|Roundoff|IEEE|Ieee|FusedMultiplyAdd|UnitRoundoff|Precision"),
    ("MatrixPowers", r"MatrixPower|MatrixFunctions|FunctionalCalculus|Resolvent|Kreiss|Semiconvergen"),
    ("Spectral", r"Eigen|Spectral|SingularValue|Jordan|Schur|NumericalRadius"),
    ("Polynomials", r"Polynomial|Horner|Vandermonde|PatersonStockmeyer"),
    ("ProbabilityStatistics", r"Probability|Statistics|Variance|Gaussian|Haar"),
    ("Nonlinear", r"Nonlinear|Newton|Aitken"),
    ("FFT", r"(?:^|\.)FFT(?:\.|$)|Fourier|Circulant"),
    ("TestMatrices", r"TestMatrices|Wilkinson|Hilbert|Hadamard"),
    ("Arithmetic", r"Arithmetic|ComplexArithmetic|SquareDifference|Quadratic|LogExp"),
]


def domain_guess(module: str) -> str:
    for label, pat in DOMAIN_RULES:
        if re.search(pat, module, re.I):
            return label
    if module.startswith("NumStability.Source.Higham") or module.startswith("NumStability.Higham"):
        return "HighamSourceOther"
    return "Other"


def workflow_signals(module: str) -> list[str]:
    tokens: set[str] = set()
    for component in module.split("."):
        for piece in re.split(r"[_-]+", component):
            tokens.update(x.lower() for x in re.findall(r"[A-Z]+(?=[A-Z][a-z]|[0-9]|$)|[A-Z]?[a-z]+|[0-9]+", piece))
    return sorted(tokens & set(WORKFLOW_TERMS))


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def nearest_rank_percentiles(values: list[int]) -> dict[str, int]:
    ordered = sorted(values)
    return {
        str(p): ordered[max(0, math.ceil(p * len(ordered)) - 1)]
        for p in (0.5, 0.75, 0.9, 0.95, 0.99, 1.0)
    }


def write_csv(path: Path, rows: list[dict], fieldnames: list[str] | None = None) -> None:
    if fieldnames is None:
        fieldnames = list(rows[0]) if rows else []
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)


def closure(start: str, adjacency: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    todo = list(adjacency.get(start, []))
    while todo:
        cur = todo.pop()
        if cur in seen:
            continue
        seen.add(cur)
        todo.extend(adjacency.get(cur, []))
    return seen


def shortest_distance_to_layers(start: str, adjacency: dict[str, list[str]], layer_of: dict[str, str], targets: set[str]) -> tuple[int | None, str]:
    q = deque([(start, 0)])
    seen = {start}
    while q:
        cur, d = q.popleft()
        if cur != start and layer_of.get(cur) in targets:
            return d, cur
        for nxt in adjacency.get(cur, []):
            if nxt not in seen:
                seen.add(nxt)
                q.append((nxt, d + 1))
    return None, ""


def tarjan(nodes: list[str], adjacency: dict[str, list[str]]) -> list[list[str]]:
    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    low: dict[str, int] = {}
    comps: list[list[str]] = []

    def visit(v: str) -> None:
        nonlocal index
        indices[v] = low[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)
        for w in adjacency.get(v, []):
            if w not in indices:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], indices[w])
        if low[v] == indices[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            comps.append(sorted(comp))

    for node in nodes:
        if node not in indices:
            visit(node)
    return comps


def validate_lexer() -> dict:
    sample = [
        "import NumStability.Analysis -- sorry\n",
        "/- outer /- nested sorry -/ comment -/ theorem ok : True := by trivial\n",
        'def s := "sorry -- not comment"\n',
        "axiom projectAssumption : True\n",
    ]
    state = LexState()
    code = []
    classes = []
    for line in sample:
        c, k, state = lex_line(line, state)
        code.append(c)
        classes.append(k)
    assertions = {
        "import_preserved": code[0].strip() == "import NumStability.Analysis",
        "line_comment_removed": "sorry" not in code[0],
        "nested_block_comment_removed": "nested" not in code[1] and "theorem ok" in code[1],
        "string_removed_from_code": "sorry" not in code[2] and "def s :=" in code[2],
        "axiom_preserved": "axiom projectAssumption" in code[3],
        "balanced_state": state.block_depth == 0 and not state.in_string,
        "root_module_mapping": module_for_path("NumStability.lean") == "NumStability",
        "nested_module_mapping": module_for_path("NumStability/Algorithms/Summation/Basic.lean") == "NumStability.Algorithms.Summation.Basic",
        "physical_layer_mapping": physical_layer("NumStability/Source/Higham/Chapter09.lean") == "Source",
        "canonical_chapter_mapping": chapter_guess("NumStability.Source.Higham.Chapter09.Basic") == ("09", "canonical_ChapterNN"),
        "numstability_prefix_not_false_perturbation": domain_guess("NumStability.Source.Higham.Chapter09.Basic") == "HighamSourceOther",
        "workflow_camelcase_detected": workflow_signals("NumStability.Algorithms.ActualExecutorBridge") == ["actual", "bridge"],
        "householder_not_old_signal": workflow_signals("NumStability.Algorithms.QR.Householder") == [],
        "source_import_orientation_rank": {"FloatingPoint": 0, "Analysis": 1, "Algorithms": 2, "Source": 3, "Examples": 4}["Algorithms"] > {"FloatingPoint": 0, "Analysis": 1, "Algorithms": 2, "Source": 3, "Examples": 4}["Analysis"],
    }
    if not all(assertions.values()):
        raise AssertionError(assertions)
    return {"sample": sample, "assertions": assertions, "passed": True}


def analyze(root: Path, output: Path) -> dict:
    source_paths = [root / "NumStability.lean"] + sorted((root / "NumStability").rglob("*.lean"))
    module_names = {module_for_path(str(p.relative_to(root))) for p in source_paths}
    module_rows: list[dict] = []
    import_rows: list[dict] = []
    hygiene_rows: list[dict] = []
    decl_rows: list[dict] = []
    naming_rows: list[dict] = []
    info: dict[str, dict] = {}

    for path in source_paths:
        rel = str(path.relative_to(root))
        module = module_for_path(rel)
        physical = physical_layer(rel)
        effective = effective_layer(module, physical)
        chapter, chapter_method = chapter_guess(module)
        domain = domain_guess(module)
        raw = path.read_text(encoding="utf-8")
        lines = raw.splitlines(keepends=True)
        state = LexState()
        imports: list[tuple[str, int]] = []
        decl_counts: Counter = Counter()
        command_counts: Counter = Counter()
        blank = 0
        code_lines = 0
        comment_only = 0
        string_only = 0
        code_cache: list[str] = []
        class_cache: list[list[str]] = []
        for line_no, line in enumerate(lines, 1):
            if not line.strip():
                blank += 1
            code, classes, state = lex_line(line, state)
            code_cache.append(code)
            class_cache.append(classes)
            if code.strip():
                code_lines += 1
            elif any(c == "M" for c in classes):
                comment_only += 1
            elif any(c == "S" for c in classes):
                string_only += 1
            m = IMPORT_RE.match(code.strip())
            if m:
                imports.append((m.group(1), line_no))
            dm = DECL_RE.match(code)
            if dm:
                kind = dm.group("kind")
                normalized_kind = {"axioms": "axiom", "constants": "constant"}.get(kind, kind)
                decl_counts[normalized_kind] += 1
                name_part = code[dm.end():].strip()
                name_match = re.match(r"(?:«[^»]+»|[^\s:{[(]+)", name_part)
                decl_rows.append({
                    "module": module,
                    "source_path": rel,
                    "line": line_no,
                    "kind": normalized_kind,
                    "name_guess": name_match.group(0) if name_match else "",
                    "source_excerpt": line.strip()[:500],
                    "note": "Static declaration-introducer match; not an elaborated declaration inventory.",
                })
            cm = COMMAND_RE.match(code)
            if cm:
                command_counts[cm.group("kind").replace(" ", "_")] += 1
            for term, pat in HYGIENE_TERMS.items():
                for match in pat.finditer(line):
                    pos = match.start()
                    cls = classes[pos] if pos < len(classes) else "C"
                    location = {"C": "code", "M": "comment", "S": "string"}[cls]
                    hygiene_rows.append({
                        "module": module,
                        "source_path": rel,
                        "line": line_no,
                        "term": term,
                        "matched_text": match.group(0),
                        "location_class": location,
                        "source_excerpt": line.strip()[:500],
                        "interpretation": "Static lexical occurrence only; compiled-environment checks are required for proof dependency claims.",
                    })
        if state.block_depth or state.in_string:
            raise ValueError(f"Unbalanced lexical state in {rel}: {state}")
        import_names = [x for x, _ in imports]
        internal = [x for x in import_names if x in module_names]
        external = [x for x in import_names if x not in module_names]
        decl_total = sum(decl_counts.values())
        cmd_total = sum(command_counts.values())
        doc_lower = raw[:12000].lower()
        declaration_free = decl_total == 0
        aggregate_candidate = declaration_free and bool(import_names) and (
            module in ROOT_ENTRY_MODULES or module.endswith(".All") or
            "aggregate" in doc_lower or "entry point" in doc_lower or "re-export" in doc_lower or "complete tree" in doc_lower
        )
        compatibility_candidate = declaration_free and bool(import_names) and (
            bool(re.search(r"compatibility\s+(?:module|import|entry\s+point|shim|wrapper\b|re-export)", doc_lower)) or
            bool(re.search(r"historical\s+(?:entry\s+point|module|import)", doc_lower)) or
            "import-only module retained" in doc_lower or "forwards to" in doc_lower or
            module == "NumStability" or module == "NumStability.Higham" or module.startswith("NumStability.Higham.")
        )
        signals = workflow_signals(module)
        for signal in signals:
            naming_rows.append({
                "module": module,
                "source_path": rel,
                "physical_layer": physical,
                "effective_layer": effective,
                "signal": signal,
                "scope_interpretation": "canonical_layer_review_signal" if physical in {"Algorithms", "Analysis", "FloatingPoint"} else "source_or_other_name_signal",
                "note": "Name substring signal only; not a finding that the module is incoherent.",
            })
        row = {
            "module": module,
            "source_path": rel,
            "sha256": sha256(path),
            "physical_layer": physical,
            "effective_architectural_layer": effective,
            "chapter_guess": chapter,
            "chapter_guess_method": chapter_method,
            "domain_guess": domain,
            "physical_lines": len(lines),
            "blank_lines": blank,
            "code_bearing_lines": code_lines,
            "comment_only_lines": comment_only,
            "string_only_lines": string_only,
            "bytes": path.stat().st_size,
            "direct_import_count": len(import_names),
            "direct_internal_import_count": len(internal),
            "direct_external_import_count": len(external),
            "direct_imports": ";".join(import_names),
            "static_declaration_starter_count": decl_total,
            "static_elaboration_command_count": cmd_total,
            "theorem_count": decl_counts["theorem"],
            "lemma_count": decl_counts["lemma"],
            "def_count": decl_counts["def"],
            "abbrev_count": decl_counts["abbrev"],
            "opaque_count": decl_counts["opaque"],
            "axiom_count": decl_counts["axiom"],
            "constant_count": decl_counts["constant"],
            "structure_count": decl_counts["structure"],
            "class_count": decl_counts["class"],
            "inductive_count": decl_counts["inductive"],
            "instance_count": decl_counts["instance"],
            "example_count": decl_counts["example"],
            "declaration_free_static": str(declaration_free).lower(),
            "aggregate_candidate_static": str(aggregate_candidate).lower(),
            "compatibility_candidate_static": str(compatibility_candidate).lower(),
            "workflow_name_signals": ";".join(signals),
            "metric_note": "Lines and syntax matches are static source metrics; declarations and dependencies require elaborated artifacts.",
        }
        module_rows.append(row)
        info[module] = {**row, "imports_pairs": imports, "imports_list": import_names, "internal": internal, "external": external}

    layer_of = {m: d["effective_architectural_layer"] for m, d in info.items()}
    adjacency = {m: list(dict.fromkeys(d["internal"])) for m, d in info.items()}
    desired_rank = {"FloatingPoint": 0, "Analysis": 1, "Algorithms": 2, "Source": 3, "SourceCompat": 3, "Examples": 4}
    for importer, d in info.items():
        for imported, line_no in d["imports_pairs"]:
            resolved = imported in info
            imported_physical = info[imported]["physical_layer"] if resolved else "External"
            imported_effective = info[imported]["effective_architectural_layer"] if resolved else "External"
            importer_eff = d["effective_architectural_layer"]
            status = "external_or_unclassified"
            if resolved and importer_eff == imported_effective:
                status = "same_layer"
            elif resolved and importer_eff in desired_rank and imported_effective in desired_rank:
                status = "allowed_downward" if desired_rank[importer_eff] > desired_rank[imported_effective] else "apparent_reverse_direction"
            elif resolved:
                status = "internal_unclassified_layer"
            compatibility_exception = d["compatibility_candidate_static"] == "true"
            import_rows.append({
                "importer_module": importer,
                "importer_source_path": d["source_path"],
                "import_line": line_no,
                "imported_module": imported,
                "is_project_module": str(resolved).lower(),
                "importer_physical_layer": d["physical_layer"],
                "imported_physical_layer": imported_physical,
                "importer_effective_layer": importer_eff,
                "imported_effective_layer": imported_effective,
                "layer_direction_class": status,
                "importer_has_static_declarations": str(d["static_declaration_starter_count"] > 0).lower(),
                "importer_compatibility_candidate": str(compatibility_exception).lower(),
                "edge_semantics": "Source import only; not an elaborated logical declaration edge.",
            })

    # Reachability, entry points, source wrapper surface, broad imports.
    entry_rows: list[dict] = []
    source_wrapper_rows: list[dict] = []
    broad_rows: list[dict] = []
    aggregate_import_rows: list[dict] = []
    layer_reachability_rows: list[dict] = []
    reachability_by_module: dict[str, set[str]] = {}
    declaration_bearing_modules = {m for m, d in info.items() if d["static_declaration_starter_count"] > 0}
    for module, d in info.items():
        reachable = closure(module, adjacency)
        reachability_by_module[module] = reachable
        reachable_including_self = reachable | {module}
        reachable_layers = Counter(layer_of.get(x, "External") for x in reachable)
        if d["aggregate_candidate_static"] == "true" or module in ROOT_ENTRY_MODULES:
            kind = "root_entry" if module in ROOT_ENTRY_MODULES else ("all_aggregate" if module.endswith(".All") else "documented_aggregate")
            entry_rows.append({
                "module": module,
                "source_path": d["source_path"],
                "entry_kind": kind,
                "declaration_free_static": d["declaration_free_static"],
                "compatibility_candidate_static": d["compatibility_candidate_static"],
                "direct_internal_import_count": len(adjacency[module]),
                "direct_internal_imports": ";".join(adjacency[module]),
                "reachable_project_module_count": len(reachable),
                "reachable_project_module_count_including_entry": len(reachable_including_self),
                "reachable_declaration_bearing_module_count_including_entry": len(reachable_including_self & declaration_bearing_modules),
                "declaration_bearing_module_universe": len(declaration_bearing_modules),
                "reachable_static_declaration_starter_count": sum(info[x]["static_declaration_starter_count"] for x in reachable_including_self),
                "static_declaration_starter_universe": sum(info[x]["static_declaration_starter_count"] for x in info),
                "reachable_FloatingPoint_modules": reachable_layers["FloatingPoint"],
                "reachable_Analysis_modules": reachable_layers["Analysis"],
                "reachable_Algorithms_modules": reachable_layers["Algorithms"],
                "reachable_Source_modules": reachable_layers["Source"],
                "reachable_SourceCompat_modules": reachable_layers["SourceCompat"],
                "reachable_Other_modules": reachable_layers["Other"],
                "reachable_Upstream_modules": reachable_layers["Upstream"],
                "reachability_semantics": "Source-import transitive closure over modules present in this snapshot; not declaration visibility proof.",
            })
        if d["physical_layer"] == "Source" and d["static_declaration_starter_count"] > 0:
            dist, target = shortest_distance_to_layers(module, adjacency, layer_of, {"Algorithms", "Analysis", "FloatingPoint"})
            direct_lower = [x for x in adjacency[module] if layer_of.get(x) in {"Algorithms", "Analysis", "FloatingPoint"}]
            if d["code_bearing_lines"] <= 100 and d["static_declaration_starter_count"] <= 5:
                bucket = "small_source_surface_candidate"
            elif d["code_bearing_lines"] > 500 or d["static_declaration_starter_count"] > 20:
                bucket = "substantial_source_module_review_candidate"
            else:
                bucket = "medium_source_module"
            source_wrapper_rows.append({
                "module": module,
                "source_path": d["source_path"],
                "chapter_guess": d["chapter_guess"],
                "domain_guess": d["domain_guess"],
                "physical_lines": d["physical_lines"],
                "blank_lines": d["blank_lines"],
                "code_bearing_lines": d["code_bearing_lines"],
                "static_declaration_starter_count": d["static_declaration_starter_count"],
                "direct_lower_layer_import_count": len(direct_lower),
                "direct_lower_layer_imports": ";".join(direct_lower),
                "shortest_import_path_to_lower_layer": "" if dist is None else dist,
                "one_nearest_lower_layer_module": target,
                "static_size_bucket": bucket,
                "interpretation": "Size/import-structure signal only; proof-body edges are needed to establish delegation or independent implementation.",
            })
        if d["physical_layer"] in {"FloatingPoint", "Analysis", "Algorithms"}:
            own_rank = desired_rank[d["physical_layer"]]
            higher_layers = {layer for layer, rank in desired_rank.items() if rank > own_rank}
            dist, target = shortest_distance_to_layers(module, adjacency, layer_of, higher_layers)
            direct_reverse = [x for x in adjacency[module] if layer_of.get(x) in higher_layers]
            layer_reachability_rows.append({
                "module": module,
                "source_path": d["source_path"],
                "physical_layer": d["physical_layer"],
                "has_static_declarations": str(d["static_declaration_starter_count"] > 0).lower(),
                "compatibility_candidate_static": d["compatibility_candidate_static"],
                "direct_reverse_layer_import_count": len(direct_reverse),
                "direct_reverse_layer_imports": ";".join(direct_reverse),
                "shortest_source_import_path_to_higher_layer": "" if dist is None else dist,
                "one_reached_higher_layer_module": target,
                "interpretation": "Source-import reachability only; this does not establish an elaborated declaration dependency.",
            })
        if d["static_declaration_starter_count"] > 0:
            for imported, line_no in d["imports_pairs"]:
                broad_kind = ""
                if imported in {"NumStability", "NumStability.All"}:
                    broad_kind = "complete_tree_umbrella"
                elif imported in TOP_UMBRELLAS:
                    broad_kind = "top_level_entry_point"
                elif imported.endswith(".All"):
                    broad_kind = "subtree_All_aggregate"
                if broad_kind:
                    broad_rows.append({
                        "importer_module": module,
                        "importer_source_path": d["source_path"],
                        "import_line": line_no,
                        "importer_physical_layer": d["physical_layer"],
                        "imported_module": imported,
                        "broad_import_kind": broad_kind,
                        "review_scope": "implementation_module_by_static_declaration_starter",
                        "interpretation": "Review candidate only; imports may supply notation, tactics, attributes, macros, or instances.",
                    })
                if imported in info and info[imported]["aggregate_candidate_static"] == "true":
                    width = len(closure(imported, adjacency))
                    aggregate_import_rows.append({
                        "importer_module": module,
                        "importer_source_path": d["source_path"],
                        "import_line": line_no,
                        "importer_physical_layer": d["physical_layer"],
                        "imported_aggregate_module": imported,
                        "imported_aggregate_reachable_project_modules": width,
                        "static_width_bucket": "broad_ge_50" if width >= 50 else ("medium_10_to_49" if width >= 10 else "narrow_lt_10"),
                        "interpretation": "Detected aggregate import and source-import closure width; review candidate only, not proof of excess or logical dependency.",
                    })

    inversion_rows = [r for r in import_rows if r["layer_direction_class"] == "apparent_reverse_direction"]
    canonical_inversions = [r for r in inversion_rows if r["importer_physical_layer"] in {"Algorithms", "Analysis", "FloatingPoint"}]
    implementation_inversions = [r for r in canonical_inversions if r["importer_has_static_declarations"] == "true"]
    import_only_inversions = [r for r in canonical_inversions if r["importer_has_static_declarations"] == "false"]
    algorithms_to_source_implementation_inversions = [
        r for r in implementation_inversions
        if r["importer_effective_layer"] == "Algorithms" and r["imported_effective_layer"] in {"Source", "SourceCompat"}
    ]
    source_to_algorithms = [r for r in import_rows if r["importer_effective_layer"] == "Source" and r["imported_effective_layer"] == "Algorithms"]

    # Source import SCCs.
    sccs = tarjan(sorted(module_names), adjacency)
    scc_rows: list[dict] = []
    for comp_id, comp in enumerate(sorted(sccs, key=lambda c: (-len(c), c)), 1):
        self_loop = len(comp) == 1 and comp[0] in adjacency.get(comp[0], [])
        for member in comp:
            scc_rows.append({
                "component_id": comp_id,
                "component_size": len(comp),
                "is_cycle": str(len(comp) > 1 or self_loop).lower(),
                "module": member,
                "edge_semantics": "SCC of source imports among project modules.",
            })

    # Layer and chapter matrices (unique source-import edges).
    layer_matrix_counts = Counter()
    domain_matrix_counts = Counter()
    chapter_matrix_counts = Counter()
    for r in import_rows:
        if r["is_project_module"] != "true":
            continue
        layer_matrix_counts[(r["importer_effective_layer"], r["imported_effective_layer"])] += 1
        a = info[r["importer_module"]]["domain_guess"]
        b = info[r["imported_module"]]["domain_guess"]
        domain_matrix_counts[(a, b)] += 1
        ca = info[r["importer_module"]]["chapter_guess"] or "NoChapter"
        cb = info[r["imported_module"]]["chapter_guess"] or "NoChapter"
        chapter_matrix_counts[(ca, cb)] += 1
    layer_matrix_rows = [{"importer_layer": a, "imported_layer": b, "unique_source_import_edges": n, "orientation": "consumer/importer -> imported dependency candidate"} for (a, b), n in sorted(layer_matrix_counts.items())]
    domain_matrix_rows = [{"importer_domain_guess": a, "imported_domain_guess": b, "unique_source_import_edges": n, "metric_note": "Heuristic path-domain classification; source imports only."} for (a, b), n in sorted(domain_matrix_counts.items())]
    chapter_matrix_rows = [{"importer_chapter_guess": a, "imported_chapter_guess": b, "unique_source_import_edges": n, "metric_note": "Explicit/name-signal chapter classification; source imports only."} for (a, b), n in sorted(chapter_matrix_counts.items())]

    # Chapter hierarchy facts by source module.
    chapter_rows: list[dict] = []
    for chapter in [f"{i:02d}" for i in range(1, 29)]:
        prefix = f"NumStability.Source.Higham.Chapter{chapter}"
        members = sorted(m for m in module_names if m == prefix or m.startswith(prefix + "."))
        chapter_rows.append({
            "chapter": chapter,
            "canonical_aggregate_module_present": str(prefix in module_names).lower(),
            "canonical_tree_module_count": len(members),
            "canonical_tree_physical_lines": sum(info[m]["physical_lines"] for m in members),
            "canonical_tree_blank_lines": sum(info[m]["blank_lines"] for m in members),
            "canonical_tree_code_bearing_lines": sum(info[m]["code_bearing_lines"] for m in members),
            "canonical_tree_static_declaration_starters": sum(info[m]["static_declaration_starter_count"] for m in members),
            "aggregate_direct_import_count": len(adjacency.get(prefix, [])),
            "aggregate_reachable_project_module_count": len(closure(prefix, adjacency)) if prefix in module_names else 0,
        })

    declaration_free_rows = []
    for m, d in info.items():
        if d["declaration_free_static"] == "true":
            declaration_free_rows.append({
                "module": m,
                "source_path": d["source_path"],
                "physical_layer": d["physical_layer"],
                "physical_lines": d["physical_lines"],
                "static_elaboration_command_count": d["static_elaboration_command_count"],
                "direct_import_count": d["direct_import_count"],
                "direct_imports": d["direct_imports"],
                "aggregate_candidate_static": d["aggregate_candidate_static"],
                "compatibility_candidate_static": d["compatibility_candidate_static"],
                "interpretation": "No matched declaration introducer; verify against elaborated origins before claiming zero environment declarations.",
            })

    compatibility_rows = [r for r in declaration_free_rows if r["compatibility_candidate_static"] == "true"]
    empty_module_rows = [r for r in declaration_free_rows if int(r["direct_import_count"]) == 0 and int(r["static_elaboration_command_count"]) == 0]
    legacy_higham_rows = [r for r in declaration_free_rows if r["module"] == "NumStability.Higham" or r["module"].startswith("NumStability.Higham.")]
    canonical_layer_source_label_rows = [
        {
            "module": d["module"],
            "source_path": d["source_path"],
            "physical_layer": d["physical_layer"],
            "chapter_guess": d["chapter_guess"],
            "chapter_guess_method": d["chapter_guess_method"],
            "declaration_free_static": d["declaration_free_static"],
            "compatibility_candidate_static": d["compatibility_candidate_static"],
            "direct_imports": d["direct_imports"],
            "interpretation": "Chapter/source-labelled path signal in a canonical physical layer; declaration-free status supports, but does not alone prove, a compatibility role.",
        }
        for d in module_rows
        if d["physical_layer"] in {"Algorithms", "Analysis", "FloatingPoint"} and d["chapter_guess_method"]
    ]
    all_reachable_including_self = closure("NumStability.All", adjacency) | {"NumStability.All"}
    all_missing_rows = []
    for m in sorted(module_names - all_reachable_including_self):
        d = info[m]
        all_missing_rows.append({
            "module": m,
            "source_path": d["source_path"],
            "physical_layer": d["physical_layer"],
            "static_declaration_starter_count": d["static_declaration_starter_count"],
            "declaration_free_static": d["declaration_free_static"],
            "aggregate_candidate_static": d["aggregate_candidate_static"],
            "compatibility_candidate_static": d["compatibility_candidate_static"],
            "interpretation": "Not in NumStability.All source-import closure; absence does not imply that declarations are missing unless the module is declaration-bearing.",
        })
    size_rows = []
    many_imports_few_declarations_rows = []
    for d in module_rows:
        if d["physical_lines"] > 10000 or d["code_bearing_lines"] > 10000:
            size_rows.append({
                "module": d["module"],
                "source_path": d["source_path"],
                "physical_layer": d["physical_layer"],
                "domain_guess": d["domain_guess"],
                "physical_lines": d["physical_lines"],
                "blank_lines": d["blank_lines"],
                "code_bearing_lines": d["code_bearing_lines"],
                "comment_only_lines": d["comment_only_lines"],
                "blank_fraction": round(d["blank_lines"] / d["physical_lines"], 6) if d["physical_lines"] else 0,
                "static_declaration_starter_count": d["static_declaration_starter_count"],
                "static_declaration_starters_per_1000_code_lines": round(1000 * d["static_declaration_starter_count"] / d["code_bearing_lines"], 6) if d["code_bearing_lines"] else 0,
                "metric_contract_physical_line_threshold": "priority_gt_25000" if d["physical_lines"] > 25000 else "review_gt_10000",
                "interpretation": "Size threshold is a review signal, not sufficient evidence that a split is warranted.",
            })
        if d["direct_import_count"] >= 20 and d["static_declaration_starter_count"] <= 5:
            many_imports_few_declarations_rows.append({
                "module": d["module"],
                "source_path": d["source_path"],
                "physical_layer": d["physical_layer"],
                "direct_import_count": d["direct_import_count"],
                "direct_internal_import_count": d["direct_internal_import_count"],
                "static_declaration_starter_count": d["static_declaration_starter_count"],
                "declaration_free_static": d["declaration_free_static"],
                "aggregate_candidate_static": d["aggregate_candidate_static"],
                "compatibility_candidate_static": d["compatibility_candidate_static"],
                "selection_formula": "direct_import_count >= 20 and static_declaration_starter_count <= 5",
                "interpretation": "Static review candidate for re-export/umbrella behavior; not evidence that an import is removable.",
            })

    # Write primary artifacts.
    write_csv(output / "modules.csv", sorted(module_rows, key=lambda r: r["module"]))
    write_csv(output / "source_imports.csv", sorted(import_rows, key=lambda r: (r["importer_module"], int(r["import_line"]), r["imported_module"])))
    write_csv(output / "static_declaration_starters.csv", sorted(decl_rows, key=lambda r: (r["module"], int(r["line"]))))
    write_csv(output / "entry_points.csv", sorted(entry_rows, key=lambda r: r["module"]))
    write_csv(output / "declaration_free_modules.csv", sorted(declaration_free_rows, key=lambda r: r["module"]))
    write_csv(output / "broad_aggregate_imports_in_implementation_modules.csv", sorted(broad_rows, key=lambda r: (r["importer_module"], int(r["import_line"]))))
    write_csv(output / "detected_aggregate_imports_in_implementation_modules.csv", sorted(aggregate_import_rows, key=lambda r: (r["importer_module"], int(r["import_line"]))))
    write_csv(output / "apparent_layer_inversions.csv", sorted(canonical_inversions, key=lambda r: (r["importer_module"], r["imported_module"])))
    write_csv(output / "implementation_layer_inversion_candidates.csv", sorted(implementation_inversions, key=lambda r: (r["importer_module"], r["imported_module"])))
    write_csv(output / "Algorithms_to_Source_implementation_import_inversions.csv", sorted(algorithms_to_source_implementation_inversions, key=lambda r: (r["importer_module"], r["imported_module"])))
    write_csv(output / "import_only_layer_inversion_candidates.csv", sorted(import_only_inversions, key=lambda r: (r["importer_module"], r["imported_module"])))
    write_csv(output / "all_layer_direction_source_imports.csv", sorted(inversion_rows, key=lambda r: (r["importer_module"], r["imported_module"])))
    write_csv(output / "source_to_algorithms_imports.csv", sorted(source_to_algorithms, key=lambda r: (r["importer_module"], r["imported_module"])))
    write_csv(output / "source_module_static_profiles.csv", sorted(source_wrapper_rows, key=lambda r: r["module"]))
    write_csv(output / "canonical_layer_source_import_reachability.csv", sorted(layer_reachability_rows, key=lambda r: r["module"]))
    write_csv(output / "naming_workflow_signals.csv", sorted(naming_rows, key=lambda r: (r["module"], r["signal"])))
    write_csv(output / "proof_hygiene_static_occurrences.csv", sorted(hygiene_rows, key=lambda r: (r["source_path"], int(r["line"]), r["term"])))
    write_csv(output / "source_import_sccs.csv", scc_rows)
    write_csv(output / "layer_source_import_matrix.csv", layer_matrix_rows)
    write_csv(output / "domain_guess_source_import_matrix.csv", domain_matrix_rows)
    write_csv(output / "chapter_guess_source_import_matrix.csv", chapter_matrix_rows)
    write_csv(output / "chapter_hierarchy.csv", chapter_rows)
    write_csv(output / "compatibility_shim_candidates.csv", sorted(compatibility_rows, key=lambda r: r["module"]))
    write_csv(output / "empty_no_import_modules.csv", sorted(empty_module_rows, key=lambda r: r["module"]))
    write_csv(output / "legacy_NumStability_Higham_modules.csv", sorted(legacy_higham_rows, key=lambda r: r["module"]))
    write_csv(output / "canonical_layer_source_label_name_signals.csv", sorted(canonical_layer_source_label_rows, key=lambda r: r["module"]))
    write_csv(output / "modules_not_reachable_from_NumStability_All.csv", all_missing_rows)
    write_csv(output / "module_size_review_candidates.csv", sorted(size_rows, key=lambda r: (-int(r["physical_lines"]), r["module"])))
    write_csv(output / "many_imports_few_declarations.csv", sorted(many_imports_few_declarations_rows, key=lambda r: (-int(r["direct_import_count"]), r["module"])))
    write_csv(output / "root_entry_points.csv", sorted([r for r in entry_rows if r["module"] in ROOT_ENTRY_MODULES], key=lambda r: r["module"]))

    by_layer_modules = Counter(r["physical_layer"] for r in module_rows)
    by_layer_lines = Counter()
    by_layer_blank = Counter()
    by_layer_code = Counter()
    by_layer_comments = Counter()
    by_layer_decls = Counter()
    by_domain_modules = Counter(r["domain_guess"] for r in module_rows)
    for r in module_rows:
        by_layer_lines[r["physical_layer"]] += r["physical_lines"]
        by_layer_blank[r["physical_layer"]] += r["blank_lines"]
        by_layer_code[r["physical_layer"]] += r["code_bearing_lines"]
        by_layer_comments[r["physical_layer"]] += r["comment_only_lines"]
        by_layer_decls[r["physical_layer"]] += r["static_declaration_starter_count"]
    hygiene_counter = Counter((r["term"], r["location_class"]) for r in hygiene_rows)
    workflow_layer_counter = Counter(info[r["module"]]["physical_layer"] for r in naming_rows)
    summary = {
        "schema_version": SCHEMA_VERSION,
        "scope": {
            "root": str(root),
            "included_globs": ["NumStability.lean", "NumStability/**/*.lean"],
            "excluded": "All non-Lean files and Lean files outside the NumStability library root.",
        },
        "metric_definitions": {
            "physical_lines": "Python splitlines(keepends=True) count for each included UTF-8 source file.",
            "code_bearing_lines": "Lines with non-whitespace text after a lexical pass removes comments and string contents.",
            "source_import_edge": "One parsed Lean import command; orientation importer/consumer -> imported candidate dependency.",
            "declaration_free_static": "Zero source lines matching the recorded declaration-introducer regex; not an environment claim.",
            "aggregate_candidate_static": "Declaration-free static module with imports and a root/.All/documented aggregate signal.",
            "layer_inversion": "Source import from a lower-ranked canonical layer to a higher-ranked layer under Examples > Source > Algorithms > Analysis > FloatingPoint.",
            "domain_guess": "Deterministic path-name regex heuristic in the recorded script.",
            "hygiene_location_class": "Lexical code/comment/string state at each matched term occurrence.",
            "many_imports_few_declarations": "direct_import_count >= 20 and static_declaration_starter_count <= 5; a review signal only.",
            "source_module_static_size_bucket": "For declaration-bearing Source modules: small iff code-bearing lines <=100 and declaration starters <=5; substantial iff code-bearing lines >500 or declaration starters >20; otherwise medium. This does not establish proof delegation.",
        },
        "totals": {
            "lean_source_files": len(module_rows),
            "modules": len(module_rows),
            "physical_lines": sum(r["physical_lines"] for r in module_rows),
            "blank_lines": sum(r["blank_lines"] for r in module_rows),
            "code_bearing_lines": sum(r["code_bearing_lines"] for r in module_rows),
            "comment_only_lines": sum(r["comment_only_lines"] for r in module_rows),
            "bytes": sum(r["bytes"] for r in module_rows),
            "source_import_commands": len(import_rows),
            "internal_source_import_edges": sum(r["is_project_module"] == "true" for r in import_rows),
            "external_source_imports": sum(r["is_project_module"] == "false" for r in import_rows),
            "static_declaration_starters": len(decl_rows),
            "declaration_free_static_modules": len(declaration_free_rows),
            "aggregate_candidates_static": sum(r["aggregate_candidate_static"] == "true" for r in module_rows),
            "compatibility_candidates_static": sum(r["compatibility_candidate_static"] == "true" for r in module_rows),
            "empty_no_import_modules_static": len(empty_module_rows),
            "implementation_modules_with_broad_aggregate_import": len(set(r["importer_module"] for r in broad_rows)),
            "broad_aggregate_import_edges": len(broad_rows),
            "apparent_reverse_layer_source_import_edges_all": len(inversion_rows),
            "apparent_reverse_layer_source_import_edges_canonical_implementation_layers": len(canonical_inversions),
            "apparent_reverse_layer_edges_from_declaration_bearing_modules": len(implementation_inversions),
            "declaration_bearing_modules_with_apparent_reverse_layer_import": len(set(r["importer_module"] for r in implementation_inversions)),
            "apparent_reverse_layer_edges_from_import_only_modules": len(import_only_inversions),
            "import_only_modules_with_apparent_reverse_layer_import": len(set(r["importer_module"] for r in import_only_inversions)),
            "source_to_algorithms_direct_import_edges": len(source_to_algorithms),
            "declaration_bearing_source_to_algorithms_direct_import_edges": sum(r["importer_has_static_declarations"] == "true" for r in source_to_algorithms),
            "declaration_bearing_source_modules_importing_algorithms_directly": len(set(r["importer_module"] for r in source_to_algorithms if r["importer_has_static_declarations"] == "true")),
            "source_import_cyclic_scc_count": sum(1 for c in sccs if len(c) > 1 or (len(c) == 1 and c[0] in adjacency.get(c[0], []))),
            "workflow_name_signal_modules": len(set(r["module"] for r in naming_rows)),
            "legacy_NumStability_Higham_modules": len(legacy_higham_rows),
            "legacy_NumStability_Higham_declaration_free_static_modules": sum(r["declaration_free_static"] == "true" for r in module_rows if r["module"] == "NumStability.Higham" or r["module"].startswith("NumStability.Higham.")),
            "module_size_review_candidates_gt_10000_physical_or_code_lines": len(size_rows),
            "modules_gt_25000_physical_lines": sum(r["physical_lines"] > 25000 for r in module_rows),
            "implementation_imports_of_detected_aggregates": len(aggregate_import_rows),
            "implementation_imports_of_detected_aggregates_width_ge_50_modules": sum(r["static_width_bucket"] == "broad_ge_50" for r in aggregate_import_rows),
            "declaration_bearing_modules_static": len(declaration_bearing_modules),
            "NumStability_All_reachable_modules_including_entry": len(all_reachable_including_self),
            "NumStability_All_unreachable_modules": len(all_missing_rows),
            "NumStability_All_unreachable_declaration_bearing_modules_static": sum(r["declaration_free_static"] == "false" for r in all_missing_rows),
            "NumStability_All_reachable_static_declaration_starters": sum(info[x]["static_declaration_starter_count"] for x in all_reachable_including_self),
            "canonical_layer_source_label_path_signals": len(canonical_layer_source_label_rows),
            "canonical_layer_source_label_path_signals_declaration_bearing": sum(r["declaration_free_static"] == "false" for r in canonical_layer_source_label_rows),
            "Algorithms_to_Source_implementation_import_inversion_edges": len(algorithms_to_source_implementation_inversions),
            "Algorithms_modules_with_Source_implementation_import_inversion": len(set(r["importer_module"] for r in algorithms_to_source_implementation_inversions)),
            "many_imports_few_declarations_review_candidates": len(many_imports_few_declarations_rows),
            "declaration_bearing_Source_modules": len(source_wrapper_rows),
            "declaration_bearing_Source_modules_with_direct_lower_layer_import": sum(int(r["direct_lower_layer_import_count"]) > 0 for r in source_wrapper_rows),
            "declaration_bearing_Source_modules_with_transitive_lower_layer_import_reach": sum(r["shortest_import_path_to_lower_layer"] != "" for r in source_wrapper_rows),
            "declaration_bearing_Source_modules_without_lower_layer_import_reach": sum(r["shortest_import_path_to_lower_layer"] == "" for r in source_wrapper_rows),
            "modules_gt_10000_code_bearing_lines": sum(r["code_bearing_lines"] > 10000 for r in module_rows),
            "modules_gt_25000_code_bearing_lines": sum(r["code_bearing_lines"] > 25000 for r in module_rows),
        },
        "by_physical_layer": {
            k: {"modules": by_layer_modules[k], "physical_lines": by_layer_lines[k], "blank_lines": by_layer_blank[k], "code_bearing_lines": by_layer_code[k], "comment_only_lines": by_layer_comments[k], "static_declaration_starters": by_layer_decls[k]}
            for k in sorted(by_layer_modules)
        },
        "by_domain_guess_modules": dict(sorted(by_domain_modules.items())),
        "static_declaration_starters_by_kind": {
            kind.removesuffix("_count"): sum(r[kind] for r in module_rows)
            for kind in ("theorem_count", "lemma_count", "def_count", "abbrev_count", "opaque_count", "axiom_count", "constant_count", "structure_count", "class_count", "inductive_count", "instance_count", "example_count")
        },
        "module_distributions_nearest_rank_percentiles": {
            "physical_lines": nearest_rank_percentiles([r["physical_lines"] for r in module_rows]),
            "code_bearing_lines": nearest_rank_percentiles([r["code_bearing_lines"] for r in module_rows]),
            "static_declaration_starter_count": nearest_rank_percentiles([r["static_declaration_starter_count"] for r in module_rows]),
            "direct_internal_import_count": nearest_rank_percentiles([r["direct_internal_import_count"] for r in module_rows]),
        },
        "proof_hygiene_static_counts": {f"{term}:{loc}": n for (term, loc), n in sorted(hygiene_counter.items())},
        "workflow_signal_rows_by_physical_layer": dict(sorted(workflow_layer_counter.items())),
        "root_entry_modules": sorted(ROOT_ENTRY_MODULES),
        "limitations": [
            "Source imports are not elaborated logical declaration dependencies.",
            "Static declaration-introducer matches neither enumerate generated declarations nor prove explicit authorship.",
            "Path-derived layers, chapters, and domains are deterministic classifications, not semantic proof.",
            "No-import logical edges and elaboration-only import requirements cannot be resolved by this analyzer.",
            "A declaration-free static result must be checked against the compiled environment before claiming a true environment-declaration-free shim.",
        ],
    }
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    validation = validate_lexer()
    summary = analyze(root, output)
    (output / "validation.json").write_text(json.dumps({"schema_version": SCHEMA_VERSION, **validation}, indent=2) + "\n", encoding="utf-8")
    (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary["totals"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
