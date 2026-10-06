#!/usr/bin/env python3
"""Enforce the NumStability layout contract with an explicit legacy ratchet."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter, deque
from pathlib import Path
from typing import Any, Iterable

from generate_baseline import IMPORT_RE, SourceModule, remove_lean_comments, scan_sources


ROOT = Path(__file__).resolve().parents[2]
BASELINE = ROOT / "docs" / "architecture" / "layout-exceptions.json"
TIERS = ROOT / "docs" / "architecture" / "tiers.json"

DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe|scoped|local)\s+)*"
    r"(?:def|theorem|lemma|abbrev|opaque|axiom|inductive|structure|class|instance)\b"
)
STRUCTURAL_LINE_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+[A-Za-z0-9_'.]+\s*$|"
    r"^\s*module\s*$",
    re.MULTILINE,
)
UPPER_CAMEL_RE = re.compile(r"^[A-Z][A-Za-z0-9']*$")
SOURCE_LOCATOR_RE = re.compile(
    r"^(?:Ch\d|Chapter\d|Higham(?:Chapter)?\d|Problem\d|Theorem\d|Thm\d|"
    r"Lemma\d|Equation\d|Eq\d|Corollary\d|Cor\d|Algorithm\d|Alg\d|Table\d)"
)
ABBREVIATED_LOCATOR_RE = re.compile(r"^(?:Ch|Thm|Eq|Cor|Alg)\d")
FULL_LOCATOR_RE = re.compile(
    r"^(?:Theorem|Lemma|Equation|Corollary|Problem|Algorithm|Example|Table)(\d+)(.*)$"
)
PLACEHOLDER_RE = re.compile(
    r"\b(?:sorry|admit)\b|^\s*(?:axiom|constant)\b",
    re.MULTILINE,
)
PROCESS_WORDS = (
    "Actual",
    "Bridge",
    "Closure",
    "Endpoint",
    "Operational",
    "Prose",
    "Remaining",
    "Source",
    "Support",
    "Whole",
)
GENERATED_PARTS = {"__pycache__", ".DS_Store"}
GENERATED_SUFFIXES = {".olean", ".ilean", ".pyc", ".pyo", ".aux", ".log", ".out"}
FORBIDDEN_TRACKED_PREFIXES = (
    ".agents/",
    ".codex/",
    ".lake/",
    ".venv/",
    "References/",
    "benchmark/",
    "benchmark-results/",
    "chapter_splitting/",
    "docs/chapter13/",
    "references/",
    "scratch/",
    "thesis/",
    "tmp/",
)
LEGACY_KEYS = (
    "unclassified_modules",
    "mixed_modules",
    "missing_module_docstrings",
    "noncanonical_modules",
    "declaration_bearing_umbrellas",
    "unsorted_aggregate_imports",
)


class LayoutError(RuntimeError):
    pass


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise LayoutError(f"cannot read {path.relative_to(ROOT)}: {error}") from error
    if not isinstance(value, dict):
        raise LayoutError(f"expected a JSON object in {path.relative_to(ROOT)}")
    return value


def tier_assignments(modules: Iterable[SourceModule]) -> tuple[dict[str, str], set[str]]:
    manifest = load_json(TIERS)
    if manifest.get("schema_version") != 1:
        raise LayoutError("unsupported tier manifest schema")
    exact = manifest.get("exact")
    prefixes = manifest.get("prefixes")
    tiers = manifest.get("tiers")
    if not isinstance(exact, dict) or not isinstance(prefixes, list) or not isinstance(tiers, list):
        raise LayoutError("invalid tier manifest structure")
    allowed = set(tiers)
    parsed_prefixes: list[tuple[str, str]] = []
    for rule in prefixes:
        if not isinstance(rule, dict):
            raise LayoutError("invalid tier prefix rule")
        prefix, tier = rule.get("prefix"), rule.get("tier")
        if not isinstance(prefix, str) or tier not in allowed:
            raise LayoutError(f"invalid tier prefix rule: {rule!r}")
        parsed_prefixes.append((prefix, tier))
    parsed_prefixes.sort(key=lambda item: (-len(item[0]), item[0]))

    by_name = {module.name for module in modules}
    missing_exact = sorted(set(exact) - by_name)
    if missing_exact:
        raise LayoutError("tier entries without files: " + ", ".join(missing_exact))

    assignment: dict[str, str] = {}
    for name in sorted(by_name):
        if name in exact:
            tier = exact[name]
            if tier not in allowed:
                raise LayoutError(f"unknown tier {tier!r} for {name}")
            assignment[name] = tier
            continue
        for prefix, tier in parsed_prefixes:
            if name == prefix or name.startswith(prefix + "."):
                assignment[name] = tier
                break
    return assignment, by_name - set(assignment)


def has_declaration(module: SourceModule) -> bool:
    text = (ROOT / module.path).read_text(encoding="utf-8-sig", errors="replace")
    return bool(DECL_RE.search(remove_lean_comments(text)))


def is_structural_only(module: SourceModule) -> bool:
    text = (ROOT / module.path).read_text(encoding="utf-8-sig", errors="replace")
    uncommented = remove_lean_comments(text)
    return not STRUCTURAL_LINE_RE.sub("", uncommented).strip()


def noncanonical_name(module: SourceModule, tier: str | None) -> bool:
    if tier == "compatibility":
        return False
    parts = module.name.split(".")[1:]
    if any(not UPPER_CAMEL_RE.fullmatch(part) for part in parts):
        return True
    if module.name == "NumStability.Source" or module.name.startswith("NumStability.Source."):
        if any("_" in part for part in parts):
            return True
        if module.name == "NumStability.Source":
            return False
        if len(parts) >= 2 and parts[:2] == ["Source", "Higham"]:
            if len(parts) == 2:
                return False
            locator = parts[2]
            if locator != "CrossChapter" and not re.fullmatch(r"Chapter\d{2}", locator):
                return True
            leaves = parts[3:]
            if locator == "CrossChapter":
                return any(
                    ABBREVIATED_LOCATOR_RE.match(leaf) or leaf.startswith("Higham")
                    for leaf in leaves
                )
            chapter_number = locator.removeprefix("Chapter")
            for leaf in leaves:
                if (
                    ABBREVIATED_LOCATOR_RE.match(leaf)
                    or leaf.startswith("Higham")
                    or leaf.startswith("Chapter")
                ):
                    return True
                match = FULL_LOCATOR_RE.match(leaf)
                if match and len(match.group(1)) != 2:
                    return True
            return False
        chapter_parts = [part for part in parts if part.startswith("Chapter")]
        if any(not re.fullmatch(r"Chapter\d{2}", part) for part in chapter_parts):
            return True
        return False
    return (
        any("_" in part for part in parts)
        or any(SOURCE_LOCATOR_RE.match(part) for part in parts)
        or any(word in part for part in parts for word in PROCESS_WORDS)
    )


def tracked_generated() -> list[str]:
    try:
        completed = subprocess.run(
            ["git", "ls-files", "-z"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except (FileNotFoundError, subprocess.CalledProcessError) as error:
        raise LayoutError(f"cannot inspect tracked files: {error}") from error
    paths = [Path(raw.decode("utf-8", errors="replace")) for raw in completed.stdout.split(b"\0") if raw]
    return sorted(
        path.as_posix()
        for path in paths
        if path.as_posix().startswith(FORBIDDEN_TRACKED_PREFIXES)
        or any(part in GENERATED_PARTS for part in path.parts)
        or path.suffix.lower() in GENERATED_SUFFIXES
    )


def reachable(start: str, by_name: dict[str, SourceModule]) -> set[str]:
    seen: set[str] = set()
    queue: deque[str] = deque([start])
    while queue:
        current = queue.popleft()
        if current in seen:
            continue
        seen.add(current)
        module = by_name.get(current)
        if module is not None:
            queue.extend(target for target in module.imports if target in by_name)
    return seen


def test_reachability_failures() -> list[str]:
    paths = [ROOT / "NumStabilityTest.lean"]
    paths.extend(sorted((ROOT / "NumStabilityTest").rglob("*.lean")))
    adjacency: dict[str, set[str]] = {}
    for path in paths:
        relative = path.relative_to(ROOT)
        name = ".".join(relative.with_suffix("").parts)
        text = path.read_text(encoding="utf-8-sig", errors="replace")
        adjacency[name] = set(IMPORT_RE.findall(remove_lean_comments(text)))
    seen: set[str] = set()
    queue: deque[str] = deque(["NumStabilityTest"])
    while queue:
        current = queue.popleft()
        if current in seen:
            continue
        seen.add(current)
        queue.extend(target for target in adjacency.get(current, set()) if target in adjacency)
    missing = sorted(set(adjacency) - seen)
    return [
        f"NumStabilityTest does not reach {len(missing)} test module(s): "
        + ", ".join(missing)
    ] if missing else []


def placeholder_failures(modules: list[SourceModule]) -> list[str]:
    paths = [ROOT / module.path for module in modules]
    paths.append(ROOT / "NumStabilityTest.lean")
    paths.extend(sorted((ROOT / "NumStabilityTest").rglob("*.lean")))
    findings: list[str] = []
    for path in paths:
        text = path.read_text(encoding="utf-8-sig", errors="replace")
        if PLACEHOLDER_RE.search(remove_lean_comments(text)):
            findings.append(path.relative_to(ROOT).as_posix())
    return ["proof placeholders or axiom/constant commands: " + ", ".join(findings)] if findings else []


def current_debt(
    modules: list[SourceModule], assignment: dict[str, str], unclassified: set[str]
) -> tuple[dict[str, list[str]], list[str]]:
    debt: dict[str, list[str]] = {
        "unclassified_modules": sorted(unclassified),
        "mixed_modules": sorted(name for name, tier in assignment.items() if tier == "mixed"),
        "missing_module_docstrings": sorted(
            module.name for module in modules if not module.has_module_docstring
        ),
        "noncanonical_modules": sorted(
            module.name
            for module in modules
            if noncanonical_name(module, assignment.get(module.name))
        ),
        "declaration_bearing_umbrellas": sorted(
            module.name
            for module in modules
            if (ROOT / module.path).with_suffix("").is_dir() and not is_structural_only(module)
        ),
        "unsorted_aggregate_imports": sorted(
            module.name
            for module in modules
            if assignment.get(module.name) == "aggregate"
            and list(module.imports) != sorted(set(module.imports), key=str.casefold)
        ),
    }
    duplicate_imports = sorted(
        module.name
        for module in modules
        if any(count > 1 for count in Counter(module.imports).values())
    )
    return debt, duplicate_imports


def render_summary(debt: dict[str, list[str]], modules: list[SourceModule]) -> str:
    labels = {
        "unclassified_modules": "unclassified modules",
        "mixed_modules": "mixed modules",
        "missing_module_docstrings": "modules missing module docs",
        "noncanonical_modules": "legacy naming exceptions",
        "declaration_bearing_umbrellas": "declaration-bearing umbrellas",
        "unsorted_aggregate_imports": "unsorted aggregate imports",
    }
    lines = [f"Lean modules: {len(modules)}"]
    lines.extend(f"{labels[key]}: {len(debt[key])}" for key in LEGACY_KEYS)
    return "\n".join(lines)


def write_baseline(
    path: Path,
    debt: dict[str, list[str]],
    complete_aggregates: dict[str, str],
    direct_import_ceilings: dict[str, Any],
) -> None:
    data = {
        "schema_version": 1,
        "policy": (
            "Exact legacy debt allowed during migration. Update this reviewed baseline whenever "
            "debt is removed; new modules must comply and be classified."
        ),
        "direct_import_ceilings": direct_import_ceilings,
        "complete_aggregates": dict(sorted(complete_aggregates.items())),
        "legacy": {key: debt[key] for key in LEGACY_KEYS},
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def check() -> int:
    _, modules = scan_sources(ROOT)
    by_name = {module.name: module for module in modules}
    assignment, unclassified = tier_assignments(modules)
    debt, duplicate_imports = current_debt(modules, assignment, unclassified)
    print(render_summary(debt, modules))

    baseline = load_json(BASELINE)
    if baseline.get("schema_version") != 1:
        raise LayoutError("unsupported layout exception schema")
    legacy = baseline.get("legacy")
    aggregate_contracts = baseline.get("complete_aggregates")
    if not isinstance(legacy, dict) or not isinstance(aggregate_contracts, dict):
        raise LayoutError("invalid layout exception structure")

    failures: list[str] = []
    if duplicate_imports:
        failures.append("duplicate imports: " + ", ".join(duplicate_imports))
    generated = tracked_generated()
    if generated:
        failures.append("tracked generated artifacts: " + ", ".join(generated))
    failures.extend(test_reachability_failures())
    failures.extend(placeholder_failures(modules))

    for key in LEGACY_KEYS:
        allowed = legacy.get(key)
        if not isinstance(allowed, list) or not all(isinstance(name, str) for name in allowed):
            raise LayoutError(f"layout exception `{key}` must be a list of module names")
        additions = sorted(set(debt[key]) - set(allowed))
        if additions:
            failures.append(f"new {key.replace('_', ' ')}: " + ", ".join(additions))
        resolved = sorted(set(allowed) - set(debt[key]))
        if resolved:
            failures.append(
                f"stale {key.replace('_', ' ')} baseline; review the improvement and run "
                f"--write-baseline: " + ", ".join(resolved)
            )

    for module in modules:
        tier = assignment.get(module.name)
        if tier in {"aggregate", "compatibility"} and not is_structural_only(module):
            failures.append(f"{tier} module is not import-and-docstring-only: {module.name}")

    structural = {
        name for name, tier in assignment.items() if tier in {"aggregate", "compatibility"}
    }
    for aggregate, prefix in sorted(aggregate_contracts.items()):
        if aggregate not in by_name:
            failures.append(f"complete aggregate is missing: {aggregate}")
            continue
        if not isinstance(prefix, str):
            raise LayoutError(f"aggregate prefix for {aggregate} must be a string")
        expected = {
            name
            for name in by_name
            if name.startswith(prefix) and name not in structural
        }
        missing = sorted(expected - reachable(aggregate, by_name))
        if missing:
            failures.append(
                f"{aggregate} misses {len(missing)} canonical descendant(s): "
                + ", ".join(missing)
            )

    import_ceilings = baseline.get("direct_import_ceilings", {})
    if not isinstance(import_ceilings, dict):
        raise LayoutError("layout exception `direct_import_ceilings` must be an object")
    for source, targets in sorted(import_ceilings.items()):
        if source not in by_name or not isinstance(targets, dict):
            raise LayoutError(f"invalid direct import ceiling source: {source}")
        for prefix, ceiling in sorted(targets.items()):
            if not isinstance(prefix, str) or not isinstance(ceiling, int):
                raise LayoutError(f"invalid direct import ceiling for {source}: {prefix}")
            count = sum(target.startswith(prefix) for target in by_name[source].imports)
            if count > ceiling:
                failures.append(
                    f"{source} has {count} direct imports below {prefix}; ceiling is {ceiling}"
                )

    if failures:
        for failure in failures:
            print(f"error: {failure}", file=sys.stderr)
        return 1
    print("Layout contract satisfied; no legacy debt increased.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-baseline",
        action="store_true",
        help="review-only operation: replace the exact legacy debt baseline",
    )
    args = parser.parse_args()
    try:
        if not args.write_baseline:
            return check()
        _, modules = scan_sources(ROOT)
        assignment, unclassified = tier_assignments(modules)
        debt, duplicate_imports = current_debt(modules, assignment, unclassified)
        if duplicate_imports:
            raise LayoutError(
                "refusing to baseline duplicate imports: " + ", ".join(duplicate_imports)
            )
        if tracked_generated():
            raise LayoutError("refusing to baseline tracked generated artifacts")
        complete_aggregates: dict[str, str] = {}
        direct_import_ceilings: dict[str, Any] = {
            "NumStability.Algorithms": {"NumStability.Analysis.": 45}
        }
        if BASELINE.is_file():
            existing = load_json(BASELINE)
            existing_aggregates = existing.get("complete_aggregates", {})
            existing_ceilings = existing.get("direct_import_ceilings", {})
            if isinstance(existing_aggregates, dict):
                complete_aggregates = existing_aggregates
            if isinstance(existing_ceilings, dict):
                direct_import_ceilings = existing_ceilings
        write_baseline(BASELINE, debt, complete_aggregates, direct_import_ceilings)
        print(render_summary(debt, modules))
        print(f"Wrote {BASELINE.relative_to(ROOT)}")
        return 0
    except LayoutError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
