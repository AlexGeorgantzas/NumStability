#!/usr/bin/env python3
"""Verify the documented old-to-new Lean module forwarding contract."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from generate_baseline import IMPORT_RE, module_name, remove_lean_comments, source_paths


ROOT = Path(__file__).resolve().parents[2]
POLICY = ROOT / "docs" / "architecture" / "COMPATIBILITY.md"
IMPORT_LINE_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import[ \t]+[^\r\n]+(?:\r?\n|$)"
)


def module_path(name: str) -> Path:
    return ROOT / Path(*name.split(".")).with_suffix(".lean")


def documented_mappings() -> dict[str, tuple[str, ...]]:
    mappings: dict[str, tuple[str, ...]] = {}
    for line in POLICY.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|"):
            continue
        names = re.findall(r"`(NumStability(?:\.[A-Za-z0-9_']+)+)`", line)
        if len(names) < 2:
            continue
        historical, *canonical = names
        if historical in mappings:
            raise ValueError(f"duplicate compatibility row: {historical}")
        mappings[historical] = tuple(canonical)
    if not mappings:
        raise ValueError(f"no compatibility mappings found in {POLICY}")
    return mappings


def main() -> int:
    try:
        mappings = documented_mappings()
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    failures: list[str] = []
    tier_manifest_path = ROOT / "docs" / "architecture" / "tiers.json"
    try:
        tier_manifest = json.loads(tier_manifest_path.read_text(encoding="utf-8"))
        tier_compatibility = {
            name
            for name, tier in tier_manifest.get("exact", {}).items()
            if tier == "compatibility"
        }
        if tier_compatibility != set(mappings):
            missing = sorted(tier_compatibility - set(mappings))
            extra = sorted(set(mappings) - tier_compatibility)
            if missing:
                failures.append(
                    "compatibility-tier modules absent from table: " + ", ".join(missing)
                )
            if extra:
                failures.append(
                    "tabled historical modules not in compatibility tier: "
                    + ", ".join(extra)
                )
    except (OSError, json.JSONDecodeError, AttributeError) as error:
        failures.append(f"cannot read tier manifest {tier_manifest_path}: {error}")

    for historical, canonical in sorted(mappings.items()):
        old_path = module_path(historical)
        if not old_path.is_file():
            failures.append(f"missing historical module: {historical}")
            continue
        for target in canonical:
            if not module_path(target).is_file():
                failures.append(f"missing canonical module: {target}")

        text = old_path.read_text(encoding="utf-8-sig", errors="replace")
        uncommented = remove_lean_comments(text)
        imports = tuple(IMPORT_RE.findall(uncommented))
        if imports != canonical:
            failures.append(
                f"{historical}: imports {imports!r}, documented {canonical!r}"
            )
        remaining = IMPORT_LINE_RE.sub("", uncommented).strip()
        if remaining:
            failures.append(f"{historical}: forwarding module contains Lean code")

    historical_names = set(mappings)
    for path in source_paths(ROOT):
        name = module_name(path.relative_to(ROOT))
        if name in historical_names:
            continue
        text = path.read_text(encoding="utf-8-sig", errors="replace")
        for target in IMPORT_RE.findall(remove_lean_comments(text)):
            if target in historical_names:
                failures.append(f"{name}: production import uses historical path {target}")

    test_imports: set[str] = set()
    test_paths = [ROOT / "NumStabilityTest.lean"]
    test_paths.extend(sorted((ROOT / "NumStabilityTest").rglob("*.lean")))
    for path in test_paths:
        text = path.read_text(encoding="utf-8-sig", errors="replace")
        test_imports.update(IMPORT_RE.findall(remove_lean_comments(text)))
    canonical_names = {target for targets in mappings.values() for target in targets}
    missing_historical_tests = sorted(historical_names - test_imports)
    missing_canonical_tests = sorted(canonical_names - test_imports)
    if missing_historical_tests:
        failures.append(
            "historical paths without a direct test import: "
            + ", ".join(missing_historical_tests)
        )
    if missing_canonical_tests:
        failures.append(
            "canonical targets without a direct test import: "
            + ", ".join(missing_canonical_tests)
        )

    if failures:
        for failure in failures:
            print(f"error: {failure}", file=sys.stderr)
        return 1
    target_count = sum(len(targets) for targets in mappings.values())
    print(
        f"compatibility contract passed: {len(mappings)} forwarding modules, "
        f"{target_count} canonical targets"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
