#!/usr/bin/env python3
"""Check repository license pointers and evidenced upstream attribution."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOT = ROOT / "NumStability"
APACHE_MARKER = "Released under Apache 2.0"
SPDX = "SPDX-License-Identifier: Apache-2.0"
BROKEN_POINTER = "described in the file LICENSE"
LICENSE_REFERENCE = "LICENSES/Apache-2.0.txt"

UPSTREAM_EVIDENCE: dict[str, tuple[str, ...]] = {
    "NumStability/Upstream/Lindemann/AlgebraicPart.lean": (
        "https://github.com/leanprover-community/mathlib4/pull/28013",
        "5abb7c68488b527e4d7ecf5d7bbe085db8d2a388",
    ),
    "NumStability/Upstream/Lindemann/Basic.lean": (
        "https://github.com/leanprover-community/mathlib4/pull/28013",
        "5abb7c68488b527e4d7ecf5d7bbe085db8d2a388",
    ),
    "NumStability/Upstream/Lindemann/FinsuppQuotient.lean": (
        "https://github.com/leanprover-community/mathlib4/pull/28013",
        "5abb7c68488b527e4d7ecf5d7bbe085db8d2a388",
    ),
    "NumStability/Upstream/Lindemann/SymmetricEval.lean": (
        "https://github.com/leanprover-community/mathlib4/pull/28013",
        "5abb7c68488b527e4d7ecf5d7bbe085db8d2a388",
    ),
    "NumStability/Upstream/Lindemann/MonoidAlgebraCompat.lean": (
        "https://github.com/leanprover-community/mathlib4/pull/36762",
        "cbdf82d6b083de3a961936dbea002185060b46c3",
        "https://github.com/leanprover-community/mathlib4/pull/37797",
        "d8255d64167683fc82500473c77d08285b6804ed",
        "5abb7c68488b527e4d7ecf5d7bbe085db8d2a388",
    ),
}


def main() -> int:
    errors: list[str] = []
    apache_files: list[Path] = []

    license_path = ROOT / LICENSE_REFERENCE
    if not license_path.is_file():
        errors.append(f"missing Apache license text: {LICENSE_REFERENCE}")
    else:
        license_text = license_path.read_text(encoding="utf-8")
        required_sections = (
            "Apache License",
            "Version 2.0, January 2004",
            "TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION",
            "END OF TERMS AND CONDITIONS",
        )
        for section in required_sections:
            if section not in license_text:
                errors.append(f"Apache license text is missing: {section}")

    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if APACHE_MARKER not in text:
            continue
        apache_files.append(path)
        relative = path.relative_to(ROOT).as_posix()
        if SPDX not in text:
            errors.append(f"Apache file lacks SPDX identifier: {relative}")
        if BROKEN_POINTER in text:
            errors.append(f"Apache file points at the MIT root license: {relative}")
        if LICENSE_REFERENCE not in text:
            errors.append(f"Apache file lacks the canonical license path: {relative}")

    notice_path = ROOT / "THIRD_PARTY_NOTICES.md"
    if not notice_path.is_file():
        errors.append("missing THIRD_PARTY_NOTICES.md")
        notice_text = ""
    else:
        notice_text = notice_path.read_text(encoding="utf-8")

    for relative, tokens in UPSTREAM_EVIDENCE.items():
        path = ROOT / relative
        if not path.is_file():
            errors.append(f"missing evidenced upstream file: {relative}")
            continue
        text = path.read_text(encoding="utf-8")
        if relative not in notice_text:
            errors.append(f"upstream file absent from THIRD_PARTY_NOTICES: {relative}")
        for token in tokens:
            if token not in text and token not in notice_text:
                errors.append(f"missing upstream evidence {token}: {relative}")

    if errors:
        for error in errors:
            print(f"error: {error}")
        print(f"provenance contract failed with {len(errors)} error(s)")
        return 1

    print(
        "provenance contract passed: "
        f"{len(apache_files)} Apache-marked production files and "
        f"{len(UPSTREAM_EVIDENCE)} evidenced upstream modules"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
