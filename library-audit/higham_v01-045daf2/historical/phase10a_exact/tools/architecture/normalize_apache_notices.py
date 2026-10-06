#!/usr/bin/env python3
"""Normalize existing Apache-2.0 pointers without changing copyright owners."""

from __future__ import annotations

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOT = ROOT / "NumStability"
APACHE_MARKER = "Released under Apache 2.0"
BROKEN_POINTER = (
    "Released under Apache 2.0 license as described in the file LICENSE."
)
FIXED_POINTER = (
    "Released under Apache 2.0 license as described in "
    "LICENSES/Apache-2.0.txt."
)
SPDX = "SPDX-License-Identifier: Apache-2.0"
LICENSE_REFERENCE = "See LICENSES/Apache-2.0.txt."


def normalize_text(text: str) -> str:
    """Return a notice-normalized file while preserving all attribution text."""

    if APACHE_MARKER not in text or SPDX in text:
        return text

    text = text.replace(BROKEN_POINTER, FIXED_POINTER)
    lines = text.splitlines(keepends=True)
    for index, line in enumerate(lines):
        if APACHE_MARKER not in line:
            continue
        ending = "\r\n" if line.endswith("\r\n") else "\n"
        lines[index + 1:index + 1] = [
            SPDX + ending,
            LICENSE_REFERENCE + ending,
        ]
        return "".join(lines)
    return text


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Report or normalize legacy Apache-2.0 pointers in production Lean "
            "files. Copyright and author lines are never rewritten."
        )
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the reviewed mechanical normalization",
    )
    args = parser.parse_args()

    changed: list[Path] = []
    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        original = path.read_text(encoding="utf-8")
        normalized = normalize_text(original)
        if normalized == original:
            continue
        changed.append(path)
        if args.write:
            path.write_text(normalized, encoding="utf-8", newline="")

    action = "normalized" if args.write else "would normalize"
    print(f"{action} {len(changed)} Apache-notice files")
    for path in changed:
        print(path.relative_to(ROOT).as_posix())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
