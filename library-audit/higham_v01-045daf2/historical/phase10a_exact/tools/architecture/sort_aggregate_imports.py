#!/usr/bin/env python3
"""Sort and deduplicate the import block of an import-only Lean aggregate."""

from __future__ import annotations

import argparse
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, help="Lean aggregate to inspect")
    parser.add_argument(
        "--write",
        action="store_true",
        help="rewrite the file; the default is a read-only check",
    )
    return parser.parse_args()


def sorted_aggregate(text: str) -> str:
    lines = text.splitlines()
    try:
        first = next(i for i, line in enumerate(lines) if line.startswith("import "))
    except StopIteration:
        raise ValueError("no Lean imports found")

    # Lean imports form the initial contiguous command block.  Stop at its first
    # nonblank, non-import line so prose such as "import the narrow leaf" in a
    # later module docstring is never mistaken for another import command.
    import_indexes: list[int] = []
    for i in range(first, len(lines)):
        line = lines[i]
        if line.startswith("import "):
            import_indexes.append(i)
        elif line:
            break

    last = import_indexes[-1]

    imports = sorted({lines[i] for i in import_indexes}, key=str.casefold)
    result = lines[:first] + imports + lines[last + 1 :]
    return "\n".join(result) + "\n"


def main() -> int:
    args = parse_args()
    original = args.path.read_text(encoding="utf-8-sig")
    normalized = sorted_aggregate(original)
    if normalized == original:
        print(f"aggregate imports already sorted: {args.path}")
        return 0
    if not args.write:
        print(f"aggregate imports need sorting: {args.path}")
        return 1
    args.path.write_text(normalized, encoding="utf-8", newline="\n")
    print(f"sorted aggregate imports: {args.path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
