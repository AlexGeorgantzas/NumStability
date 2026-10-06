#!/usr/bin/env python3
"""Write or verify the deterministic checksum inventory for this audit.

The manifest deliberately excludes the isolated Git worktree, generated Lean
object files used only while exercising client probes, Python bytecode caches,
and the manifest itself.  It hashes every other regular, non-symlink file below
the audit root in bytewise relative-path order.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import sys
from pathlib import Path


AUDIT_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = AUDIT_ROOT / "ARTIFACT_SHA256SUMS"
TEMP_MANIFEST = AUDIT_ROOT / ".ARTIFACT_SHA256SUMS.tmp"

EXCLUDED_PREFIXES = (
    Path("_worktree"),
    Path("probes/build"),
    Path("timings/fresh_outputs"),
)
EXCLUDED_NAMES = {
    "ARTIFACT_SHA256SUMS",
    ".ARTIFACT_SHA256SUMS.tmp",
    ".DS_Store",
}


def validate_root() -> None:
    if not re.fullmatch(r"higham_v01-[0-9a-f]{7,40}", AUDIT_ROOT.name):
        raise SystemExit(f"refusing unexpected audit root: {AUDIT_ROOT}")
    if not (AUDIT_ROOT / "provenance").is_dir():
        raise SystemExit(f"missing provenance directory: {AUDIT_ROOT}")


def excluded(relative: Path) -> bool:
    if relative.name in EXCLUDED_NAMES or "__pycache__" in relative.parts:
        return True
    if relative.suffix == ".pyc":
        return True
    if (
        relative.suffix in {".olean", ".ilean"}
        and Path("probes/validation_output") in relative.parents
    ):
        return True
    return any(
        relative == prefix or prefix in relative.parents
        for prefix in EXCLUDED_PREFIXES
    )


def eligible_files() -> list[Path]:
    result: list[Path] = []
    for directory, directory_names, file_names in os.walk(
        AUDIT_ROOT, topdown=True, followlinks=False
    ):
        directory_path = Path(directory)
        retained_directories: list[str] = []
        for name in directory_names:
            path = directory_path / name
            relative = path.relative_to(AUDIT_ROOT)
            if excluded(relative):
                continue
            if path.is_symlink():
                raise SystemExit(
                    f"unexpected symlink outside excluded trees: {relative}"
                )
            retained_directories.append(name)
        directory_names[:] = retained_directories
        for name in file_names:
            path = directory_path / name
            relative = path.relative_to(AUDIT_ROOT)
            if excluded(relative):
                continue
            # Do not checksum symlinks. An unexpected artifact symlink must be
            # reported instead of silently hashing its target.
            if path.is_symlink():
                raise SystemExit(
                    f"unexpected symlink outside excluded trees: {relative}"
                )
            if path.is_file():
                result.append(path)
    return sorted(result, key=lambda path: os.fsencode(path.relative_to(AUDIT_ROOT)))


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            value.update(block)
    return value.hexdigest()


def current_rows() -> list[tuple[str, str]]:
    return [
        (digest(path), path.relative_to(AUDIT_ROOT).as_posix())
        for path in eligible_files()
    ]


def write_manifest() -> int:
    rows = current_rows()
    data = "".join(f"{value}  {relative}\n" for value, relative in rows)
    TEMP_MANIFEST.write_text(data, encoding="utf-8", newline="\n")
    os.replace(TEMP_MANIFEST, MANIFEST)
    print(f"wrote {MANIFEST} ({len(rows)} files)")
    return 0


def parse_manifest() -> list[tuple[str, str]]:
    if not MANIFEST.is_file():
        raise SystemExit(f"missing checksum manifest: {MANIFEST}")
    result: list[tuple[str, str]] = []
    for line_number, line in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), 1):
        try:
            value, relative = line.split("  ", 1)
        except ValueError as exc:
            raise SystemExit(f"malformed manifest line {line_number}") from exc
        if not re.fullmatch(r"[0-9a-f]{64}", value):
            raise SystemExit(f"invalid SHA-256 on manifest line {line_number}")
        if Path(relative).is_absolute() or ".." in Path(relative).parts:
            raise SystemExit(f"unsafe path on manifest line {line_number}: {relative}")
        result.append((value, relative))
    return result


def verify_manifest() -> int:
    expected = parse_manifest()
    actual = current_rows()
    if expected == actual:
        print(f"verified {MANIFEST} ({len(actual)} files)")
        return 0

    expected_map = {relative: value for value, relative in expected}
    actual_map = {relative: value for value, relative in actual}
    for relative in sorted(expected_map.keys() - actual_map.keys()):
        print(f"MISSING  {relative}")
    for relative in sorted(actual_map.keys() - expected_map.keys()):
        print(f"UNLISTED {relative}")
    for relative in sorted(expected_map.keys() & actual_map.keys()):
        if expected_map[relative] != actual_map[relative]:
            print(
                f"MISMATCH {relative} "
                f"expected={expected_map[relative]} actual={actual_map[relative]}"
            )
    return 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("write", "verify"))
    args = parser.parse_args()
    validate_root()
    return write_manifest() if args.mode == "write" else verify_manifest()


if __name__ == "__main__":
    sys.exit(main())
