#!/usr/bin/env python3
"""Replay the recovered Phase 10A ``scan_sources`` function without edits.

This wrapper is audit infrastructure only.  It imports the exact recovered
``generate_baseline.py`` blob from a caller-supplied path, invokes its
``scan_sources`` function, and serializes the result plus per-module rows.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import sys
from pathlib import Path


SCHEMA_VERSION = "numstability-phase10a-source-scan-replay/v1"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generator", type=Path, required=True)
    parser.add_argument("--worktree", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-modules", type=Path, required=True)
    args = parser.parse_args()

    spec = importlib.util.spec_from_file_location(
        "recovered_phase10a_generate_baseline", args.generator
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load recovered generator: {args.generator}")
    recovered = importlib.util.module_from_spec(spec)
    # Python 3.14's dataclass annotation resolution expects the module to be
    # registered while it is executed by an explicit importlib loader.
    sys.modules[spec.name] = recovered
    spec.loader.exec_module(recovered)

    summary, modules = recovered.scan_sources(args.worktree)
    wrapper_path = Path(__file__).resolve()
    envelope = {
        "schema_version": SCHEMA_VERSION,
        "target_commit": args.commit,
        "worktree": str(args.worktree.resolve()),
        "recovered_generator": str(args.generator.resolve()),
        "recovered_generator_sha256": sha256(args.generator),
        "wrapper": str(wrapper_path),
        "wrapper_sha256": sha256(wrapper_path),
        "function_invoked": "scan_sources",
        "function_source_modified": False,
        "source": summary,
        "module_rows_artifact": str(args.output_modules.resolve()),
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(envelope, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    fields = [
        "name",
        "path",
        "line_count",
        "nonblank_line_count",
        "byte_count",
        "direct_import_count",
        "imports",
        "has_module_docstring",
    ]
    with args.output_modules.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for module in modules:
            writer.writerow(
                {
                    "name": module.name,
                    "path": module.path,
                    "line_count": module.line_count,
                    "nonblank_line_count": module.nonblank_line_count,
                    "byte_count": module.byte_count,
                    "direct_import_count": len(module.imports),
                    "imports": ";".join(module.imports),
                    "has_module_docstring": str(module.has_module_docstring).lower(),
                }
            )

    print(json.dumps({
        "schema_version": SCHEMA_VERSION,
        "module_count": summary["module_count"],
        "line_count": summary["line_count"],
        "nonblank_line_count": summary["nonblank_line_count"],
        "byte_count": summary["byte_count"],
        "direct_import_count": summary["direct_import_count"],
        "internal_direct_import_count": summary["internal_direct_import_count"],
        "external_direct_import_count": summary["external_direct_import_count"],
        "unresolved_project_import_count": summary["unresolved_project_import_count"],
        "source_tree_sha256": summary["source_tree_sha256"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
