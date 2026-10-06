#!/usr/bin/env python3
"""Write provenance and checksums for the timing/proof-hygiene sub-audit."""

from __future__ import annotations

import csv
import datetime as dt
import hashlib
import json
import subprocess
from pathlib import Path


AUDIT = Path(__file__).resolve().parents[1]
ROOT = AUDIT / "_worktree"
TIMINGS = AUDIT / "timings"
HYGIENE = AUDIT / "hygiene"
REPORT = AUDIT / "TIMINGS_AND_PROOF_HYGIENE.md"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def command(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def main() -> int:
    with (TIMINGS / "fresh_module_timings_effective.csv").open(newline="", encoding="utf-8") as handle:
        effective = list(csv.DictReader(handle))
    environment = json.loads((AUDIT / "provenance" / "build_environment.json").read_text(encoding="utf-8"))
    tools = [
        TIMINGS / "run_fresh_module_timings.py",
        TIMINGS / "rerun_interfered_timings.py",
        TIMINGS / "summarize_timings.py",
        HYGIENE / "RepresentativeAxioms.lean",
        HYGIENE / "parse_axiom_probe.py",
        HYGIENE / "analyze_proof_hygiene.py",
        AUDIT / "tooling" / "current_audit" / "DeclarationMetadata.lean",
        AUDIT / "static_architecture" / "static_architecture.py",
    ]
    status = subprocess.check_output(["git", "status", "--porcelain=v1"], cwd=ROOT, text=True)
    symbolic = subprocess.run(
        ["git", "symbolic-ref", "-q", "--short", "HEAD"],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, check=False,
    )
    provenance = {
        "schema_version": "numstability.timing-hygiene-provenance.v1",
        "commit": command("git", "rev-parse", "HEAD"),
        "detached_head": symbolic.returncode != 0,
        "source_tree_clean_after": status == "",
        "source_status_porcelain": status.splitlines(),
        "captured_at": dt.datetime.now().astimezone().isoformat(),
        "timezone": "Europe/Athens (EEST, UTC+03:00 at capture)",
        "platform": environment["platform"],
        "toolchain": environment["toolchain"],
        "timing": {
            "sample_size": len(effective),
            "first_original_started_at": effective[0]["started_at_local"],
            "last_effective_started_at": max(r["started_at_local"] for r in effective),
            "class": "fresh target .olean/.ilean with exact cached imports",
            "output_paths_initially_absent": True,
            "output_artifacts_removed_after_hashing": True,
            "known_interference_rows_replaced": [25, 26],
        },
        "axiom_probe": {
            "command": "lake env lean <audit>/hygiene/RepresentativeAxioms.lean",
            "return_code": 0,
            "cache_class": "diagnostic elaboration with exact cached imports; not a performance measurement",
        },
        "tool_sha256": {str(p.relative_to(AUDIT)): sha256(p) for p in tools},
        "metric_contract_thresholds": {
            "fresh_output_review_seconds_strictly_greater_than": 20,
            "fresh_output_priority_seconds_strictly_greater_than": 40,
        },
    }
    (TIMINGS / "timing_hygiene_provenance.json").write_text(
        json.dumps(provenance, indent=2) + "\n", encoding="utf-8"
    )

    checksum_path = TIMINGS / "TIMING_HYGIENE_SHA256SUMS"
    candidates = [REPORT]
    for folder in (TIMINGS, HYGIENE):
        candidates.extend(
            p for p in folder.rglob("*")
            if p.is_file() and "__pycache__" not in p.parts and p != checksum_path
        )
    lines = [f"{sha256(path)}  {path.relative_to(AUDIT)}" for path in sorted(set(candidates))]
    checksum_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
