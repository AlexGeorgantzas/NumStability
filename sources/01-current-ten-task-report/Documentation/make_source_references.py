#!/usr/bin/env python3
"""Extract namespace-resolved NumStability source uses from accepted Lean files.

Lean's .ilean reference index is produced offline from each hash-frozen final
Candidate.lean. It records source ranges and resolved declaration names; it
is not a contestant or auditor rerun. Counts below are source reference
sites, not occurrences in expanded kernel expressions.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess


HERE = Path(__file__).resolve().parent
REPO = Path(os.environ.get("NUMSTABILITY_REPO", str(HERE.parents[2])))
LEDGER = REPO / "benchmark/results/usage_metric_points.json"
REMOTE = os.environ.get("TITAN_HOST", "<user>@<host-ip>")
DEPLOYMENT = os.environ.get("NUMSTABILITY_DEPLOYMENT", "<data-drive>/highambench/deployment-pilot19-cli0156/deployment.json")
SCRATCH = os.environ.get("NUMSTABILITY_SCAN_SCRATCH", "<data-drive>/highambench/ten-task-occurrences-20261001")
INDEX_DIR = HERE / "source_ileans"
RESULT = HERE / "source_reference_counts.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(argv: list[str], *, timeout: int = 700) -> str:
    proc = subprocess.run(argv, text=True, capture_output=True, timeout=timeout)
    if proc.returncode:
        raise RuntimeError(f"{argv} exited {proc.returncode}:\n"
                           f"stdout: {proc.stdout[-1500:]}\nstderr: {proc.stderr[-1500:]}")
    return proc.stdout


def remote(command: str, *, timeout: int = 700) -> str:
    return run(["ssh", "-o", "BatchMode=yes", REMOTE, command], timeout=timeout)


def q(text: str) -> str:
    return shlex.quote(text)


def names_and_sites(index: dict) -> dict[str, list[list]]:
    result: dict[str, list[list]] = {}
    for key, info in index["references"].items():
        ident = json.loads(key).get("c")
        if not isinstance(ident, dict):
            continue
        module, name = ident.get("m", ""), ident.get("n", "")
        if module != "NumStability" and not module.startswith("NumStability."):
            continue
        if not name.startswith("NumStability."):
            raise ValueError(f"unexpected library name: {name}")
        sites = [site for site in info["usages"] if len(site) in (4, 5)]
        if len(sites) != len(info["usages"]):
            raise ValueError(f"malformed source locations: {name}")
        if sites:
            result.setdefault(name, []).extend(sites)
    for name, sites in result.items():
        unique = {tuple(site) for site in sites}
        if len(unique) != len(sites):
            raise ValueError(f"duplicate source location for {name}")
    return result


def main() -> None:
    ledger = json.loads(LEDGER.read_text())
    assert len(ledger["rows"]) == 10
    fields = remote(f"jq -r '.library_olean,.toolchain_root,.packages_root' {q(DEPLOYMENT)}")
    library, toolchain, packages = fields.strip().splitlines()
    common = str(Path(packages).parents[1])
    lake = f"{toolchain}/bin/lake"
    lean = f"{toolchain}/bin/lean"
    base = remote(f"cd {q(common)} && {q(lake)} env printenv LEAN_PATH").strip()
    INDEX_DIR.mkdir(exist_ok=True)

    rows = []
    for row in ledger["rows"]:
        task = row["task_id"]
        assert re.fullmatch(r"[A-Za-z0-9_.-]+", task)
        candidate = REPO / row["accepted_proof_path"]
        assert sha256(candidate) == row["accepted_proof_sha256"]
        task_dir = f"{SCRATCH}/{task}"
        copied = remote(f"sha256sum {q(task_dir + '/Candidate.lean')}").split()[0]
        assert copied == row["accepted_proof_sha256"]
        command = (f"cd {q(task_dir)} && "
                   f"LEAN_PATH={q(library + ':' + base)} {q(lean)} "
                   "-i Candidate.ilean Candidate.lean")
        remote(command)
        local_index = INDEX_DIR / f"{task}.ilean"
        run(["scp", "-q", f"{REMOTE}:{task_dir}/Candidate.ilean", str(local_index)])
        index = json.loads(local_index.read_text())
        assert index["module"] == "Candidate"
        uses = names_and_sites(index)
        counts = {name: len(sites) for name, sites in sorted(uses.items())}
        rows.append({
            "task_id": task,
            "candidate_sha256": copied,
            "ilean_sha256": sha256(local_index),
            "distinct_source_names": len(counts),
            "source_references": sum(counts.values()),
            "per_name": counts,
            "source_sites": uses,
        })
        print(task, len(counts), sum(counts.values()), flush=True)

    RESULT.write_text(json.dumps({
        "schema": "namespace-resolved-source-references-v1",
        "definition": "Lean .ilean usage locations for NumStability constants in each final accepted L Candidate.lean; imports/comments omitted by Lean; all source declarations in the file, including helpers, counted",
        "metric_ledger_sha256": sha256(LEDGER),
        "deployment_record": DEPLOYMENT,
        "task_count": len(rows),
        "rows": rows,
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
