#!/usr/bin/env python3
"""Offline, hash-checked elaborated-constant occurrence scan for accepted L proofs.

This is not a contestant rerun. Each archived Candidate.lean is recompiled in
an isolated /hdd scratch directory on Titan against the frozen deployment.
The scanner counts Expr.const nodes in the target statement/proof and the
bodies of reachable Candidate-local declarations, visiting each local body
once. External library declarations are not unfolded.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REMOTE = "<user>@<host-ip>"
DEPLOYMENT = "<data-drive>/highambench/deployment-pilot19-cli0156/deployment.json"
SCRATCH = "<data-drive>/highambench/ten-task-occurrences-20261001"
SCANNER = HERE / "direct_occurrence_scan.lean"
RESULT = HERE / "direct_occurrences.json"
SCAN = ROOT / "benchmark/results/declaration_scan.json"
POINTS = ROOT / "benchmark/results/usage_metric_points.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(argv: list[str], *, timeout: int = 700) -> str:
    result = subprocess.run(argv, text=True, capture_output=True, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {argv}\n"
                           f"stdout: {result.stdout[-2500:]}\n"
                           f"stderr: {result.stderr[-2500:]}")
    return result.stdout


def remote(command: str, *, timeout: int = 700) -> str:
    return run(["ssh", "-o", "BatchMode=yes", REMOTE, command], timeout=timeout)


def quote(value: str) -> str:
    return shlex.quote(value)


def main() -> None:
    points = json.loads(POINTS.read_text())
    scans = {row["task_id"]: row for row in json.loads(SCAN.read_text())}
    assert len(points["rows"]) == len(scans) == 10
    assert sha256(SCANNER)

    fields = remote(f"jq -r '.library_olean,.toolchain_root,.packages_root' {quote(DEPLOYMENT)}")
    library, toolchain, packages = fields.strip().splitlines()
    common = str(Path(packages).parents[1])
    lean = f"{toolchain}/bin/lean"
    lake = f"{toolchain}/bin/lake"
    base_path = remote(f"cd {quote(common)} && {quote(lake)} env printenv LEAN_PATH").strip()
    assert base_path and library.startswith("/hdd/")
    remote(f"mkdir -p {quote(SCRATCH)}")
    run(["scp", "-q", str(SCANNER), f"{REMOTE}:{SCRATCH}/direct_occurrence_scan.lean"])
    remote_hash = remote(f"sha256sum {quote(SCRATCH + '/direct_occurrence_scan.lean')}").split()[0]
    assert remote_hash == sha256(SCANNER)

    output = []
    for row in points["rows"]:
        task = row["task_id"]
        assert re.fullmatch(r"[A-Za-z0-9_.-]+", task)
        candidate = ROOT / row["accepted_proof_path"]
        assert sha256(candidate) == row["accepted_proof_sha256"]
        task_dir = f"{SCRATCH}/{task}"
        remote(f"mkdir -p {quote(task_dir)}")
        run(["scp", "-q", str(candidate), f"{REMOTE}:{task_dir}/Candidate.lean"])
        copied_hash = remote(f"sha256sum {quote(task_dir + '/Candidate.lean')}").split()[0]
        assert copied_hash == sha256(candidate)
        compile_path = f"{library}:{base_path}"
        compile_command = (f"cd {quote(task_dir)} && "
                           f"LEAN_PATH={quote(compile_path)} {quote(lean)} "
                           "-o Candidate.olean Candidate.lean")
        remote(compile_command)
        scan_path = f"{task_dir}:{compile_path}"
        scan_command = (f"cd {quote(task_dir)} && "
                        f"PATH={quote(toolchain + '/bin')}:\"$PATH\" "
                        f"LEAN_PATH={quote(scan_path)} {quote(lean)} --run "
                        f"{quote(SCRATCH + '/direct_occurrence_scan.lean')} "
                        "Candidate HighamBenchCandidate.target")
        raw = remote(scan_command)
        names: dict[str, dict[str, int]] = {"statement": {}, "proof": {}}
        summaries: dict[str, tuple[int, int]] = {}
        for line in raw.splitlines():
            parts = line.split("\t")
            if parts[0] == "name" and len(parts) == 4:
                _, surface, name, count = parts
                names[surface][name] = int(count)
            elif parts[0] == "summary" and len(parts) == 4:
                _, surface, distinct, occurrences = parts
                summaries[surface] = (int(distinct), int(occurrences))
        assert set(summaries) == {"statement", "proof"}, (task, raw)
        for surface in ("statement", "proof"):
            assert summaries[surface] == (len(names[surface]), sum(names[surface].values()))
            expected = set(scans[task][f"{surface}_names"])
            actual = set(names[surface])
            if actual != expected:
                raise RuntimeError(f"{task} {surface} name-set mismatch: "
                                   f"missing={sorted(expected-actual)} extra={sorted(actual-expected)}")
        output.append({
            "task_id": task,
            "candidate_sha256": copied_hash,
            "distinct_statement": summaries["statement"][0],
            "occurrences_statement": summaries["statement"][1],
            "distinct_proof": summaries["proof"][0],
            "occurrences_proof": summaries["proof"][1],
            "distinct_union": len(set(names["statement"]) | set(names["proof"])),
            "occurrences_combined": summaries["statement"][1] + summaries["proof"][1],
            "statement_names": names["statement"],
            "proof_names": names["proof"],
        })
        print(task, summaries, flush=True)

    record = {
        "schema": "direct-elaborated-occurrences-v1",
        "definition": "Expr.const node frequency in target type/proof and reachable Candidate-local declaration bodies, each local body once; imported definitions not unfolded; combined occurrences sum statement and proof surfaces",
        "source_metric_ledger_sha256": sha256(POINTS),
        "source_declaration_scan_sha256": sha256(SCAN),
        "scanner_sha256": sha256(SCANNER),
        "deployment_record": DEPLOYMENT,
        "task_count": len(output),
        "rows": output,
    }
    RESULT.write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
