#!/usr/bin/env python3
"""Recompute ten-task-style direct proof use for accepted historical L proofs.

The manifest phase pins archived accepted-file hashes and target names. The
scan phase recompiles each file with the historical Lean/Mathlib/NumStability
snapshot, then runs the same proof-term-and-local-helper scanner used by the
ten-task benchmark. This is post-run analysis, never a contestant rerun.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


ATTEMPT_CSV_SHA256 = "bd536d94b2c5e98eebc68d8e3e81a96b879498278317f21eee5bc2dc9712a43a"
SCOPE_CSV_SHA256 = "28a38a3151d873a1c27c2f8cf955d38599a49dadbf0e8d2e92c6fdfbcf3fe8c8"
LIBRARY_COMMIT = "045daf28056a6e4358d5de7c22c7a9d7acc2e80e"
MATHLIB_COMMIT = "e8ea1afc32790ce1d4e1a4e45cc412ba9388716b"
LEAN_VERSION = "4.29.0-rc3"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def make_manifest(args: argparse.Namespace) -> None:
    attempts = Path(args.attempt_csv)
    scope = Path(args.scope_csv)
    proof_root = Path(args.proof_root).resolve()
    if digest(attempts) != ATTEMPT_CSV_SHA256 or digest(scope) != SCOPE_CSV_SHA256:
        raise ValueError("archived attempt/scope CSV identity differs from report")
    retained = {row["task_id"] for row in read_csv(scope)}
    entries = []
    corpus_by_run: dict[str, dict[str, str]] = {}
    for row in read_csv(attempts):
        if row["task_id"] not in retained or row["condition"] != "L":
            continue
        relative = Path(row["proof_path"])
        proof = (proof_root / relative).resolve()
        if not proof.is_relative_to(proof_root) or digest(proof) != row["proof_sha256"]:
            raise ValueError(f"archived accepted proof does not match: {relative}")
        attempt = (proof_root / row["attempt_path"]).resolve()
        if not attempt.is_relative_to(proof_root) or digest(attempt) != row["attempt_sha256"]:
            raise ValueError(f"archived attempt does not match: {row['attempt_path']}")
        record = json.loads(attempt.read_text())
        if record.get("pass") is not True:
            raise ValueError(f"attempt was not accepted: {relative}")
        target = record["validation"]["target_theorem"]
        run = row["source_run"]
        if run not in corpus_by_run:
            corpus = proof_root / "measurements/runs" / run / "environment/corpus_manifest.json"
            corpus_by_run[run] = {file["path"]: file["sha256"]
                                  for file in json.loads(corpus.read_text())["files"]}
        paper = row["task_id"].split("-")[0]
        definition = f"HighamBench/{paper}Definitions.lean"
        definition_sha = corpus_by_run[run][f"shared/{definition}"]
        archived_definition = proof_root / "paper_bencmark/highambench/shared" / definition
        if digest(archived_definition) != definition_sha:
            raise ValueError(f"shared definition source does not match historical corpus: {definition}")
        entries.append({
            "task_id": row["task_id"], "pair_id": row["pair_id"],
            "source_run": row["source_run"], "condition": "L",
            "proof_path": relative.as_posix(), "proof_sha256": row["proof_sha256"],
            "attempt_path": row["attempt_path"],
            "attempt_sha256": row["attempt_sha256"], "target_theorem": target,
            "common_definition": definition,
            "common_definition_sha256": definition_sha,
        })
    entries.sort(key=lambda item: (item["task_id"], item["pair_id"]))
    if len(entries) != 90 or len({item["task_id"] for item in entries}) != 30:
        raise ValueError(f"expected 90 accepted L proofs for 30 tasks, got {len(entries)}")
    output = {
        "schema": "historical-dp-manifest-v1",
        "attempt_csv_sha256": ATTEMPT_CSV_SHA256,
        "scope_csv_sha256": SCOPE_CSV_SHA256,
        "library_commit": LIBRARY_COMMIT,
        "mathlib_commit": MATHLIB_COMMIT,
        "lean_version": LEAN_VERSION,
        "entries": entries,
    }
    Path(args.output).write_text(json.dumps(output, indent=2) + "\n")


def run_checked(command: list[str], *, cwd: Path, env: dict[str, str],
                timeout: int) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                            text=True, timeout=timeout, check=False)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {command}\n"
                           f"stdout:\n{result.stdout[-3000:]}\n"
                           f"stderr:\n{result.stderr[-3000:]}")
    return result


def compile_definitions(args: argparse.Namespace, entries: list[dict],
                        env: dict[str, str], lean: Path) -> list[str]:
    task_root = Path(args.task_root)
    modules = sorted({line.split()[1] for entry in entries
                      for line in (task_root / entry["proof_path"]).read_text().splitlines()
                      if line.startswith("import HighamBench.")})
    for entry in entries:
        source = task_root / entry["common_definition"]
        if digest(source) != entry["common_definition_sha256"]:
            raise ValueError(f"shared definition source differs from historical corpus: {source}")
    def compile_one(module: str) -> None:
        relative = Path(*module.split("."))
        source = task_root / relative.with_suffix(".lean")
        olean = task_root / relative.with_suffix(".olean")
        if not source.is_file():
            raise ValueError(f"missing frozen common definition: {source}")
        if not olean.is_file() or olean.stat().st_mtime < source.stat().st_mtime:
            run_checked([str(lean), "-j", "1", "-o", str(olean), str(source)], cwd=task_root,
                        env=env, timeout=1200)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for module, _ in zip(modules, pool.map(compile_one, modules)):
            print(f"definition {module}", flush=True)
    return modules


def scan_one(entry: dict, args: argparse.Namespace, env: dict[str, str],
             lean: Path, scanner: Path, scratch: Path,
             checkpoint_dir: Path) -> dict:
    source = Path(args.task_root) / entry["proof_path"]
    if digest(source) != entry["proof_sha256"]:
        raise ValueError(f"accepted source hash differs: {source}")
    checkpoint = checkpoint_dir / f"{entry['pair_id']}.json"
    if checkpoint.is_file():
        saved = json.loads(checkpoint.read_text())
        if (all(saved.get(key) == value for key, value in entry.items())
                and saved.get("scanner_sha256") == digest(scanner)
                and saved.get("direct_proof_count") ==
                    len(set(saved.get("direct_proof_names", [])))):
            return saved
        raise ValueError(f"invalid existing checkpoint: {checkpoint}")
    with tempfile.TemporaryDirectory(prefix="historical-dp-", dir=scratch) as name:
        temp = Path(name)
        candidate = temp / "Candidate.lean"
        shutil.copyfile(source, candidate)
        if digest(candidate) != entry["proof_sha256"]:
            raise ValueError(f"copied source hash differs: {source}")
        try:
            run_checked([str(lean), "-j", "1", "-o", "Candidate.olean",
                         "Candidate.lean"], cwd=temp, env=env, timeout=1200)
        except Exception as exc:
            raise RuntimeError(f"accepted proof recompilation failed: {source}: {exc}") from exc
        scan_env = dict(env)
        scan_env["LEAN_PATH"] = f"{temp}:{env['LEAN_PATH']}"
        try:
            result = run_checked([str(lean), "--run", str(scanner), "Candidate",
                                  entry["target_theorem"]], cwd=temp,
                                 env=scan_env, timeout=1200)
        except Exception as exc:
            raise RuntimeError(f"proof-term scan failed: {source}: {exc}") from exc
        names = sorted({line.split("\t", 1)[1]
                        for line in result.stdout.splitlines()
                        if line.startswith("proof-library\t")})
        summary = [line for line in result.stdout.splitlines()
                   if line.startswith("summary\t")]
        if len(summary) != 1 or int(summary[0].split("\t")[1]) != len(names):
            raise ValueError(f"invalid proof scanner summary: {source}")
        record = {**entry, "direct_proof_names": names,
                  "direct_proof_count": len(names),
                  "scanner_summary": summary[0],
                  "scanner_sha256": digest(scanner)}
        checkpoint.write_text(json.dumps(record, indent=2) + "\n")
        return record


def scan(args: argparse.Namespace) -> None:
    manifest_path = Path(args.manifest)
    manifest = json.loads(manifest_path.read_text())
    if manifest["library_commit"] != LIBRARY_COMMIT or len(manifest["entries"]) != 90:
        raise ValueError("unexpected rescan manifest")
    task_root = Path(args.task_root).resolve()
    library_root = Path(args.library_root).resolve()
    scratch = Path(args.scratch).resolve()
    scanner = Path(args.scanner).resolve()
    lean = Path(args.lean).resolve()
    lake = Path(args.lake).resolve()
    for path in (task_root, library_root, scratch, scanner, lean, lake):
        if not path.exists():
            raise ValueError(f"missing scan dependency: {path}")
    env = dict(os.environ)
    env["PATH"] = f"{lean.parent}:{env.get('PATH', '')}"
    env["TMPDIR"] = str(scratch)
    env["XDG_CACHE_HOME"] = str(scratch / "cache")
    Path(env["XDG_CACHE_HOME"]).mkdir(exist_ok=True)
    probe = run_checked([str(lake), "env", "printenv", "LEAN_PATH"],
                        cwd=library_root, env=env, timeout=120)
    env["LEAN_PATH"] = f"{task_root}:{probe.stdout.strip()}"
    modules = compile_definitions(args, manifest["entries"], env, lean)
    checkpoint_dir = Path(args.output).with_suffix(".checkpoints")
    checkpoint_dir.mkdir(exist_ok=True)
    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = {pool.submit(scan_one, entry, args, env, lean, scanner,
                               scratch, checkpoint_dir): entry
                   for entry in manifest["entries"]}
        for future in as_completed(pending):
            entry = pending[future]
            result = future.result()
            results.append(result)
            print(f"{len(results)}/90 {entry['pair_id']} DP={result['direct_proof_count']}",
                  flush=True)
    results.sort(key=lambda item: (item["task_id"], item["pair_id"]))
    Path(args.output).write_text(json.dumps({
        "schema": "historical-direct-proof-scan-v1",
        "manifest_sha256": digest(manifest_path),
        "scanner_sha256": digest(scanner),
        "library_commit": LIBRARY_COMMIT,
        "mathlib_commit": MATHLIB_COMMIT,
        "lean_version": LEAN_VERSION,
        "definition_modules_compiled": modules,
        "entries": results,
    }, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="mode", required=True)
    prepare = sub.add_parser("manifest")
    prepare.add_argument("--attempt-csv", required=True)
    prepare.add_argument("--scope-csv", required=True)
    prepare.add_argument("--proof-root", required=True)
    prepare.add_argument("--output", required=True)
    execute = sub.add_parser("scan")
    execute.add_argument("--manifest", required=True)
    execute.add_argument("--task-root", required=True)
    execute.add_argument("--library-root", required=True)
    execute.add_argument("--scratch", required=True)
    execute.add_argument("--scanner", required=True)
    execute.add_argument("--lean", required=True)
    execute.add_argument("--lake", required=True)
    execute.add_argument("--jobs", type=int, default=2)
    execute.add_argument("--output", required=True)
    args = parser.parse_args()
    if args.mode == "manifest":
        make_manifest(args)
    else:
        scan(args)


if __name__ == "__main__":
    main()
