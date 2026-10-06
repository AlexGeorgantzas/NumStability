#!/usr/bin/env python3
"""Run a predeclared, deterministic sample of fresh-output Lean module timings.

The source tree and its cached dependency outputs are read-only.  Each sampled
source is elaborated to a unique, initially absent .olean/.ilean pair under the
ignored audit directory.  Sizes and hashes are recorded, then those two fresh
outputs are deleted immediately to bound disk use.  The timing therefore is a
fresh *target-output* timing with exact cached imports, not a clean-library
build timing.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import re
import signal
import subprocess
import time
from pathlib import Path


AUDIT = Path(__file__).resolve().parents[1]
ROOT = AUDIT / "_worktree"
STATIC_MODULES = AUDIT / "static_architecture" / "modules.csv"
OUT = AUDIT / "timings"
FRESH = OUT / "fresh_outputs"
LOGS = OUT / "logs"

# Frozen before timing began.  Selection is deliberately stratified rather
# than random: public roots/re-export surfaces, lower layers, major domains,
# source wrappers, and the largest source modules are all represented.
SAMPLE: list[tuple[str, str, str]] = [
    ("NumStability", "entry_point", "library root"),
    ("NumStability.All", "entry_point", "complete public aggregate"),
    ("NumStability.FloatingPoint", "entry_point", "FloatingPoint aggregate"),
    ("NumStability.Analysis", "entry_point", "Analysis aggregate"),
    ("NumStability.Algorithms", "entry_point", "Algorithms aggregate"),
    ("NumStability.Source", "entry_point", "Source aggregate"),
    ("NumStability.Source.Higham", "entry_point", "Higham source aggregate"),
    ("NumStability.FloatingPoint.Model", "layer_domain", "floating-point model foundation"),
    ("NumStability.FloatingPoint.FusedMultiplyAdd.Core", "layer_domain", "floating-point FMA foundation"),
    ("NumStability.Analysis.FloatingPointArithmetic.Rounding", "layer_domain", "rounding analysis"),
    ("NumStability.Analysis.Error.RoundingProducts.Core", "layer_domain", "gamma/rounding-product analysis"),
    ("NumStability.Analysis.MatrixNorms.Basic", "layer_domain", "matrix norms"),
    ("NumStability.Analysis.VectorNorms.Basic", "layer_domain", "vector norms"),
    ("NumStability.Analysis.Conditioning.InversePerturbation", "layer_domain", "conditioning and perturbation"),
    ("NumStability.Analysis.Perturbation.LeastSquares.Basic", "large_domain", "large least-squares analysis module"),
    ("NumStability.Algorithms.DotProduct", "layer_domain", "dot-product algorithm"),
    ("NumStability.Algorithms.MatMul", "layer_domain", "matrix multiplication"),
    ("NumStability.Algorithms.MatMulBackwardError", "layer_domain", "matrix-multiplication backward error"),
    ("NumStability.Algorithms.LU.LUSolve", "layer_domain", "LU solver"),
    ("NumStability.Algorithms.LinearSystems.QR.QRSolve", "large_domain", "QR solver"),
    ("NumStability.Algorithms.Summation.Insertion.Schedule", "large_domain", "largest Algorithms source by code-bearing lines"),
    ("NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal", "large_domain", "large matrix-equation solver module"),
    ("NumStability.Source.Higham.Chapter09", "chapter_entry", "Chapter 9 source entry point"),
    ("NumStability.Source.Higham.Chapter12", "chapter_entry", "Chapter 12 source entry point"),
    ("NumStability.Source.Higham.Chapter09.Section11", "largest_source", "large Chapter 9 source module"),
    ("NumStability.Source.Higham.Chapter11.Section01.Tridiagonal", "largest_source", "largest library source by code-bearing lines"),
    ("NumStability.Source.Higham.Chapter19.Core", "largest_source", "large Chapter 19 source module"),
    ("NumStability.Source.Higham.Chapter20.Theorem03.QRSolve", "large_source_domain", "large source-facing QR theorem module"),
    ("NumStability.Source.Higham.Chapter12.IterativeRefinement.Results.Theorems", "cross_chapter_endpoint", "Chapter 12 iterative-refinement endpoint"),
    ("NumStability.Source.Higham.Chapter03.Lemma01.RoundingProducts.All", "source_bridge", "source-facing rounding-products bridge"),
]

TIME_RE = {
    "real_seconds": re.compile(r"^real\s+([0-9.]+)$", re.MULTILINE),
    "user_seconds": re.compile(r"^user\s+([0-9.]+)$", re.MULTILINE),
    "sys_seconds": re.compile(r"^sys\s+([0-9.]+)$", re.MULTILINE),
    "max_rss_bytes": re.compile(r"^\s*(\d+)\s+maximum resident set size$", re.MULTILINE),
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_profiles() -> dict[str, dict[str, str]]:
    with STATIC_MODULES.open(newline="", encoding="utf-8") as handle:
        return {row["module"]: row for row in csv.DictReader(handle)}


def source_for(module: str, row: dict[str, str]) -> Path:
    source = ROOT / row["source_path"]
    if not source.is_file():
        raise FileNotFoundError(f"missing source for {module}: {source}")
    return source


def slug(module: str) -> str:
    return module.replace(".", "__")


def write_selection(profiles: dict[str, dict[str, str]]) -> None:
    path = OUT / "timing_sample_predeclared.csv"
    fields = [
        "sample_index", "module", "selection_stratum", "selection_reason",
        "source_path", "effective_architectural_layer", "domain_guess",
        "chapter_guess", "physical_lines", "code_bearing_lines",
        "static_declaration_starter_count",
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for i, (module, stratum, reason) in enumerate(SAMPLE, 1):
            r = profiles[module]
            writer.writerow({
                "sample_index": i,
                "module": module,
                "selection_stratum": stratum,
                "selection_reason": reason,
                "source_path": r["source_path"],
                "effective_architectural_layer": r["effective_architectural_layer"],
                "domain_guess": r["domain_guess"],
                "chapter_guess": r["chapter_guess"],
                "physical_lines": r["physical_lines"],
                "code_bearing_lines": r["code_bearing_lines"],
                "static_declaration_starter_count": r["static_declaration_starter_count"],
            })


def parse_time(stderr: str, field: str) -> str:
    match = TIME_RE[field].search(stderr)
    return match.group(1) if match else ""


def terminate_group(process: subprocess.Popen[str]) -> None:
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def run_one(index: int, module: str, row: dict[str, str], timeout: int) -> dict[str, object]:
    source = source_for(module, row)
    stem = slug(module)
    olean = FRESH / f"{stem}.olean"
    ilean = FRESH / f"{stem}.ilean"
    stdout_path = LOGS / f"{index:02d}_{stem}.stdout.log"
    stderr_path = LOGS / f"{index:02d}_{stem}.stderr.log"
    for target in (olean, ilean):
        if target.exists():
            raise RuntimeError(f"fresh output already exists: {target}")
    command = [
        "/usr/bin/time", "-lp", "lake", "env", "lean",
        "-o", str(olean), "-i", str(ilean), str(source),
    ]
    started = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    wall_start = time.perf_counter()
    timed_out = False
    with stdout_path.open("w", encoding="utf-8") as stdout_handle, stderr_path.open(
        "w", encoding="utf-8"
    ) as stderr_handle:
        process = subprocess.Popen(
            command,
            cwd=ROOT,
            text=True,
            stdout=stdout_handle,
            stderr=stderr_handle,
            start_new_session=True,
        )
        try:
            return_code = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            terminate_group(process)
            return_code = 124
    observed_wall = time.perf_counter() - wall_start
    stderr = stderr_path.read_text(encoding="utf-8", errors="replace")
    stdout = stdout_path.read_text(encoding="utf-8", errors="replace")
    result: dict[str, object] = {
        "sample_index": index,
        "module": module,
        "source_path": str(source.relative_to(ROOT)),
        "started_at_local": started,
        "cache_class": "fresh target .olean/.ilean; exact cached imports",
        "command": " ".join(command),
        "return_code": return_code,
        "timed_out": str(timed_out).lower(),
        "wall_seconds_observed": f"{observed_wall:.6f}",
        "real_seconds": parse_time(stderr, "real_seconds"),
        "user_seconds": parse_time(stderr, "user_seconds"),
        "sys_seconds": parse_time(stderr, "sys_seconds"),
        "max_rss_bytes": parse_time(stderr, "max_rss_bytes"),
        "olean_bytes": olean.stat().st_size if olean.exists() else "",
        "olean_sha256": sha256(olean) if olean.exists() else "",
        "ilean_bytes": ilean.stat().st_size if ilean.exists() else "",
        "ilean_sha256": sha256(ilean) if ilean.exists() else "",
        "stdout_log": str(stdout_path.relative_to(AUDIT)),
        "stderr_log": str(stderr_path.relative_to(AUDIT)),
        "warning_count": stdout.count("warning:") + stderr.count("warning:"),
        "error_count_text": stdout.count("error:") + stderr.count("error:"),
    }
    # The explicit targets are constrained beneath this audit directory and
    # were constructed from a fixed slug; unlinking them cannot touch sources.
    for target in (olean, ilean):
        target.unlink(missing_ok=True)
    return result


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    FRESH.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    profiles = load_profiles()
    missing = [module for module, _, _ in SAMPLE if module not in profiles]
    if missing:
        raise SystemExit(f"sample modules absent from static inventory: {missing}")
    write_selection(profiles)

    timing_path = OUT / "fresh_module_timings.csv"
    fields = [
        "sample_index", "module", "source_path", "started_at_local",
        "cache_class", "command", "return_code", "timed_out",
        "wall_seconds_observed", "real_seconds", "user_seconds", "sys_seconds",
        "max_rss_bytes", "olean_bytes", "olean_sha256", "ilean_bytes",
        "ilean_sha256", "stdout_log", "stderr_log", "warning_count",
        "error_count_text",
    ]
    completed: set[str] = set()
    if timing_path.exists():
        with timing_path.open(newline="", encoding="utf-8") as handle:
            completed = {r["module"] for r in csv.DictReader(handle)}
    write_header = not timing_path.exists()
    with timing_path.open("a", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        if write_header:
            writer.writeheader()
        for index, (module, _, _) in enumerate(SAMPLE, 1):
            if module in completed:
                continue
            row = run_one(index, module, profiles[module], timeout=900)
            writer.writerow(row)
            handle.flush()
            print(
                f"[{index:02d}/{len(SAMPLE)}] {module}: "
                f"rc={row['return_code']} wall={row['wall_seconds_observed']}s",
                flush=True,
            )

    metadata = {
        "schema_version": "numstability.fresh-module-timing-sample.v1",
        "commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "sample_predeclared_before_measurement": True,
        "sample_size": len(SAMPLE),
        "timeout_seconds_per_module": 900,
        "cache_class": "fresh target outputs with exact cached imported modules",
        "interpretation": (
            "Times measure re-elaboration and fresh .olean/.ilean emission for only "
            "the selected target file. Imported module artifacts are cached. This is "
            "not a clean whole-library build and the percentiles are sample-only."
        ),
    }
    (OUT / "timing_method.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
