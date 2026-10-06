#!/usr/bin/env python3
"""Capture a reproducible, read-only baseline for the NumStability library."""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path


IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private|protected|meta)\s+)*import\s+([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)


def run_text(command: list[str], cwd: Path) -> dict[str, object]:
    completed = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return {
        "command": command,
        "return_code": completed.returncode,
        "output": completed.stdout.strip(),
    }


def module_name(root: Path, source: Path) -> str:
    return ".".join(source.relative_to(root).with_suffix("").parts)


def source_files(root: Path) -> list[Path]:
    files = sorted((root / "NumStability").rglob("*.lean"))
    umbrella = root / "NumStability.lean"
    if umbrella.exists():
        files.append(umbrella)
    return sorted(files)


def write_file_statistics(root: Path, output: Path) -> dict[str, int]:
    files = source_files(root)
    total_lines = 0
    total_bytes = 0
    import_edges = 0
    with (output / "files.csv").open("w", newline="", encoding="utf-8") as handle, (
        output / "module_imports_source.csv"
    ).open("w", newline="", encoding="utf-8") as import_handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "file",
                "module",
                "line_count",
                "byte_count",
                "direct_import_count",
            ],
        )
        import_writer = csv.DictWriter(
            import_handle, fieldnames=["source_module", "target_module"]
        )
        writer.writeheader()
        import_writer.writeheader()
        for source in files:
            raw = source.read_bytes()
            text = raw.decode("utf-8")
            line_count = len(text.splitlines())
            imports = IMPORT_RE.findall(text)
            source_module = module_name(root, source)
            writer.writerow(
                {
                    "file": str(source.relative_to(root)),
                    "module": source_module,
                    "line_count": line_count,
                    "byte_count": len(raw),
                    "direct_import_count": len(imports),
                }
            )
            for target in imports:
                import_writer.writerow(
                    {"source_module": source_module, "target_module": target}
                )
            total_lines += line_count
            total_bytes += len(raw)
            import_edges += len(imports)
    return {
        "lean_file_count": len(files),
        "line_count": total_lines,
        "byte_count": total_bytes,
        "source_direct_import_count": import_edges,
    }


def run_build(root: Path, output: Path) -> dict[str, object]:
    started = dt.datetime.now(dt.timezone.utc)
    start = time.perf_counter()
    with (output / "lake-build.log").open("w", encoding="utf-8") as log:
        completed = subprocess.run(
            ["lake", "build"],
            cwd=root,
            text=True,
            stdout=log,
            stderr=subprocess.STDOUT,
            check=False,
        )
    duration = time.perf_counter() - start
    return {
        "command": ["lake", "build"],
        "cache_state": "incremental build using the artifacts present at baseline time",
        "started_at": started.isoformat(),
        "duration_seconds": round(duration, 6),
        "return_code": completed.returncode,
        "log": "lake-build.log",
    }


def read_completed_timings(path: Path) -> set[str]:
    if not path.exists():
        return set()
    with path.open(newline="", encoding="utf-8") as handle:
        return {row["module"] for row in csv.DictReader(handle)}


def time_modules(
    root: Path,
    output: Path,
    timeout_seconds: int,
    limit: int | None,
    selected_modules: set[str] | None,
) -> dict[str, object]:
    timing_path = output / "module_compile_times.csv"
    completed_modules = read_completed_timings(timing_path)
    files = [
        source
        for source in source_files(root)
        if module_name(root, source) not in completed_modules
        and (
            selected_modules is None
            or module_name(root, source) in selected_modules
        )
    ]
    if limit is not None:
        files = files[:limit]
    write_header = not timing_path.exists()
    succeeded = 0
    failed = 0
    timed_out = 0
    with timing_path.open("a", newline="", encoding="utf-8") as handle, tempfile.TemporaryDirectory(
        prefix="numstability-module-timings-"
    ) as temporary:
        fields = [
            "module",
            "file",
            "duration_seconds",
            "return_code",
            "timed_out",
            "diagnostic_excerpt",
        ]
        writer = csv.DictWriter(handle, fieldnames=fields)
        if write_header:
            writer.writeheader()
        temporary_root = Path(temporary)
        for number, source in enumerate(files, start=1):
            module = module_name(root, source)
            artifact = temporary_root / Path(*module.split(".")).with_suffix(".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            start = time.perf_counter()
            was_timeout = False
            try:
                result = subprocess.run(
                    ["lake", "env", "lean", "-o", str(artifact), str(source)],
                    cwd=root,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    timeout=timeout_seconds,
                    check=False,
                )
                return_code = result.returncode
                excerpt = result.stdout[-4000:]
            except subprocess.TimeoutExpired as error:
                return_code = 124
                was_timeout = True
                raw_output = error.stdout or ""
                excerpt = raw_output[-4000:] if isinstance(raw_output, str) else ""
            duration = time.perf_counter() - start
            writer.writerow(
                {
                    "module": module,
                    "file": str(source.relative_to(root)),
                    "duration_seconds": round(duration, 6),
                    "return_code": return_code,
                    "timed_out": str(was_timeout).lower(),
                    "diagnostic_excerpt": excerpt,
                }
            )
            handle.flush()
            if was_timeout:
                timed_out += 1
            elif return_code == 0:
                succeeded += 1
            else:
                failed += 1
            print(
                f"[{number}/{len(files)}] {module}: {duration:.3f}s "
                f"(return_code={return_code})",
                flush=True,
            )
    return {
        "attempted_this_run": len(files),
        "already_recorded": len(completed_modules),
        "succeeded_this_run": succeeded,
        "failed_this_run": failed,
        "timed_out_this_run": timed_out,
        "timeout_seconds_per_module": timeout_seconds,
        "resumable_output": "module_compile_times.csv",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--run-build", action="store_true")
    parser.add_argument("--time-modules", action="store_true")
    parser.add_argument("--module-timeout", type=int, default=3600)
    parser.add_argument("--module-limit", type=int)
    parser.add_argument(
        "--module",
        action="append",
        dest="modules",
        help="time only this exact module (repeatable)",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[2]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    baseline_path = output / "baseline.json"
    metadata: dict[str, object] = {}
    if baseline_path.exists():
        metadata = json.loads(baseline_path.read_text(encoding="utf-8"))
    lakefile_text = (root / "lakefile.toml").read_text(encoding="utf-8")
    mathlib_revision_match = re.search(
        r'\[\[require\]\]\s+name\s*=\s*"mathlib".*?rev\s*=\s*"([^"]+)"',
        lakefile_text,
        re.DOTALL,
    )
    metadata.update({
        "schema_version": 1,
        "captured_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "repository_root": str(root),
        "git_commit": run_text(["git", "rev-parse", "HEAD"], root),
        "git_branch": run_text(["git", "branch", "--show-current"], root),
        "git_status": run_text(["git", "status", "--short"], root),
        "library_source_status": run_text(
            ["git", "status", "--short", "--", "NumStability", "NumStability.lean"],
            root,
        ),
        "lean_version": run_text(["lake", "env", "lean", "--version"], root),
        "lake_version": run_text(["lake", "--version"], root),
        "lean_toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lakefile": lakefile_text,
        "mathlib_revision": (
            mathlib_revision_match.group(1) if mathlib_revision_match else "unknown"
        ),
        "file_statistics": write_file_statistics(root, output),
    })
    if args.run_build:
        metadata["full_build"] = run_build(root, output)
    else:
        metadata.setdefault(
            "full_build",
            {"status": "not requested", "required_command": "lake build"},
        )
    if args.time_modules:
        metadata["module_compilation_timings"] = time_modules(
            root,
            output,
            args.module_timeout,
            args.module_limit,
            set(args.modules) if args.modules else None,
        )
    else:
        metadata.setdefault(
            "module_compilation_timings",
            {"status": "not requested", "required_flag": "--time-modules"},
        )
    baseline_path.write_text(
        json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(metadata, indent=2, sort_keys=True))
    build = metadata.get("full_build")
    if isinstance(build, dict) and build.get("return_code", 0) != 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
