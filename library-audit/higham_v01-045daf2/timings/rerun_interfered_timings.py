#!/usr/bin/env python3
"""Rerun two rows whose first attempts overlapped an unrelated host scan."""

from __future__ import annotations

import csv
import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
RUNNER_PATH = HERE / "run_fresh_module_timings.py"
spec = importlib.util.spec_from_file_location("timing_runner", RUNNER_PATH)
assert spec and spec.loader
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

RERUN_INDICES = {25, 26}


def main() -> int:
    profiles = runner.load_profiles()
    rows = []
    for index, (module, _stratum, _reason) in enumerate(runner.SAMPLE, 1):
        if index not in RERUN_INDICES:
            continue
        row = runner.run_one(index, module, profiles[module], timeout=900)
        row["rerun_reason"] = (
            "first attempt overlapped conservative 2026-09-03T12:05:30+0300/"
            "2026-09-03T12:06:40+0300 unrelated Python scan window"
        )
        rows.append(row)
        print(f"rerun [{index}] {module}: rc={row['return_code']} wall={row['wall_seconds_observed']}s", flush=True)
    fields = list(rows[0].keys()) if rows else []
    with (HERE / "fresh_module_timing_reruns.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
