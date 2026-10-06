#!/usr/bin/env python3
"""Summarize the fixed fresh-output timing sample with explicit percentiles."""

from __future__ import annotations

import csv
import json
import re
import statistics
from collections import defaultdict
from pathlib import Path


OUT = Path(__file__).resolve().parent
TIMINGS = OUT / "fresh_module_timings.csv"
RERUNS = OUT / "fresh_module_timing_reruns.csv"
SELECTION = OUT / "timing_sample_predeclared.csv"


def percentile_r7(values: list[float], p: float) -> float:
    """R-7 / NumPy default linear percentile on sorted finite observations."""
    if not values:
        raise ValueError("empty percentile input")
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    h = (len(ordered) - 1) * p
    lo = int(h)
    hi = min(lo + 1, len(ordered) - 1)
    return ordered[lo] + (h - lo) * (ordered[hi] - ordered[lo])


def write_csv(path: Path, rows: list[dict], fields: list[str]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def stats_row(group: str, rows: list[dict]) -> dict:
    values = [float(r["real_seconds"] or r["wall_seconds_observed"]) for r in rows]
    return {
        "group": group,
        "successful_n": len(values),
        "min_seconds": f"{min(values):.6f}",
        "p25_seconds": f"{percentile_r7(values, .25):.6f}",
        "p50_seconds": f"{percentile_r7(values, .50):.6f}",
        "p75_seconds": f"{percentile_r7(values, .75):.6f}",
        "p90_seconds": f"{percentile_r7(values, .90):.6f}",
        "p95_seconds": f"{percentile_r7(values, .95):.6f}",
        "max_seconds": f"{max(values):.6f}",
        "mean_seconds": f"{statistics.fmean(values):.6f}",
        "percentile_definition": "R-7 linear interpolation h=(n-1)p",
        "universe": "successful members of the predeclared 30-module stratified sample",
    }


def main() -> int:
    with SELECTION.open(newline="", encoding="utf-8") as handle:
        selection = {r["module"]: r for r in csv.DictReader(handle)}
    with TIMINGS.open(newline="", encoding="utf-8") as handle:
        original_rows = list(csv.DictReader(handle))
    if len(original_rows) != 30:
        raise SystemExit(f"expected 30 original timing rows, got {len(original_rows)}")
    with RERUNS.open(newline="", encoding="utf-8") as handle:
        rerun_rows = list(csv.DictReader(handle))
    if {int(r["sample_index"]) for r in rerun_rows} != {25, 26}:
        raise SystemExit("expected uncontaminated reruns for sample indices 25 and 26")
    replacement = {r["module"]: r for r in rerun_rows}
    timing_rows = [replacement.get(r["module"], r) for r in original_rows]
    for row in timing_rows:
        if not row.get("max_rss_bytes"):
            stderr_path = OUT.parent / row["stderr_log"]
            stderr = stderr_path.read_text(encoding="utf-8", errors="replace")
            match = re.search(r"^\s*(\d+)\s+maximum resident set size$", stderr, re.MULTILINE)
            if match:
                row["max_rss_bytes"] = match.group(1)
    merged: list[dict] = []
    for row in timing_rows:
        merged.append({**selection[row["module"]], **row, "effective_attempt": "quiet_rerun" if row["module"] in replacement else "original_quiet_attempt"})
    effective_fields: list[str] = []
    for merged_row in merged:
        for field in merged_row:
            if field not in effective_fields:
                effective_fields.append(field)
    write_csv(OUT / "fresh_module_timings_effective.csv", merged, effective_fields)
    successful = [r for r in merged if r["return_code"] == "0" and r["timed_out"] == "false"]

    groups: dict[str, list[dict]] = {"all_predeclared_sample": successful}
    by_layer: dict[str, list[dict]] = defaultdict(list)
    for row in successful:
        by_layer[row["effective_architectural_layer"]].append(row)
    for layer, rows in sorted(by_layer.items()):
        groups[f"effective_layer:{layer}"] = rows
    percentile_rows = [stats_row(name, rows) for name, rows in groups.items() if rows]
    write_csv(
        OUT / "fresh_module_timing_percentiles.csv",
        percentile_rows,
        ["group", "successful_n", "min_seconds", "p25_seconds", "p50_seconds", "p75_seconds", "p90_seconds", "p95_seconds", "max_seconds", "mean_seconds", "percentile_definition", "universe"],
    )

    hotspots: list[dict] = []
    for row in successful:
        seconds = float(row["real_seconds"] or row["wall_seconds_observed"])
        threshold = "priority_gt_40s" if seconds > 40 else "review_gt_20s" if seconds > 20 else "below_review_threshold"
        if threshold != "below_review_threshold":
            hotspots.append({
                "module": row["module"],
                "real_seconds": f"{seconds:.6f}",
                "threshold_class": threshold,
                "effective_architectural_layer": row["effective_architectural_layer"],
                "domain_guess": row["domain_guess"],
                "chapter_guess": row["chapter_guess"],
                "code_bearing_lines": row["code_bearing_lines"],
                "selection_stratum": row["selection_stratum"],
                "selection_reason": row["selection_reason"],
                "interpretation": "Skill threshold flags review priority; it does not imply a split or defect.",
            })
    hotspots.sort(key=lambda r: float(r["real_seconds"]), reverse=True)
    write_csv(
        OUT / "fresh_module_timing_hotspots.csv",
        hotspots,
        ["module", "real_seconds", "threshold_class", "effective_architectural_layer", "domain_guess", "chapter_guess", "code_bearing_lines", "selection_stratum", "selection_reason", "interpretation"],
    )

    ranked = sorted(successful, key=lambda r: float(r["real_seconds"] or r["wall_seconds_observed"]), reverse=True)
    summary = {
        "schema_version": "numstability.fresh-module-timing-summary.v1",
        "predeclared_sample_size": 30,
        "original_attempted": len(original_rows),
        "rerun_attempted": len(rerun_rows),
        "effective_observations": len(timing_rows),
        "successful": len(successful),
        "failed": sum(r["return_code"] != "0" and r["timed_out"] == "false" for r in timing_rows),
        "timed_out": sum(r["timed_out"] == "true" for r in timing_rows),
        "review_threshold_gt_20_seconds_count": sum(float(r["real_seconds"] or r["wall_seconds_observed"]) > 20 for r in successful),
        "priority_threshold_gt_40_seconds_count": sum(float(r["real_seconds"] or r["wall_seconds_observed"]) > 40 for r in successful),
        "slowest_successful_module": ranked[0]["module"] if ranked else None,
        "slowest_real_seconds": float(ranked[0]["real_seconds"] or ranked[0]["wall_seconds_observed"]) if ranked else None,
        "sample_percentiles": stats_row("all_predeclared_sample", successful) if successful else None,
        "measurement_class": "fresh target .olean/.ilean with exact cached imports",
        "limitations": [
            "The 30 modules are a deterministic stratified sample, not all 2,839 source modules.",
            "Percentiles describe only the sampled modules and are not library-wide estimates.",
            "Imported module outputs were cached at the exact audited commit.",
            "Wall-clock results are host- and load-specific and were collected sequentially with no other planned Lean jobs.",
        ],
    }
    (OUT / "timing_summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
