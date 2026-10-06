#!/usr/bin/env python3
"""Reproduce the selected-tier accepted-proof NumStability usage analysis.

No Lean build or network access is required: this reads the frozen per-attempt
kernel dependency audits and accepted sources already in the repository.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import re
import statistics
from collections import Counter, defaultdict
from pathlib import Path
from xml.sax.saxutils import escape


ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
MANIFEST = ROOT / "paper_bencmark/highambench/metadata/manifest.json"
SEMANTIC_CATALOG = OUT / "semantic_catalog.json"
SOURCES = (
    (ROOT / "paper_bencmark/highambench/reports/live-r11/completed_pairs.csv", {"T1", "T2"}),
    (ROOT / "paper_bencmark/highambench/reports/combined-r09-r10/completed_pairs.csv", {"T3"}),
)
FIELDS = (
    "task_id", "tier", "pair_id", "condition", "source_run", "pass", "proof_sha256",
    "attempt_sha256", "imports", "qualified_occurrences", "qualified_distinct",
    "qualified_live_distinct", "transitive_declarations", "distance1_declarations",
    "distance2_declarations", "library_modules", "candidate_total", "candidate_hits",
    "candidate_distance1_hits", "candidate_score", "time_seconds", "observed_tokens",
    "public_transitive_declarations", "substantial_audit_hits", "substantial_explicit_hits",
    "substantial_score", "final_matches_accepted",
    "physical_loc", "proof_region_loc", "dependency_names", "distance1_names",
    "candidate_names", "hit_names", "substantial_names", "substantial_hit_names",
    "explicit_names", "proof_path", "attempt_path",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_lean_comments_and_strings(source: str) -> str:
    """Mask line comments, nested block comments and string literals."""
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif string:
            if source[i] == "\\" and i + 1 < len(source):
                out.extend("  ")
                i += 2
            elif source[i] == '"':
                string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end < 0:
                out.extend(" " * (len(source) - i))
                break
            out.extend(" " * (end - i))
            i = end
        elif source.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif source[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(out)


def lexical_counts(source: str, audit_names: set[str]) -> dict:
    clean = strip_lean_comments_and_strings(source)
    imports = set(re.findall(r"^\s*import\s+(NumStability(?:\.[A-Za-z0-9_']+)*)", clean, re.M))
    body = "\n".join(line for line in clean.splitlines() if not line.lstrip().startswith("import "))
    refs = re.findall(r"(?<![A-Za-z0-9_'])NumStability(?:\.[A-Za-z0-9_']+)+", body)
    unique = set(refs)
    live = {q for q in unique if any(q == n or n.startswith(q + ".") or q.startswith(n + ".") for n in audit_names)}
    return {"imports": len(imports), "qualified_occurrences": len(refs),
            "qualified_distinct": len(unique), "qualified_live_distinct": len(live),
            "explicit_names": ";".join(sorted(unique))}


def score(dependency_count: int, candidate_hits: int) -> int:
    # Candidate-aware *observed* reuse, not a measure of latent library coverage.
    if dependency_count == 0:
        return 0
    if candidate_hits == 0:
        return 1
    if candidate_hits == 1:
        return 2
    return 3


def is_public(name: str) -> bool:
    return not (name.startswith("_private.") or "._proof_" in name or ".match_" in name)


def read_rows() -> tuple[list[dict], list[dict], dict]:
    manifest = json.loads(MANIFEST.read_text())
    semantic = json.loads(SEMANTIC_CATALOG.read_text())["tasks"]
    targets = {t["task_id"]: t for p in manifest["papers"] for t in p["targets"]}
    attempts: list[dict] = []
    pairs: list[dict] = []
    seen_pairs: set[str] = set()
    for source_csv, tiers in SOURCES:
        with source_csv.open(newline="") as stream:
            for row in csv.DictReader(stream):
                if row["tier"] not in tiers or row["task_id"] == "P16-T3":
                    continue  # Mirrors selected-tier report: P16-T3 target documented false.
                pair_id = row["pair_id"]
                if pair_id in seen_pairs:
                    raise ValueError(f"Duplicate selected pair: {pair_id}")
                seen_pairs.add(pair_id)
                run = Path(row["source_results_root"]).name
                target = targets[row["task_id"]]
                if target["tier"] != row["tier"]:
                    raise ValueError(f"Tier mismatch: {pair_id}")
                candidates = set(target["candidate_library_dependencies_for_audit"])
                substantial = set(semantic.get(row["task_id"], []))
                if row["tier"] in ("T1", "T2") and not substantial:
                    raise ValueError(f"Missing substantial-result classification: {row['task_id']}")
                pair_attempts = {}
                for condition in ("N", "L"):
                    folder = ROOT / "measurements/runs" / run / "pairs" / pair_id / f"condition-{condition}"
                    proof = folder / "accepted_proof.lean"
                    record = folder / "attempt.json"
                    data = json.loads(record.read_text())
                    validation = data["validation"]
                    if not data["pass"] or not validation["pass"] or not validation["library_audit_complete"]:
                        raise ValueError(f"Incomplete/failed accepted attempt: {record}")
                    if data["pair_id"] != pair_id or data["condition"] != condition:
                        raise ValueError(f"Attempt identity mismatch: {record}")
                    if (abs(float(row[f"{condition}_time_seconds"]) - float(data["first_valid_seconds"])) > 1e-5
                            or int(row[f"{condition}_observed_tokens"]) != data["token_usage"]["total_tokens"]
                            or int(row[f"{condition}_physical_loc"]) != data["proof_loc"]["physical_lines"]
                            or int(row[f"{condition}_proof_region_loc"]) != data["proof_loc"]["proof_region_nonblank_non_line_comment_lines"]):
                        raise ValueError(f"Pair summary does not match accepted attempt: {record}")
                    proof_sha = digest(proof)
                    if proof_sha != data["artifacts"]["accepted_proof"]["sha256"]:
                        raise ValueError(f"Accepted-proof hash mismatch: {proof}")
                    declarations = validation["library_declarations"]
                    names = {d["name"] for d in declarations}
                    if bool(names) != validation["library_use"]:
                        raise ValueError(f"Library-use flag mismatch: {record}")
                    if condition == "N" and names:
                        raise ValueError(f"N condition used NumStability: {record}")
                    hit = names & candidates
                    distance1 = {d["name"] for d in declarations if d["distance"] == 1}
                    lexical = lexical_counts(proof.read_text(), names)
                    explicit = set(filter(None, lexical["explicit_names"].split(";")))
                    substantial_audit = names & substantial
                    substantial_explicit = {name for name in substantial_audit if name in explicit}
                    substantial_score = (0 if not names else 3 if len(substantial_explicit) >= 2
                                         else 2 if substantial_audit else 1)
                    final_artifact = data["artifacts"].get("final_candidate")
                    relative_proof = proof.relative_to(ROOT).as_posix()
                    relative_record = record.relative_to(ROOT).as_posix()
                    output = {
                        "task_id": row["task_id"], "tier": row["tier"], "pair_id": pair_id,
                        "condition": condition, "source_run": run, "pass": True,
                        "proof_sha256": proof_sha, "attempt_sha256": digest(record),
                        **lexical,
                        "transitive_declarations": len(names), "distance1_declarations": len(distance1),
                        "public_transitive_declarations": sum(is_public(n) for n in names),
                        "distance2_declarations": sum(d["distance"] == 2 for d in declarations),
                        "library_modules": len({d["module"] for d in declarations}),
                        "candidate_total": len(candidates), "candidate_hits": len(hit),
                        "candidate_distance1_hits": len(hit & distance1),
                        "candidate_score": score(len(names), len(hit)),
                        "substantial_audit_hits": len(substantial_audit),
                        "substantial_explicit_hits": len(substantial_explicit),
                        "substantial_score": substantial_score,
                        "final_matches_accepted": bool(final_artifact and final_artifact["sha256"] == proof_sha),
                        "time_seconds": float(row[f"{condition}_time_seconds"]),
                        "observed_tokens": int(row[f"{condition}_observed_tokens"]),
                        "physical_loc": int(row[f"{condition}_physical_loc"]),
                        "proof_region_loc": int(row[f"{condition}_proof_region_loc"]),
                        "dependency_names": ";".join(sorted(names)),
                        "distance1_names": ";".join(sorted(distance1)),
                        "candidate_names": ";".join(sorted(candidates)),
                        "hit_names": ";".join(sorted(hit)),
                        "substantial_names": ";".join(sorted(substantial)),
                        "substantial_hit_names": ";".join(sorted(substantial_audit)),
                        "proof_path": relative_proof, "attempt_path": relative_record,
                    }
                    attempts.append(output)
                    pair_attempts[condition] = output
                n, l = pair_attempts["N"], pair_attempts["L"]
                pairs.append({"task_id": row["task_id"], "tier": row["tier"], "pair_id": pair_id,
                              "source_run": run, "score": l["candidate_score"],
                              "L_any_use": int(l["transitive_declarations"] > 0),
                              "L_candidate_use": int(l["candidate_hits"] > 0),
                              "L_imports": l["imports"], "L_qualified_distinct": l["qualified_distinct"],
                              "L_qualified_live_distinct": l["qualified_live_distinct"],
                              "L_transitive": l["transitive_declarations"],
                              "L_distance1": l["distance1_declarations"],
                              "L_modules": l["library_modules"],
                              "L_candidates": l["candidate_hits"],
                              "L_direct_candidates": l["candidate_distance1_hits"],
                              "L_public_transitive": l["public_transitive_declarations"],
                              "L_substantial_hits": l["substantial_audit_hits"],
                              "L_substantial_explicit": l["substantial_explicit_hits"],
                              "L_substantial_score": l["substantial_score"],
                              "N_time": n["time_seconds"], "L_time": l["time_seconds"],
                              "N_tokens": n["observed_tokens"], "L_tokens": l["observed_tokens"],
                              "N_loc": n["physical_loc"], "L_loc": l["physical_loc"],
                              "time_gain_pct": 100 * (n["time_seconds"] - l["time_seconds"]) / n["time_seconds"],
                              "token_gain_pct": 100 * (n["observed_tokens"] - l["observed_tokens"]) / n["observed_tokens"],
                              "loc_gain_pct": 100 * (n["physical_loc"] - l["physical_loc"]) / n["physical_loc"]})
    if len(pairs) != 114 or len(attempts) != 228:
        raise ValueError(f"Unexpected selected corpus size: {len(pairs)} pairs, {len(attempts)} attempts")
    return attempts, pairs, targets


def mean(rows: list[dict], key: str) -> float:
    return statistics.mean(float(r[key]) for r in rows)


def ranks(values: list[float]) -> list[float]:
    indexed = sorted(enumerate(values), key=lambda item: item[1])
    result = [0.0] * len(values)
    i = 0
    while i < len(values):
        j = i + 1
        while j < len(values) and indexed[j][1] == indexed[i][1]:
            j += 1
        rank = (i + 1 + j) / 2
        for k in range(i, j):
            result[indexed[k][0]] = rank
        i = j
    return result


def spearman(rows: list[dict], x: str, y: str) -> float | None:
    if len(rows) < 3:
        return None
    a = ranks([float(r[x]) for r in rows])
    b = ranks([float(r[y]) for r in rows])
    ma, mb = statistics.mean(a), statistics.mean(b)
    numerator = sum((u - ma) * (v - mb) for u, v in zip(a, b))
    den = math.sqrt(sum((u - ma) ** 2 for u in a) * sum((v - mb) ** 2 for v in b))
    return numerator / den if den else None


def task_rows(pairs: list[dict]) -> list[dict]:
    grouped = defaultdict(list)
    for p in pairs:
        grouped[p["task_id"]].append(p)
    result = []
    for task in sorted(grouped):
        rows = grouped[task]
        if len(rows) != 3:
            raise ValueError(f"Expected 3 repetitions: {task}")
        result.append({"task_id": task, "tier": rows[0]["tier"], "repetitions": 3,
                       "score_median": statistics.median(r["score"] for r in rows),
                       "scores": "/".join(str(r["score"]) for r in rows),
                       "substantial_score_median": statistics.median(r["L_substantial_score"] for r in rows),
                       "substantial_scores": "/".join(str(r["L_substantial_score"]) for r in rows),
                       "any_use_runs": sum(r["L_any_use"] for r in rows),
                       "candidate_use_runs": sum(r["L_candidate_use"] for r in rows),
                       "substantial_use_runs": sum(r["L_substantial_hits"] > 0 for r in rows),
                       **{f"mean_{key}": mean(rows, key) for key in (
                           "L_imports", "L_qualified_distinct", "L_qualified_live_distinct",
                           "L_transitive", "L_public_transitive", "L_distance1", "L_modules",
                           "L_candidates", "L_direct_candidates", "L_substantial_hits",
                           "L_substantial_explicit", "N_time", "L_time", "N_tokens", "L_tokens",
                           "N_loc", "L_loc")},
                       "time_gain_pct": 100 * (mean(rows, "N_time") - mean(rows, "L_time")) / mean(rows, "N_time"),
                       "token_gain_pct": 100 * (mean(rows, "N_tokens") - mean(rows, "L_tokens")) / mean(rows, "N_tokens"),
                       "loc_gain_pct": 100 * (mean(rows, "N_loc") - mean(rows, "L_loc")) / mean(rows, "N_loc")})
    return result


def write_csv(path: Path, rows: list[dict], fields: list[str] | tuple[str, ...] | None = None) -> None:
    fields = fields or list(rows[0])
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def declaration_rows(attempts: list[dict]) -> list[dict]:
    data = defaultdict(lambda: {"runs": 0, "tasks": set(), "tiers": Counter(), "distance1_runs": 0})
    for row in attempts:
        if row["condition"] != "L":
            continue
        direct = set(filter(None, row["distance1_names"].split(";")))
        for name in filter(None, row["dependency_names"].split(";")):
            cell = data[name]
            cell["runs"] += 1
            cell["tasks"].add(row["task_id"])
            cell["tiers"][row["tier"]] += 1
            cell["distance1_runs"] += name in direct
    return [{"declaration": name, "L_runs": d["runs"], "tasks": len(d["tasks"]),
             "distance1_runs": d["distance1_runs"], "T1_runs": d["tiers"]["T1"],
             "T2_runs": d["tiers"]["T2"], "T3_runs": d["tiers"]["T3"],
             "task_ids": ";".join(sorted(d["tasks"]))} for name, d in sorted(data.items())]


def association_rows(tasks: list[dict]) -> list[dict]:
    predictors = ("score_median", "substantial_score_median", "any_use_runs",
                  "candidate_use_runs", "mean_L_imports", "mean_L_qualified_distinct",
                  "mean_L_qualified_live_distinct", "mean_L_distance1",
                  "mean_L_public_transitive", "mean_L_modules", "mean_L_candidates")
    outcomes = ("time_gain_pct", "token_gain_pct", "loc_gain_pct")
    result = []
    for group in ("All", "T1", "T2", "T3"):
        subset = tasks if group == "All" else [t for t in tasks if t["tier"] == group]
        for predictor in predictors:
            for outcome in outcomes:
                result.append({"group": group, "tasks": len(subset), "predictor": predictor,
                               "outcome": outcome, "spearman_rho": spearman(subset, predictor, outcome)})
    return result


def mixed_task_rows(pairs: list[dict]) -> list[dict]:
    grouped = defaultdict(list)
    for row in pairs:
        grouped[row["task_id"]].append(row)
    result = []
    for task, rows in sorted(grouped.items()):
        used = [r for r in rows if r["L_any_use"]]
        unused = [r for r in rows if not r["L_any_use"]]
        if not used or not unused:
            continue
        result.append({"task_id": task, "tier": rows[0]["tier"],
                       "used_runs": len(used), "unused_runs": len(unused),
                       "used_mean_time_gain_pct": mean(used, "time_gain_pct"),
                       "unused_mean_time_gain_pct": mean(unused, "time_gain_pct"),
                       "used_mean_loc_gain_pct": mean(used, "loc_gain_pct"),
                       "unused_mean_loc_gain_pct": mean(unused, "loc_gain_pct"),
                       "used_mean_token_gain_pct": mean(used, "token_gain_pct"),
                       "unused_mean_token_gain_pct": mean(unused, "token_gain_pct")})
    return result


def svg_bars(tasks: list[dict]) -> str:
    tiers = [(tier, [r for r in tasks if r["tier"] == tier]) for tier in ("T1", "T2", "T3")]
    metrics = [("Any audited use", "any_use_runs"), ("Manifest-candidate use", "candidate_use_runs")]
    lines = ['<svg xmlns="http://www.w3.org/2000/svg" width="900" height="380" viewBox="0 0 900 380">',
             '<rect width="900" height="380" fill="white"/>',
             '<text x="30" y="35" font-family="sans-serif" font-size="20">Observed L-side NumStability use by tier</text>']
    colors = {"T1": "#3366a8", "T2": "#e0803b", "T3": "#50966a"}
    for i, (label, key) in enumerate(metrics):
        y = 85 + i * 145
        lines.append(f'<text x="30" y="{y}" font-family="sans-serif" font-size="15">{escape(label)} (fraction of runs)</text>')
        for j, (tier, rows) in enumerate(tiers):
            val = sum(r[key] for r in rows) / (3 * len(rows))
            x = 35 + j * 285
            lines.append(f'<text x="{x}" y="{y+29}" font-family="sans-serif" font-size="14">{tier}</text>')
            lines.append(f'<rect x="{x}" y="{y+39}" width="{235*val:.1f}" height="28" fill="{colors[tier]}"/>')
            lines.append(f'<rect x="{x}" y="{y+39}" width="235" height="28" fill="none" stroke="#888"/>')
            lines.append(f'<text x="{x}" y="{y+88}" font-family="sans-serif" font-size="13">{100*val:.1f}% ({int(3*len(rows)*val)}/{3*len(rows)})</text>')
    lines.append('</svg>')
    return "\n".join(lines) + "\n"


def svg_scatter(tasks: list[dict], xkey: str, ykey: str, title: str, filename: str) -> None:
    width, height = 930, 570
    vals = [r[ykey] for r in tasks]
    bottom = min(-10, math.floor(min(vals) / 10) * 10)
    top = max(10, math.ceil(max(vals) / 10) * 10)
    x0, y0, plotw, ploth = 80, 80, 780, 400
    colors = {"T1": "#3366a8", "T2": "#e0803b", "T3": "#50966a"}
    lines = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
             f'<rect width="{width}" height="{height}" fill="white"/>',
             f'<text x="30" y="35" font-family="sans-serif" font-size="20">{escape(title)}</text>']
    for tick in range(0, 4):
        x = x0 + tick * plotw / 3
        lines.append(f'<line x1="{x:.1f}" y1="{y0}" x2="{x:.1f}" y2="{y0+ploth}" stroke="#eee"/>')
        lines.append(f'<text x="{x-4:.1f}" y="{y0+ploth+25}" font-family="sans-serif" font-size="13">{tick}</text>')
    for tick in range(5):
        val = bottom + (top - bottom) * tick / 4
        y = y0 + ploth * (1 - tick / 4)
        lines.append(f'<line x1="{x0}" y1="{y:.1f}" x2="{x0+plotw}" y2="{y:.1f}" stroke="#ddd"/>')
        lines.append(f'<text x="{x0-60}" y="{y+5:.1f}" font-family="sans-serif" font-size="12">{val:.0f}%</text>')
    # Deterministic small horizontal offset separates coincident ordinal scores.
    for i, r in enumerate(tasks):
        x = x0 + r[xkey] * plotw / 3 + ((i % 5) - 2) * 5
        y = y0 + ploth * (top - r[ykey]) / (top - bottom)
        lines.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="5" fill="{colors[r["tier"]]}" opacity="0.75"><title>{r["task_id"]}: score {r[xkey]}, gain {r[ykey]:.1f}%</title></circle>')
    xlabel = "Median substantial-result score (0–3)" if xkey == "substantial_score_median" else "Median candidate-aware score (0–3)"
    lines.append(f'<text x="340" y="{height-35}" font-family="sans-serif" font-size="14">{xlabel}</text>')
    lines.append('<text x="700" y="52" font-family="sans-serif" font-size="12" fill="#3366a8">T1</text>')
    lines.append('<text x="750" y="52" font-family="sans-serif" font-size="12" fill="#e0803b">T2</text>')
    lines.append('<text x="800" y="52" font-family="sans-serif" font-size="12" fill="#50966a">T3</text>')
    lines.append('</svg>')
    (OUT / filename).write_text("\n".join(lines) + "\n")


def fmt(x: float, digits: int = 1) -> str:
    return f"{x:+.{digits}f}"


def report(attempts: list[dict], pairs: list[dict], tasks: list[dict], declarations: list[dict]) -> str:
    l = [a for a in attempts if a["condition"] == "L"]
    lines = ["# NumStability use in accepted HighamBench answers", "",
             "This is a reproducible **observational analysis** of the accepted N/L Lean answers used by the repository's selected-tier report. It covers 38 tasks, 114 paired repetitions and 228 validated attempts: r11 for T1/T2, combined r09–r10 for T3, excluding P16-T3 because its target was documented false. No benchmark rerun or new contestant work was performed.", "",
             "## Executive finding", "",
             "The expected tier gradient is present in *observed* L-side use, though not universal. The strongest evidence is the existing Lean dependency audit, not the textual scan:", "",
             "| Tier | Tasks | L runs | Any audited NumStability dependency | ≥1 metadata candidate | ≥1 substantial tier-rationale result | Median distance-1 declarations | Median filtered transitive declarations |",
             "|---|---:|---:|---:|---:|---:|---:|---:|",]
    for tier in ("T1", "T2", "T3"):
        q = [a for a in l if a["tier"] == tier]
        lines.append(f"| {tier} | {len(q)//3} | {len(q)} | {sum(a['transitive_declarations']>0 for a in q)}/{len(q)} | {sum(a['candidate_hits']>0 for a in q)}/{len(q)} | {sum(a['substantial_audit_hits']>0 for a in q)}/{len(q)} | {statistics.median(a['distance1_declarations'] for a in q):g} | {statistics.median(a['public_transitive_declarations'] for a in q):g} |")
    lines += ["", "![Audited library use by tier](tier_usage.svg)", "",
              "T1 has meaningful exceptions, and T3 is not uniformly library-free. In particular, the selected P15-T3 answers use NumStability's matrix/norm lemmas in every repetition. These are results, not exclusions.", "",
              "## Method and definitions", "",
              "- **Inputs:** the two completed-pairs CSVs named above; `metadata/manifest.json` for predeclared task candidates; each accepted `accepted_proof.lean` and `attempt.json`. The script verifies the accepted-proof SHA-256 against its attempt record, all pass flags, the completeness of the hidden Lean dependency audit, the condition and pair identities, and absence of NumStability dependencies in N.",
              "- **Import count:** distinct `import NumStability...` module lines. Imports show availability only, not proof use.",
              "- **Qualified occurrences / distinct names:** lexical `NumStability.*` references outside imports, Lean comments and strings. These can include repeated rewrites, definitions and unused helper code; they are not by themselves a semantic usage measure.",
              "- **Qualified live names:** lexical references matched to some declaration in the accepted theorem's audited dependency closure. This removes some syntactically present but unused references; name-prefix matching remains approximate.",
              "- **Distance-1 declarations:** NumStability declarations directly in the target theorem's dependency graph according to the saved Lean audit. **Transitive declarations** include their downstream library dependencies, so their count is a footprint rather than the number of deliberate theorem applications. **Module count** is the breadth of that closure.",
              "- **Filtered transitive declarations:** the same closure after dropping names matching `_private`, `._proof_` and `.match_`. The CSV field is `public_transitive_declarations`, but this heuristic is **not** a complete public-API classifier. It is still a dependency footprint, not a count of applications.",
              "- **Metadata-candidate hits:** intersection of the audited closure with `candidate_library_dependencies_for_audit` in the repository's task manifest. A hit is task-specific evidence but the lists are not exhaustive; zero does not imply zero helpful use. The `candidate_distance1_hits` column distinguishes near/direct hits from deeper reach. The present repository manifest is hashed in this analysis, but its byte identity with a campaign-time manifest was not established; treat this as a retrospective classification.",
              "- **Candidate-aware usage score (per run):** 0=no audited library dependency; 1=some dependency but no manifest-candidate hit; 2=one candidate hit; 3=two or more candidate hits. The task score is the median of its three runs. It is an ordinal description of observed reuse, not a claim that score 3 exhausts the library or causes a performance gain.",
              "- **Substantial-result score (per run):** a separate [semantic catalog](semantic_catalog.json) names the substantial error/probability results in T1/T2 tier rationales and documented alternatives. Score 0=no audited use; 1=library used but none of these results reached; 2=at least one such result in the accepted theorem closure; 3=two or more *explicitly named in accepted source* and in the closure. T3 has no predesignated substantial result by definition; a T3 score of 1 may still represent useful foundational lemmas. This score therefore partly reflects the task-tier design and must not be used as an independent validation of the tiers.",
              "- **Gain:** `(N − L)/N × 100%`; positive values favor L. Task gains use the arithmetic mean N and L values over the three repetitions. All reported token counts are *observed lower bounds*, not complete token usage, so token gains are descriptive only.", "",
              "## Complementary measurements", "",
              "| Tier | Runs with import | Runs with qualified reference | Median distinct qualified refs | Median distinct imported modules | Median audited modules | Runs with ≥2 candidate hits | Runs with ≥1 substantial result |",
              "|---|---:|---:|---:|---:|---:|---:|---:|",]
    for tier in ("T1", "T2", "T3"):
        q = [a for a in l if a["tier"] == tier]
        lines.append(f"| {tier} | {sum(a['imports']>0 for a in q)}/{len(q)} | {sum(a['qualified_distinct']>0 for a in q)}/{len(q)} | {statistics.median(a['qualified_distinct'] for a in q):g} | {statistics.median(a['imports'] for a in q):g} | {statistics.median(a['library_modules'] for a in q):g} | {sum(a['candidate_hits']>=2 for a in q)}/{len(q)} | {sum(a['substantial_audit_hits']>0 for a in q)}/{len(q)} |")
    lines += ["", "Raw source and semantic dependency measures agree on the presence/absence pattern in this corpus. They do **not** measure the same quantity: transitive closure can be large because one theorem depends on many helpers; an import can be unused.", "",
              "## Per-task results", "",
              "Each task row summarizes three accepted L answers. `Use` and `cand` are repetition counts. `d1` and `all` are mean audited distance-1 and transitive declaration counts; `qref` is the mean count of distinct qualified names in source. Positive gain favors L.", "",
              "| Task | Tier | Candidate score (runs) | Substantial score (runs) | Use | cand | subst | imports | qref | d1 | all | Time gain | Token gain* | LOC gain |",
              "|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",]
    for t in tasks:
        lines.append(f"| {t['task_id']} | {t['tier']} | {t['score_median']:g} ({t['scores']}) | {t['substantial_score_median']:g} ({t['substantial_scores']}) | {t['any_use_runs']}/3 | {t['candidate_use_runs']}/3 | {t['substantial_use_runs']}/3 | {t['mean_L_imports']:.1f} | {t['mean_L_qualified_distinct']:.1f} | {t['mean_L_distance1']:.1f} | {t['mean_L_transitive']:.1f} | {fmt(t['time_gain_pct'])}% | {fmt(t['token_gain_pct'])}% | {fmt(t['loc_gain_pct'])}% |")
    lines += ["", "\\*Observed-token lower-bound comparison, not an exact token saving.", "",
              "## Usage versus efficiency", "",
              "The scatter plots show **all 38 tasks**, without dropping unfavorable outcomes. Each dot is a three-run task mean; color is tier and horizontal position is median candidate-aware score. Scores are not independent of task design, so across-tier correlations are descriptive rather than causal.", "",
              "![Usage score versus physical LOC gain](score_vs_loc.svg)", "",
              "![Usage score versus elapsed-time gain](score_vs_time.svg)", "",
              "![Usage score versus observed-token gain](score_vs_tokens.svg)", "",
              "The second pair of plots uses the stricter substantial-result score. Because it is anchored in tier rationales, it should be read as a robustness/descriptive view, not an independent cross-tier test.", "",
              "![Substantial-result score versus physical LOC gain](substantial_vs_loc.svg)", "",
              "![Substantial-result score versus elapsed-time gain](substantial_vs_time.svg)", "",
              "Grouping task means by candidate-aware score makes the gross pattern visible, but mixes tier and mathematical difficulty:", "",
              "| Median score | Tasks | Mean time gain | Mean LOC gain | L faster | L shorter |",
              "|---:|---:|---:|---:|---:|---:|",]
    for value in (0, 1, 2, 3):
        group = [t for t in tasks if t["score_median"] == value]
        if group:
            lines.append(f"| {value} | {len(group)} | {fmt(mean(group, 'time_gain_pct'))}% | {fmt(mean(group, 'loc_gain_pct'))}% | {sum(t['time_gain_pct']>0 for t in group)}/{len(group)} | {sum(t['loc_gain_pct']>0 for t in group)}/{len(group)} |")
    lines += ["",
              "Spearman correlations (task-level, ties assigned average ranks):", "",
              "| Group | Tasks | Candidate score vs time | Candidate score vs LOC | Candidate score vs tokens* | Substantial score vs time | Substantial score vs LOC | d1 count vs time | d1 count vs LOC |",
              "|---|---:|---:|---:|---:|---:|---:|---:|---:|",]
    for label, q in [("All", tasks)] + [(tier, [t for t in tasks if t["tier"] == tier]) for tier in ("T1", "T2", "T3")]:
        vals = [spearman(q, "score_median", y) for y in ("time_gain_pct", "loc_gain_pct", "token_gain_pct")]
        vals += [spearman(q, "substantial_score_median", y) for y in ("time_gain_pct", "loc_gain_pct")]
        vals += [spearman(q, "mean_L_distance1", y) for y in ("time_gain_pct", "loc_gain_pct")]
        lines.append(f"| {label} | {len(q)} | " + " | ".join("undefined" if v is None else f"{v:+.2f}" for v in vals) + " |")
    lines += ["", "The score is often tied within a tier (and T2 has only three tasks); a within-tier `undefined` correlation means no score variation, not evidence of zero association. The positive across-tier associations do **not** establish an improvement trend within T1 or T3; in particular, the T1 candidate-score correlations with time and LOC are negative in this sample. No p-value or causal inference is claimed. Token correlations are especially fragile because the archived counts are incomplete.", "",
              "### Mixed-use repetitions of the same task", "",
              "Only six tasks have both a library-using and a non-using L repetition. The table compares *paired N/L gains* within those tasks; it controls task identity but not random run variation or the agent's decision to use the library. It is exploratory, not a causal estimate.", "",
              "| Task | Tier | Using runs | Non-using runs | Mean time gain: using / non-using | Mean LOC gain: using / non-using |",
              "|---|---|---:|---:|---:|---:|",]
    for m in mixed_task_rows(pairs):
        lines.append(f"| {m['task_id']} | {m['tier']} | {m['used_runs']} | {m['unused_runs']} | {fmt(m['used_mean_time_gain_pct'])}% / {fmt(m['unused_mean_time_gain_pct'])}% | {fmt(m['used_mean_loc_gain_pct'])}% / {fmt(m['unused_mean_loc_gain_pct'])}% |")
    lines += ["", "The complete values, including observed-token comparisons, are in [mixed_task_usage.csv](mixed_task_usage.csv).", "",
              "## What the accepted code shows", "",
              "The [declaration frequency table](declaration_usage.csv) lists every audited NumStability declaration, its run/task frequency and direct distance-1 frequency. [Attempt-level data](attempt_usage.csv) gives the exact hashes and paths of all 228 accepted proofs and audit records; [pair-level data](pair_usage.csv) joins each N/L pair; [task-level data](task_usage.csv) carries the plotted values. [Association data](associations.csv) tests eleven separate usage measures against time, observed tokens and LOC, both overall and within each tier; undefined values reflect no rank variation. The audit's closure, not an import or a `grep` hit, determines `Use`.", "",]
    for task in ("P01-T1", "P01-T2", "P15-T3", "P17-T1"):
        t = next(q for q in tasks if q["task_id"] == task)
        lines.append(f"- **{task}:** score sequence {t['scores']}; library use {t['any_use_runs']}/3; manifest-candidate use {t['candidate_use_runs']}/3; mean physical-LOC gain {fmt(t['loc_gain_pct'])}%. The exact declaration names are recorded per attempt in `attempt_usage.csv`.")
    mismatches = [a for a in attempts if not a["final_matches_accepted"]]
    lines += ["", f"In {len(mismatches)} of 228 attempts, the recorded final on-disk candidate hash differs from the accepted-proof hash. This report analyzes the **validated accepted proof used for scoring**, not that later terminal candidate. The full later candidate files are not archived here.", "",
              "## Interpretation and limits", "",
              "The analysis supports the narrow descriptive claim that L used NumStability much more often in the T1/T2 selected answers than in T3, and that T2 has more direct/task-listed dependency use than T1 on these runs. It does not prove that the library caused every time or LOC difference. The tiers were defined using anticipated library support, the task sample is selected, T2 has only three tasks, and repeated runs of one task are not independent papers. The metadata-candidate and semantic classifications are retrospective, not an independently validated campaign-time treatment. The dependency closure may count infrastructure declarations carried by a single invoked theorem; lexical use may miss unqualified names. Conversely, a library theorem can be available but not used. Full agent conversations and every draft are absent from this repository, so search time and abandoned routes cannot be reconstructed here. Exact statement/proof-region decomposition of every dependency would require a further Lean elaboration instrument; the saved audit covers the accepted target theorem as a whole.", "",
              "## Reproduction", "",
              "From the repository root, run `python3 paper_bencmark/highambench/reports/library-usage-analysis/analyze.py`. It uses only Python's standard library, writes deterministic CSV/SVG/Markdown outputs beside itself, and fails on missing or non-validated selected attempts or proof-hash mismatches. Source-input digests are in [input_hashes.json](input_hashes.json). No source or measurement record is modified.", ""]
    return "\n".join(lines)


def main() -> None:
    attempts, pairs, _ = read_rows()
    tasks = task_rows(pairs)
    declarations = declaration_rows(attempts)
    write_csv(OUT / "attempt_usage.csv", attempts, FIELDS)
    write_csv(OUT / "pair_usage.csv", pairs)
    write_csv(OUT / "task_usage.csv", tasks)
    write_csv(OUT / "declaration_usage.csv", declarations)
    write_csv(OUT / "associations.csv", association_rows(tasks))
    write_csv(OUT / "mixed_task_usage.csv", mixed_task_rows(pairs))
    (OUT / "tier_usage.svg").write_text(svg_bars(tasks))
    for key, title, file in (("loc_gain_pct", "Candidate-aware library use versus physical-LOC gain", "score_vs_loc.svg"),
                             ("time_gain_pct", "Library use versus elapsed-time gain", "score_vs_time.svg"),
                             ("token_gain_pct", "Library use versus observed-token gain", "score_vs_tokens.svg")):
        svg_scatter(tasks, "score_median", key, title, file)
    svg_scatter(tasks, "substantial_score_median", "loc_gain_pct", "Substantial-result reuse versus physical-LOC gain", "substantial_vs_loc.svg")
    svg_scatter(tasks, "substantial_score_median", "time_gain_pct", "Substantial-result reuse versus elapsed-time gain", "substantial_vs_time.svg")
    (OUT / "report.md").write_text(report(attempts, pairs, tasks, declarations))
    inputs = [MANIFEST, SEMANTIC_CATALOG] + [f for f, _ in SOURCES]
    hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in inputs}
    (OUT / "input_hashes.json").write_text(json.dumps(hashes, indent=2, sort_keys=True) + "\n")
    print(f"Analyzed {len(tasks)} tasks, {len(pairs)} pairs, {len(attempts)} accepted attempts; {len(declarations)} library declarations")


if __name__ == "__main__":
    main()
