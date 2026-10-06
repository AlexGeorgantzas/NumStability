#!/usr/bin/env python3
"""Compare seven observable NumStability-use counts with ten paired outcomes.

Only archived accepted candidates, Lean declaration scans, semantic dossiers,
and the frozen task ledger are read. No contestant or auditor is rerun.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.stats import spearmanr


ROOT = Path(__file__).resolve().parent.parent
BENCH = ROOT / "benchmark"
RESULTS = BENCH / "results"
FIGURES = BENCH / "figures"
GENERATED = ROOT / "Documentation" / "generated"
METRICS = (
    ("qualified_distinct", "Distinct qualified source names", "17a_qualified_distinct"),
    ("qualified_occurrences", "Qualified source occurrences", "17b_qualified_occurrences"),
    ("direct_statement", "Direct statement declarations", "17c_direct_statement"),
    ("direct_proof", "Direct proof-term declarations", "17d_direct_proof"),
    ("direct_union", "Distinct direct statement/proof declarations", "17e_direct_union"),
    ("recursive_statement", "Recursive statement dependencies", "17f_recursive_statement"),
    ("recursive_filtered", "Recursive dependencies, filtered", "17g_recursive_filtered"),
)
OUTCOMES = (
    ("total_time_gain_pct", "Total active-time gain (%)"),
    ("proof_line_gain_pct", "Proof-code-line gain (%)"),
    ("total_tokens_gain_pct", "Total net-new-token gain (%)"),
)
PHASES = (
    ("formalization", "direct_statement", "Statement declarations",
     (("formalization_time_gain_pct", "Formalization-time gain (%)"),
      ("formalization_tokens_gain_pct", "Formalization net-new-token gain (%)"),
      ("statement_lines_gain_pct", "Faithful-statement-line gain (%)")),
     "19a_statement_use_formalization"),
    ("proof", "direct_proof", "Proof-term declarations",
     (("proof_time_gain_pct", "Proof-time gain (%)"),
      ("proof_tokens_gain_pct", "Proof net-new-token gain (%)"),
      ("proof_line_gain_pct", "Proof-code-line gain (%)")),
     "19b_proof_use_proving"),
    ("total", "direct_union", "Statement/proof union declarations",
     (("total_time_gain_pct", "Total active-time gain (%)"),
      ("total_tokens_gain_pct", "Total net-new-token gain (%)"),
      ("total_code_lines_gain_pct", "Statement-plus-proof-line gain (%)")),
     "19c_union_use_total"),
)
NAME_RE = re.compile(r"\bNumStability(?:\.[A-Za-z_][A-Za-z_0-9']*)+")
# A limited syntactic filter, not a certified public-API classifier.
GENERATED_NAME_RE = re.compile(
    r"(?:\._proof_[0-9]+|\.match_[0-9]+|\.(?:recOn|casesOn|brecOn|noConfusion|below)(?:\.|$))"
)
INK = "#24547a"
MUTED = "#59636e"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_without_comments_strings_imports(source: str) -> str:
    """Blank Lean comments and strings while retaining newlines/positions."""
    out: list[str] = []
    i, depth, state = 0, 0, "code"
    while i < len(source):
        char = source[i]
        following = source[i:i + 2]
        if state == "code":
            if following == "--":
                state = "line"
                out.extend("  ")
                i += 2
                continue
            if following == "/-":
                state, depth = "block", 1
                out.extend("  ")
                i += 2
                continue
            if char == '"':
                state = "string"
                out.append(" ")
                i += 1
                continue
            out.append(char)
            i += 1
            continue
        if state == "line":
            if char == "\n":
                state = "code"
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if state == "block":
            if following == "/-":
                depth += 1
                out.extend("  ")
                i += 2
                continue
            if following == "-/":
                depth -= 1
                if depth == 0:
                    state = "code"
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if char == "\n" else " ")
            i += 1
            continue
        if char == "\\" and i + 1 < len(source):
            out.extend("  ")
            i += 2
            continue
        if char == '"':
            state = "code"
        out.append("\n" if char == "\n" else " ")
        i += 1
    if state == "block":
        raise ValueError("Unclosed block comment in accepted Lean source")
    cleaned = "".join(out)
    return "\n".join(
        " " * len(line) if re.match(r"^\s*import\b", line) else line
        for line in cleaned.split("\n")
    )


def accepted_l_proof(task_id: str) -> tuple[Path, Path, str]:
    folder = BENCH / "runs" / task_id
    pair = json.loads((folder / "pair-report.json").read_text())
    candidates = [(condition, record) for condition, record in pair["conditions"].items()
                  if record["library_olean_visible"]]
    assert len(candidates) == 1
    condition, record = candidates[0]
    assert record["proof_stage"]["status"] == "PROVED_FROZEN_STATEMENT"
    accepted = []
    for attempt in record["proof_stage"]["attempts"]:
        local = folder / condition / "proof-submissions" / f"{attempt['attempt']:02d}"
        validation = json.loads((local / "validation.json").read_text())
        if validation["pass"]:
            candidate = local / "Candidate.lean"
            manifest = local / "private_semantic_manifest.json"
            assert sha256(candidate) == attempt["candidate"]["sha256"]
            assert sha256(candidate) == validation["candidate"]["sha256"]
            assert sha256(candidate) == json.loads(manifest.read_text())["candidate"]["sha256"]
            accepted.append((candidate, manifest))
    assert len(accepted) == 1, (task_id, len(accepted))
    return *accepted[0], condition


def gain(n: float, l: float) -> float:
    assert n > 0
    return 100 * (n - l) / n


def build_rows() -> list[dict]:
    ledger = json.loads((RESULTS / "source_task_ledger.json").read_text())
    scans = json.loads((RESULTS / "declaration_scan.json").read_text())
    summary = json.loads((RESULTS / "summary.json").read_text())
    tasks = ledger["tasks"]
    assert len(tasks) == len(scans) == 10
    assert [row["task_id"] for row in tasks] == [row["task_id"] for row in scans]
    assert [row["task_id"] for row in tasks] == summary["scheduled_task_ids"]
    rows = []
    for number, (task, scan) in enumerate(zip(tasks, scans), start=1):
        task_id = task["task_id"]
        candidate, semantic, condition = accepted_l_proof(task_id)
        source = source_without_comments_strings_imports(candidate.read_text())
        qualified = [match.group() for match in NAME_RE.finditer(source)]
        manifest = json.loads(semantic.read_text())
        assert manifest["raw_semantic_report"]["target_name"] == "HighamBenchCandidate.target"
        assert manifest["blind_semantic_sha256"] == (
            json.loads((BENCH / "runs" / task_id / "pair-report.json").read_text())
            ["conditions"][condition]["proof_stage"]["accepted_semantic_sha256"]
        )
        recursive = {dep["name"] for dep in manifest["raw_semantic_report"]["dependencies"]
                     if dep["name"].startswith("NumStability.")}
        statement = set(scan["statement_names"])
        proof = set(scan["proof_names"])
        assert statement == set(task["direct_statement_numstability_names"])
        assert proof == set(task["L"]["proof_term_numstability_names"])
        assert statement <= proof  # Supports the report's redundant-union note.
        assert scan["statement_count"] == len(statement)
        assert scan["proof_count"] == len(proof)
        measurements = {
            "qualified_distinct": len(set(qualified)),
            "qualified_occurrences": len(qualified),
            "direct_statement": len(statement),
            "direct_proof": len(proof),
            "direct_union": len(statement | proof),
            "recursive_statement": len(recursive),
            "recursive_filtered": len({name for name in recursive
                                       if not GENERATED_NAME_RE.search(name)}),
        }
        outcomes = {
            "total_time_gain_pct": gain(task["N"]["total_seconds_inclusive"],
                                        task["L"]["total_seconds_inclusive"]),
            "proof_line_gain_pct": gain(task["N"]["proof_code_lines"],
                                        task["L"]["proof_code_lines"]),
            "total_tokens_gain_pct": gain(task["N"]["total_tokens_net_new"],
                                          task["L"]["total_tokens_net_new"]),
        }
        rows.append({"number": number, "task_id": task_id,
                     "accepted_proof_path": str(candidate.relative_to(ROOT)),
                     "accepted_proof_sha256": sha256(candidate),
                     "semantic_manifest_path": str(semantic.relative_to(ROOT)),
                     "semantic_manifest_sha256": sha256(semantic),
                     "measurements": measurements, "gains": outcomes})
    return rows


def rank_stats(rows: list[dict]) -> dict:
    result = {}
    for key, _, _ in METRICS:
        x = [row["measurements"][key] for row in rows]
        result[key] = {}
        for outcome, _ in OUTCOMES:
            y = [row["gains"][outcome] for row in rows]
            estimate = spearmanr(x, y)
            rho = float(estimate.statistic)
            if not math.isfinite(rho):
                raise ValueError(f"Constant metric or outcome: {key}, {outcome}")
            result[key][outcome] = {"spearman_rho": rho, "n": len(rows)}
    return result


def scatter_figure(rows: list[dict], metric: str, title: str, filename: str,
                   statistics: dict) -> None:
    x = np.array([row["measurements"][metric] for row in rows], dtype=float)
    fig, axes = plt.subplots(1, 3, figsize=(12.2, 7.0))
    fig.suptitle(title + " vs. N-to-L gains", x=.50, y=.975, fontsize=15, fontweight="bold")
    for ax, (outcome, label) in zip(axes, OUTCOMES):
        y = np.array([row["gains"][outcome] for row in rows])
        # Display-only offsets distinguish points with identical x and nearby y.
        display = x.copy()
        for value in sorted(set(x)):
            peers = [i for i, v in enumerate(x) if v == value]
            peers.sort(key=lambda i: y[i])
            for i in peers:
                display[i] += .22 * (peers.index(i) - (len(peers) - 1) / 2)
        ax.scatter(display, y, s=165, c=INK, edgecolors="white", linewidths=.8, zorder=3)
        for i, row in enumerate(rows):
            ax.text(display[i], y[i], str(row["number"]), ha="center", va="center",
                    color="white", fontsize=8, fontweight="bold", zorder=4)
        rho = statistics[metric][outcome]["spearman_rho"]
        ax.text(.02, .98, f"Spearman $\\rho$={rho:+.2f}; n=10",
                transform=ax.transAxes, ha="left", va="top", fontsize=9,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.88))
        ax.axhline(0, color=MUTED, linewidth=.85)
        low = min(float(y.min()), 0)
        high = max(float(y.max()), 0)
        pad = max(5, .10 * (high - low))
        ax.set_ylim(low - pad, high + pad)
        ax.set_xlim(min(-1.1, x.min() - 1.1), x.max() + 1.1)
        ax.set_xlabel(title + " (count)", fontsize=9)
        ax.set_ylabel(label, fontsize=9)
        ax.grid(alpha=.18)
        ax.set_axisbelow(True)
    for j, row in enumerate(rows):
        col, line = j // 5, j % 5
        name = row["task_id"].replace("P14-SHIFTED-", "P14-S-")
        fig.text(.09 + .48 * col, .19 - .035 * line,
                 f"{row['number']:>2}. {name}", fontsize=8.5, ha="left")
    fig.text(.50, .008,
             "Positive gain favors L; numbered points match the task key. Horizontal offsets are visual only.",
             fontsize=8, ha="center")
    fig.tight_layout(rect=(0, .23, 1, .94), w_pad=2.0)
    fig.savefig(FIGURES / f"{filename}.pdf", bbox_inches="tight", pad_inches=.10)
    plt.close(fig)


def outcome_pair_figure(rows: list[dict], x_key: str, x_label: str,
                        y_key: str, y_label: str, filename: str) -> None:
    fig, ax = plt.subplots(figsize=(9.0, 5.6))
    x = np.array([row["gains"][x_key] for row in rows])
    y = np.array([row["gains"][y_key] for row in rows])
    ax.scatter(x, y, s=165, c=INK, edgecolors="white", linewidths=.8, zorder=3)
    for i, row in enumerate(rows):
        ax.text(x[i], y[i], str(row["number"]), ha="center", va="center",
                color="white", fontsize=8, fontweight="bold", zorder=4)
    ax.axhline(0, color=MUTED, linewidth=.85)
    ax.axvline(0, color=MUTED, linewidth=.85)
    for values, setter in ((x, ax.set_xlim), (y, ax.set_ylim)):
        low, high = min(float(values.min()), 0), max(float(values.max()), 0)
        pad = max(5, .10 * (high - low))
        setter(low - pad, high + pad)
    ax.set_xlabel(x_label + " gain (%)")
    ax.set_ylabel(y_label + " gain (%)")
    ax.grid(alpha=.18)
    ax.set_axisbelow(True)
    fig.text(.5, .02, "Numbered points use the task key in the metric-count table; positive gains favor L.",
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .05, 1, 1))
    fig.savefig(FIGURES / f"{filename}.pdf", bbox_inches="tight", pad_inches=.10)
    plt.close(fig)


def write_tables(rows: list[dict], statistics: dict) -> None:
    with (GENERATED / "usage_metric_counts.tex").open("w") as output:
        for row in rows:
            counts = [str(row["measurements"][key]) for key, _, _ in METRICS]
            output.write(f"{row['number']} & {row['task_id']} & " + " & ".join(counts) + r" \\" + "\n")
    with (GENERATED / "usage_metric_correlations.tex").open("w") as output:
        for key, label, _ in METRICS:
            numbers = [f"{statistics[key][outcome]['spearman_rho']:+.2f}"
                       for outcome, _ in OUTCOMES]
            output.write(label + " & " + " & ".join(numbers) + r" \\" + "\n")
        output.write("\\bottomrule\n")


def build_phase_rows(rows: list[dict]) -> list[dict]:
    ledger_path = RESULTS / "source_task_ledger.json"
    ledger = json.loads(ledger_path.read_text())
    scans = json.loads((RESULTS / "declaration_scan.json").read_text())
    assert len(rows) == len(ledger["tasks"]) == len(scans) == 10
    phase_rows = []
    for row, task, scan in zip(rows, ledger["tasks"], scans):
        assert row["task_id"] == task["task_id"] == scan["task_id"]
        statement = set(scan["statement_names"])
        proof = set(scan["proof_names"])
        assert len(statement) == row["measurements"]["direct_statement"]
        assert len(proof) == row["measurements"]["direct_proof"]
        assert len(statement | proof) == row["measurements"]["direct_union"]
        n, l = task["N"], task["L"]
        outcomes = {}
        for phase in ("formalization", "proof", "total"):
            for unit in ("seconds_inclusive", "tokens_net_new"):
                key = f"{phase}_{unit}"
                result_key = f"{phase}_{'time' if unit == 'seconds_inclusive' else 'tokens'}_gain_pct"
                outcomes[result_key] = gain(n[key], l[key])
        outcomes["statement_lines_gain_pct"] = gain(n["statement_lines"], l["statement_lines"])
        outcomes["proof_line_gain_pct"] = gain(n["proof_code_lines"], l["proof_code_lines"])
        outcomes["total_code_lines_gain_pct"] = gain(
            n["statement_lines"] + n["proof_code_lines"],
            l["statement_lines"] + l["proof_code_lines"])
        phase_rows.append({
            "number": row["number"], "task_id": row["task_id"],
            "usage": {
                "statement": len(statement),
                "proof_term": len(proof),
                "proof_exclusive": len(proof - statement),
                "union": len(statement | proof),
            },
            "gains": outcomes,
        })
    return phase_rows


def phase_scatter_figure(rows: list[dict], phase: str, use_key: str,
                         x_label: str, outcomes: tuple, filename: str,
                         correlations: dict) -> None:
    x = np.array([row["usage"][{
        "direct_statement": "statement", "direct_proof": "proof_term",
        "direct_union": "union"}[use_key]] for row in rows], dtype=float)
    fig, axes = plt.subplots(1, 3, figsize=(12.2, 7.0))
    fig.suptitle(f"{phase.capitalize()} gains vs. {x_label.lower()}",
                 x=.50, y=.975, fontsize=15, fontweight="bold")
    for ax, (outcome, label) in zip(axes, outcomes):
        y = np.array([row["gains"][outcome] for row in rows])
        display = x.copy()
        for value in sorted(set(x)):
            peers = [i for i, v in enumerate(x) if v == value]
            peers.sort(key=lambda i: y[i])
            for offset, i in enumerate(peers):
                display[i] += .22 * (offset - (len(peers) - 1) / 2)
        ax.scatter(display, y, s=165, c=INK, edgecolors="white", linewidths=.8, zorder=3)
        for i, row in enumerate(rows):
            ax.text(display[i], y[i], str(row["number"]), ha="center", va="center",
                    color="white", fontsize=8, fontweight="bold", zorder=4)
        rho = correlations[phase][outcome]["spearman_rho"]
        ax.text(.02, .98, f"Spearman $\\rho$={rho:+.2f}; n=10",
                transform=ax.transAxes, ha="left", va="top", fontsize=9,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.88))
        ax.axhline(0, color=MUTED, linewidth=.85)
        low, high = min(float(y.min()), 0), max(float(y.max()), 0)
        pad = max(5, .10 * (high - low))
        ax.set_ylim(low - pad, high + pad)
        ax.set_xlim(min(-1.1, x.min() - 1.1), x.max() + 1.1)
        ax.set_xlabel(x_label + " (distinct names)", fontsize=9)
        ax.set_ylabel(label, fontsize=9)
        ax.grid(alpha=.18)
        ax.set_axisbelow(True)
    for j, row in enumerate(rows):
        col, line = j // 5, j % 5
        name = row["task_id"].replace("P14-SHIFTED-", "P14-S-")
        fig.text(.09 + .48 * col, .19 - .035 * line,
                 f"{row['number']:>2}. {name}", fontsize=8.5, ha="left")
    fig.text(.50, .008,
             "Positive gain favors L; numbered points match the task key. Horizontal offsets are visual only.",
             fontsize=8, ha="center")
    fig.tight_layout(rect=(0, .23, 1, .94), w_pad=2.0)
    fig.savefig(FIGURES / f"{filename}.pdf", bbox_inches="tight", pad_inches=.10)
    plt.close(fig)


def write_phase_analysis(rows: list[dict]) -> None:
    correlations = {}
    for phase, use_key, x_label, outcomes, filename in PHASES:
        x = [row["usage"][{
            "direct_statement": "statement", "direct_proof": "proof_term",
            "direct_union": "union"}[use_key]] for row in rows]
        correlations[phase] = {}
        for outcome, _ in outcomes:
            y = [row["gains"][outcome] for row in rows]
            rho = float(spearmanr(x, y).statistic)
            assert math.isfinite(rho)
            correlations[phase][outcome] = {"spearman_rho": rho, "n": len(rows)}
        phase_scatter_figure(rows, phase, use_key, x_label, outcomes, filename, correlations)
    with (GENERATED / "phase_usage_correlations.tex").open("w") as output:
        for phase, _, label, outcomes, _ in PHASES:
            values = [f"{correlations[phase][key]['spearman_rho']:+.2f}" for key, _ in outcomes]
            output.write(f"{phase.capitalize()} / {label} & " + " & ".join(values) + r" \\" + "\n")
        output.write("\\bottomrule\n")
    with (GENERATED / "phase_usage_counts.tex").open("w") as output:
        for row in rows:
            u = row["usage"]
            output.write(f"{row['number']} & {row['task_id']} & {u['statement']} & "
                         f"{u['proof_term']} & {u['proof_exclusive']} & {u['union']} " + r" \\" + "\n")
        output.write("\\bottomrule\n")
    record = {
        "schema_version": "ten-task-phase-aligned-use-1",
        "task_count": len(rows),
        "source_sha256": {name: sha256(path) for name, path in (
            ("source_task_ledger.json", RESULTS / "source_task_ledger.json"),
            ("declaration_scan.json", RESULTS / "declaration_scan.json"),
            ("usage_metric_points.json", RESULTS / "usage_metric_points.json"))},
        "definitions": {
            "statement": "Distinct direct NumStability constants in accepted elaborated target type and statement-local definitions.",
            "proof_term": "Distinct direct NumStability constants in accepted proof term and proof-local helper bodies; names may also occur in the statement.",
            "proof_exclusive": "Proof-term names absent from the statement set; not a complete proof-use measure.",
            "union": "Deduplicated union of direct statement and proof-term names.",
            "recursive_statement_note": "The separately reported recursive semantic dossier roots at the target type and explicitly excludes the target proof.",
            "outcomes": "N-to-L percentage gains by phase, positive favoring L; active times and net-new tokens exclude the one-time scout; statement/proof code-line definitions follow source_task_ledger.json.",
        },
        "rows": rows,
        "spearman": correlations,
    }
    (RESULTS / "phase_usage_points.json").write_text(json.dumps(record, indent=2) + "\n")


def main() -> None:
    FIGURES.mkdir(exist_ok=True)
    GENERATED.mkdir(exist_ok=True)
    rows = build_rows()
    statistics = rank_stats(rows)
    record = {
        "schema_version": "ten-task-observed-use-metric-comparison-1",
        "task_count": 10,
        "source_sha256": {p.name: sha256(p) for p in (
            RESULTS / "source_task_ledger.json", RESULTS / "declaration_scan.json",
            RESULTS / "summary.json")},
        "metric_definitions": {
            "qualified_distinct": "Distinct explicit NumStability.* tokens in the accepted L proof file outside imports, Lean comments, and strings; open-namespace references are missed.",
            "qualified_occurrences": "Occurrences of those same explicit qualified tokens; repeated names count repeatedly.",
            "direct_statement": "Distinct NumStability constants in the elaborated accepted target statement and local statement definitions, from declaration_scan.json.",
            "direct_proof": "Distinct NumStability constants in the accepted proof term and proof-local helper bodies, from declaration_scan.json.",
            "direct_union": "Distinct union of direct_statement and direct_proof names.",
            "recursive_statement": "Distinct NumStability constants in the archived recursive semantic dossier of the accepted theorem statement, including compiler-generated names; not the proof-term closure.",
            "recursive_filtered": "The recursive_statement count after heuristic generated-name pattern removal; not a certified public-API count.",
        },
        "outcome_definition": "100*(N-L)/N, positive favoring L; total active time and net-new tokens exclude the one-time scout; LOC is accepted proof code only.",
        "rows": rows,
        "spearman": statistics,
    }
    for key, title, filename in METRICS:
        scatter_figure(rows, key, title, filename, statistics)
    outcome_pair_figure(rows, "total_time_gain_pct", "Total active time",
                        "total_tokens_gain_pct", "Net-new tokens",
                        "18a_time_token_gain")
    # Proof time is not one of the three requested use-correlation outcomes,
    # but the archive retains it for the original cross-phase diagnostic.
    ledger = json.loads((RESULTS / "source_task_ledger.json").read_text())
    for row, task in zip(rows, ledger["tasks"]):
        row["gains"]["proof_time_gain_pct"] = gain(
            task["N"]["proof_seconds_inclusive"], task["L"]["proof_seconds_inclusive"])
        row["gains"]["formalization_time_gain_pct"] = gain(
            task["N"]["formalization_seconds_inclusive"],
            task["L"]["formalization_seconds_inclusive"])
    outcome_pair_figure(rows, "formalization_time_gain_pct", "Formalization time",
                        "proof_time_gain_pct", "Proof time",
                        "18b_formal_proof_gain")
    write_tables(rows, statistics)
    (RESULTS / "usage_metric_points.json").write_text(json.dumps(record, indent=2) + "\n")
    write_phase_analysis(build_phase_rows(rows))
    print("PASS: seven use metrics plus three phase-aligned views, ten hash-verified accepted L proofs")


if __name__ == "__main__":
    main()
