"""Recalculate archived token observations using the ten-task net-new rule.

The source CSV records total tokens including cached input. Keep that ledger
unchanged; this module validates each accepted attempt and emits a derived
ledger for the restricted thirty-task report.
"""

from __future__ import annotations

import hashlib
import json
from collections import defaultdict
from pathlib import Path


def apply_net_new_tokens(
    tasks: list[dict], attempts: list[dict], archive: Path, output: Path
) -> dict:
    grouped: dict[tuple[str, str], list[int]] = defaultdict(list)
    entries = []
    for row in attempts:
        path = (archive / row["attempt_path"]).resolve()
        if not path.is_relative_to(archive.resolve()):
            raise ValueError(f"attempt path outside archive: {path}")
        raw = path.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        if digest != row["attempt_sha256"]:
            raise ValueError(f"attempt hash mismatch: {path}")
        usage = json.loads(raw)["token_usage"]
        if usage.get("input_includes_cached") is not True:
            raise ValueError(f"unknown cached-input convention: {path}")
        input_tokens = usage["input_tokens"]
        cached_tokens = usage["cached_input_tokens"]
        output_tokens = usage["output_tokens"]
        if not all(isinstance(v, int) and v >= 0 for v in
                   (input_tokens, cached_tokens, output_tokens)):
            raise ValueError(f"invalid token counts: {path}")
        if cached_tokens > input_tokens or usage["total_tokens"] != input_tokens + output_tokens:
            raise ValueError(f"inconsistent token totals: {path}")
        if usage["total_tokens"] != int(row["observed_tokens"]):
            raise ValueError(f"archived CSV disagrees with attempt: {path}")
        net_new = input_tokens - cached_tokens + output_tokens
        grouped[(row["task_id"], row["condition"])].append(net_new)
        entries.append({
            "task_id": row["task_id"], "pair_id": row["pair_id"],
            "condition": row["condition"], "source_run": row["source_run"],
            "attempt_path": row["attempt_path"], "attempt_sha256": digest,
            "input_tokens": input_tokens, "cached_input_tokens": cached_tokens,
            "output_tokens": output_tokens,
            "observed_total_including_cache": usage["total_tokens"],
            "observed_net_new_tokens": net_new,
        })
    if len(entries) != 180:
        raise ValueError(f"expected 180 accepted attempts, found {len(entries)}")
    for task in tasks:
        n = grouped[(task["task_id"], "N")]
        l = grouped[(task["task_id"], "L")]
        if len(n) != 3 or len(l) != 3:
            raise ValueError(f"task lacks three N/L attempts: {task['task_id']}")
        task["mean_N_tokens"] = sum(n) / 3
        task["mean_L_tokens"] = sum(l) / 3
        task["token_gain_pct"] = 100 * (sum(n) - sum(l)) / sum(n)
    totals = {
        condition: sum(entry["observed_net_new_tokens"] for entry in entries
                       if entry["condition"] == condition)
        for condition in ("N", "L")
    }
    payload = {
        "schema": "historical-net-new-token-ledger-v1",
        "formula": "input_tokens - cached_input_tokens + output_tokens",
        "scope": "180 accepted contestant attempts for the restricted thirty-task report; no scout or audit stages",
        "limitation": "Counts cover observed completed provider responses only; private or interrupted in-flight use is unavailable.",
        "totals": totals,
        "attempts": sorted(entries, key=lambda e: (e["task_id"], e["pair_id"], e["condition"])),
    }
    output.write_text(json.dumps(payload, indent=2) + "\n")
    return payload
