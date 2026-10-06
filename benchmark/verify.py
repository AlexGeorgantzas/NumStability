"""Verify the ten-task private working archive without network access."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
TASKS = (
    "CAST08-FIXED3",
    "P14-T1",
    "HI21-LEM2.2",
    "CAST08-PROP3.1",
    "P14-T2",
    "RUMP12-THM3.4",
    "P14-LOGSUMEXP",
    "H20-8",
    "CAST08-PROP3.2",
    "P14-SHIFTED-SOFTMAX",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def main() -> None:
    expected = set(TASKS)
    actual_packets = {path.stem for path in (ROOT / "tasks").glob("*.json")}
    actual_runs = {path.name for path in (ROOT / "runs").iterdir() if path.is_dir()}
    assert actual_packets == expected, ("task packets", actual_packets ^ expected)
    assert actual_runs == expected, ("run folders", actual_runs ^ expected)

    summary = read_json(ROOT / "results/summary.json")
    ledger = read_json(ROOT / "results/source_task_ledger.json")
    reuse = read_json(ROOT / "results/realized_reuse.json")
    assert summary["scheduled_task_ids"] == list(TASKS)
    assert [row["task_id"] for row in ledger["tasks"]] == list(TASKS)
    assert {row["task_id"] for row in reuse["rows"]} == expected

    for task in TASKS:
        packet = ROOT / "tasks" / f"{task}.json"
        run = ROOT / "runs" / task
        pair = read_json(run / "pair-report.json")
        assert pair["task_id"] == task
        assert pair["source_packet_sha256"] == digest(packet), task
        assert pair["faithfulness_status"] == "BOTH_FAITHFUL", task
        assert pair["proof_pair_status"] == "BOTH_PROVED_FROZEN_STATEMENTS", task
        for role in ("R0", "R1"):
            condition = read_json(run / role / "report.json")
            assert condition["task_id"] == task
            assert (run / role / "workspace/Candidate.lean").is_file()
            for attempt in pair["conditions"][role]["attempts"]:
                submission = run / role / "submissions" / f"{attempt['attempt']:02d}" / "Candidate.lean"
                assert digest(submission) == attempt["candidate"]["sha256"], submission
        print(f"verified {task}")

    print("Verified ten task packets, paired runs, submissions, and summary ledgers.")


if __name__ == "__main__":
    main()
