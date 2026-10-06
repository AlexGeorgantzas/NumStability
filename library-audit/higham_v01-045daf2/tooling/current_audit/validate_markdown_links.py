#!/usr/bin/env python3
"""Validate local links in current-audit Markdown without editing reports."""

from __future__ import annotations

import csv
import json
import re
import sys
from pathlib import Path
from urllib.parse import unquote


AUDIT_ROOT = Path(__file__).resolve().parents[2]
CSV_OUTPUT = AUDIT_ROOT / "provenance" / "MARKDOWN_LINK_VALIDATION.csv"
JSON_OUTPUT = AUDIT_ROOT / "provenance" / "MARKDOWN_LINK_VALIDATION.json"
ARCHIVAL_PREFIXES = (
    Path("_worktree"),
    Path("tooling/phase10a_exact"),
    Path("historical/phase10a_exact"),
    Path("historical/phase10a_validation_21e"),
    Path("historical/recovered_library_audit"),
    Path("historical/library_audit_2bb76d0"),
    Path("historical/later_library_audit_stash"),
)
LINK_RE = re.compile(r"!?\[[^\]]*\]\((<[^>]+>|[^)\s]+)(?:\s+['\"][^)]*['\"])?\)")


def is_archival(path: Path) -> bool:
    relative = path.relative_to(AUDIT_ROOT)
    return any(relative == prefix or prefix in relative.parents for prefix in ARCHIVAL_PREFIXES)


def strip_line_suffix(target: str) -> str:
    # Codex local-file links can use /absolute/path:line.  Preserve ordinary
    # colons in filenames and strip only a final decimal line suffix.
    return re.sub(r":\d+$", "", target)


def main() -> int:
    rows: list[dict[str, object]] = []
    for source in sorted(AUDIT_ROOT.rglob("*.md")):
        if is_archival(source):
            continue
        in_fence = False
        for line_number, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
            if re.match(r"^\s*(```|~~~)", line):
                in_fence = not in_fence
                continue
            if in_fence:
                continue
            for match in LINK_RE.finditer(line):
                raw = match.group(1)
                target = raw[1:-1] if raw.startswith("<") and raw.endswith(">") else raw
                if target.startswith(("http://", "https://", "mailto:", "data:")):
                    continue
                path_part = unquote(target.split("#", 1)[0])
                if not path_part:
                    status = "anchor_only_not_checked"
                    resolved = ""
                else:
                    path_part = strip_line_suffix(path_part)
                    candidate = Path(path_part)
                    resolved_path = candidate if candidate.is_absolute() else source.parent / candidate
                    resolved_path = resolved_path.resolve(strict=False)
                    status = "ok" if resolved_path.exists() else "missing"
                    resolved = str(resolved_path)
                rows.append(
                    {
                        "source": source.relative_to(AUDIT_ROOT).as_posix(),
                        "line": line_number,
                        "target": target,
                        "status": status,
                        "resolved_path": resolved,
                    }
                )
    CSV_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with CSV_OUTPUT.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["source", "line", "target", "status", "resolved_path"])
        writer.writeheader()
        writer.writerows(rows)
    summary = {
        "schema_version": "numstability-markdown-link-validation/v1",
        "scope": "current audit Markdown; recovered archival trees and isolated worktree excluded; fenced code ignored",
        "links_checked": sum(row["status"] != "anchor_only_not_checked" for row in rows),
        "anchor_only_links_not_checked": sum(row["status"] == "anchor_only_not_checked" for row in rows),
        "resolved": sum(row["status"] == "ok" for row in rows),
        "unresolved": sum(row["status"] == "missing" for row in rows),
        "csv": str(CSV_OUTPUT.relative_to(AUDIT_ROOT)),
    }
    JSON_OUTPUT.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, sort_keys=True))
    return 1 if summary["unresolved"] else 0


if __name__ == "__main__":
    sys.exit(main())
