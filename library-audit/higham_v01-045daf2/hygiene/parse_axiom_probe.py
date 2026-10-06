#!/usr/bin/env python3
"""Parse marker-delimited `#print axioms` output into a reproducible table."""

from __future__ import annotations

import csv
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
AUDIT = HERE.parent
LOG = HERE / "representative_axioms.log"
METADATA = AUDIT / "raw" / "declaration_metadata.csv"

FOUNDATIONAL = {"propext", "Classical.choice", "Quot.sound"}
NATIVE_MARKER = "._native.native_decide.ax_"


def main() -> int:
    text = LOG.read_text(encoding="utf-8")
    with METADATA.open(newline="", encoding="utf-8") as handle:
        by_name = {r["name"]: r for r in csv.DictReader(handle)}
    rows = []
    blocks = text.split("AXIOM_PROBE|")[1:]
    for i, block in enumerate(blocks, 1):
        declaration, _, payload = block.partition("\n")
        match = re.search(r"depends on axioms:\s*\[(.*?)\]", payload, re.DOTALL)
        if not match:
            raise RuntimeError(f"axiom output missing for {declaration}")
        axioms = [x.strip() for x in match.group(1).replace("\n", " ").split(",") if x.strip()]
        foundational = [x for x in axioms if x in FOUNDATIONAL]
        native = [x for x in axioms if NATIVE_MARKER in x]
        other = [x for x in axioms if x not in FOUNDATIONAL and NATIVE_MARKER not in x]
        metadata = by_name[declaration]
        rows.append({
            "sample_index": i,
            "declaration": declaration,
            "module": metadata["module"],
            "selection_start_line": metadata["selection_start_line"],
            "sample_class": "high_level_endpoint" if i <= 6 else "native_decide_parent_theorem",
            "probe_compile_status": "success",
            "axiom_count": len(axioms),
            "axioms": ";".join(axioms),
            "ordinary_lean_mathlib_foundational_axioms": ";".join(foundational),
            "lean_generated_native_decide_axioms": ";".join(native),
            "other_or_unrecognized_axioms": ";".join(other),
            "interpretation": (
                "`#print axioms` reports transitive proof-term assumptions. "
                "Generated native_decide helpers are not source axiom commands."
            ),
        })
    fields = list(rows[0].keys())
    with (HERE / "representative_endpoint_axioms.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
