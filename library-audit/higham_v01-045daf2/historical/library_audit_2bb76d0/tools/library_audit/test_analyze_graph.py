#!/usr/bin/env python3

import csv
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
ANALYZER = ROOT / "tools/library_audit/analyze_graph.py"


def write_csv(path: Path, fields: list[str], rows: list[dict[str, object]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


class AnalyzeGraphTest(unittest.TestCase):
    def test_direction_leaves_utilization_and_transitive_counts(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            raw = base / "raw"
            output = base / "metrics"
            raw.mkdir()
            declaration_fields = [
                "name",
                "module",
                "kind",
                "is_internal",
                "is_private",
                "has_body",
                "type_direct_count",
                "body_direct_count",
            ]
            write_csv(
                raw / "declarations.csv",
                declaration_fields,
                [
                    {
                        "name": name,
                        "module": module,
                        "kind": "theorem",
                        "is_internal": "false",
                        "is_private": "false",
                        "has_body": "true",
                        "type_direct_count": 1 if name != "D" else 0,
                        "body_direct_count": 0,
                    }
                    for name, module in [
                        ("A", "NumStability.M1"),
                        ("B", "NumStability.M1"),
                        ("C", "NumStability.M2"),
                        ("D", "NumStability.M3"),
                    ]
                ],
            )
            dependency_fields = [
                "source",
                "source_module",
                "target",
                "target_module",
                "target_scope",
                "occurs_in_type",
                "occurs_in_body",
                "same_module",
            ]
            write_csv(
                raw / "direct_dependencies.csv",
                dependency_fields,
                [
                    {
                        "source": "A",
                        "source_module": "NumStability.M1",
                        "target": "B",
                        "target_module": "NumStability.M1",
                        "target_scope": "project",
                        "occurs_in_type": "true",
                        "occurs_in_body": "false",
                        "same_module": "true",
                    },
                    {
                        "source": "B",
                        "source_module": "NumStability.M1",
                        "target": "C",
                        "target_module": "NumStability.M2",
                        "target_scope": "project",
                        "occurs_in_type": "true",
                        "occurs_in_body": "false",
                        "same_module": "false",
                    },
                ],
            )
            write_csv(
                raw / "module_imports.csv",
                ["source_module", "target_module", "target_scope"],
                [
                    {
                        "source_module": "NumStability.M1",
                        "target_module": "NumStability.M2",
                        "target_scope": "project",
                    },
                    {
                        "source_module": "NumStability.M1",
                        "target_module": "NumStability.M3",
                        "target_scope": "project",
                    },
                ],
            )

            subprocess.run(
                [sys.executable, str(ANALYZER), str(raw), "--output", str(output)],
                cwd=ROOT,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            )
            with (output / "declaration_metrics.csv").open(
                newline="", encoding="utf-8"
            ) as handle:
                metrics = {row["name"]: row for row in csv.DictReader(handle)}
            self.assertEqual(metrics["A"]["transitive_project_dependency_count"], "2")
            self.assertEqual(metrics["B"]["transitive_project_dependency_count"], "1")
            self.assertEqual(metrics["C"]["transitive_project_dependency_count"], "0")
            self.assertEqual(metrics["D"]["transitive_project_dependency_count"], "0")
            self.assertEqual(metrics["A"]["is_apparent_leaf"], "true")
            self.assertEqual(metrics["D"]["is_project_isolated"], "true")
            self.assertEqual(metrics["C"]["is_used_outside_module"], "true")

            summary = json.loads((output / "summary.json").read_text(encoding="utf-8"))
            self.assertEqual(summary["counts"]["apparent_leaves"], 2)
            self.assertEqual(summary["counts"]["isolated_declarations"], 1)
            self.assertEqual(
                summary["connected_component_coverage"][
                    "largest_weak_component_percent"
                ],
                75.0,
            )
            self.assertEqual(
                summary["usage_rates"][
                    "public_declarations_used_outside_their_module_percent"
                ],
                25.0,
            )
            self.assertEqual(
                summary["module_import_vs_declaration_use"][
                    "direct_imports_without_direct_declaration_use"
                ],
                1,
            )


if __name__ == "__main__":
    unittest.main()
