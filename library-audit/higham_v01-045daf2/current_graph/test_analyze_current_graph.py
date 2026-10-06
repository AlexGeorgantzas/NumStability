#!/usr/bin/env python3
"""Small known-graph validation for analyze_current_graph.py."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("analyze_current_graph.py")
SPEC = importlib.util.spec_from_file_location("audit_graph", SCRIPT)
assert SPEC and SPEC.loader
audit_graph = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = audit_graph
SPEC.loader.exec_module(audit_graph)


class KnownGraphTests(unittest.TestCase):
    def test_acyclic_counts_components_and_depth(self) -> None:
        # A -> B -> C and A -> C; D -> C; E isolated.
        names = ["A", "B", "C", "D", "E"]
        adjacency = [{1, 2}, {2}, set(), {2}, set()]
        reverse = [set(), {0}, {0, 1, 3}, set(), set()]
        strong_of, strong = audit_graph.strongly_connected_components(
            adjacency, reverse, names
        )
        self.assertEqual(len(strong), 5)
        dag, rev, topo = audit_graph.condensation(adjacency, strong_of, len(strong))
        downstream = audit_graph.reverse_transitive_component_counts(rev, topo, strong)
        dependencies = audit_graph.transitive_component_counts(dag, topo, strong)
        self.assertEqual(downstream[strong_of[2]], 3)
        self.assertEqual(downstream[strong_of[1]], 1)
        self.assertEqual(dependencies[strong_of[0]], 2)
        dependency_depth, downstream_depth, _ = audit_graph.depths(dag, rev, topo)
        self.assertEqual(dependency_depth[strong_of[0]], 2)
        self.assertEqual(downstream_depth[strong_of[2]], 2)
        weak_of, weak = audit_graph.weak_components(
            5,
            ((source, target) for source, targets in enumerate(adjacency) for target in targets),
            set(range(5)),
            names,
        )
        self.assertEqual([len(component) for component in weak], [4, 1])
        self.assertNotEqual(weak_of[0], weak_of[4])

    def test_scc_weighted_reachability(self) -> None:
        # A <-> B -> C, so C has two distinct downstream consumers.
        names = ["A", "B", "C"]
        adjacency = [{1}, {0, 2}, set()]
        reverse = [{1}, {0}, {1}]
        strong_of, strong = audit_graph.strongly_connected_components(
            adjacency, reverse, names
        )
        self.assertEqual(sorted(map(len, strong)), [1, 2])
        dag, rev, topo = audit_graph.condensation(adjacency, strong_of, len(strong))
        downstream = audit_graph.reverse_transitive_component_counts(rev, topo, strong)
        dependencies = audit_graph.transitive_component_counts(dag, topo, strong)
        self.assertEqual(downstream[strong_of[2]], 2)
        self.assertEqual(dependencies[strong_of[0]], 2)

    def test_sibling_cross_edge_does_not_create_false_scc(self) -> None:
        # A -> B, A -> C, B -> C exposed a scheduling bug in a naive iterative DFS.
        names = ["A", "B", "C"]
        adjacency = [{1, 2}, {2}, set()]
        reverse = [set(), {0}, {0, 1}]
        _, strong = audit_graph.strongly_connected_components(adjacency, reverse, names)
        self.assertEqual(len(strong), 3)
        self.assertEqual(sorted(map(len, strong)), [1, 1, 1])

    def test_percentile_contract(self) -> None:
        values = [0, 1, 2, 100]
        self.assertEqual(audit_graph.nearest_rank(values, 0), 0)
        self.assertEqual(audit_graph.nearest_rank(values, 0.5), 1)
        self.assertEqual(audit_graph.nearest_rank(values, 0.9), 100)

    def test_layer_direction(self) -> None:
        self.assertLess(
            audit_graph.LAYER_RANK["Analysis"],
            audit_graph.LAYER_RANK["Algorithms"],
        )
        self.assertTrue(
            audit_graph.LAYER_RANK["Analysis"]
            < audit_graph.LAYER_RANK["Source"]
        )

    def test_range_token_mismatch_is_not_source_written(self) -> None:
        # Mirrors inherited source ranges such as native_decide-generated ax_*:
        # the selected source token is the invocation, not the generated name.
        decl = audit_graph.Decl(
            "NumStability._native.native_decide.ax_1",
            "NumStability.Source.Higham.Chapter01.Generated",
            "axiom",
            True,
            False,
            False,
            0,
            0,
        )
        metadata = audit_graph.Metadata(
            False, False, False, False, False, False, "not_definition", False,
            10, 2, 10, 15,
        )
        self.assertEqual(
            audit_graph.authorship_class(decl, metadata, "native_decide", {}),
            "range_present_token_mismatch_generated_or_unresolved",
        )

    def test_namespace_qualified_source_token_is_exact_match(self) -> None:
        decl = audit_graph.Decl(
            "NumStability.RectLSNormalEquations.isLeastSquaresMinimizer",
            "NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations",
            "theorem",
            False,
            False,
            True,
            1,
            1,
        )
        metadata = audit_graph.Metadata(
            False, False, False, False, False, False, "not_definition", True,
            222, 8, 222, 58,
        )
        self.assertEqual(
            audit_graph.authorship_class(
                decl,
                metadata,
                "RectLSNormalEquations.isLeastSquaresMinimizer",
                {},
            ),
            "confirmed_source_written",
        )


if __name__ == "__main__":
    unittest.main()
