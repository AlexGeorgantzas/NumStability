# Recovered-analyzer validity notice

The exact recovered `analyze_graph.py` was retained and run unchanged for
provenance. During the richer current-schema validation, a sibling-cross-edge
DAG counterexample exposed a defect in its iterative DFS finishing-order
implementation: it marks every sibling as scheduled before descending, which
can emit a consumer before a dependency and can create false strongly
connected components on the transpose pass.

Consequently, **do not use** this directory's:

- `strong_components` summary count;
- `strong_component_id` values;
- `transitive_project_dependency_count` values; or
- any depth/condensation inference derived from those fields.

Its declaration inventory, unique direct-edge counts, incoming/outgoing direct
counts, cross-module counts, weakly connected components, module-pair direct
logical-dependency comparison, apparent leaves, and isolates do not use that
faulty SCC postorder and remain usable as independent cross-checks.

The primary current audit uses `numstability-current-graph/v2`, whose iterator-
stack DFS is validated by a sibling-cross-edge DAG regression as well as the
other known-graph tests. This notice does not alter the recovered files; it
scopes which of their outputs are admissible evidence.
