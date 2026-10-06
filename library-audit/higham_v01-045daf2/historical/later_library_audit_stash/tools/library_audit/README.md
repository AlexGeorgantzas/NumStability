# NumStability library audit

These tools measure the existing library without renaming, moving, splitting, or
deleting Lean sources.

## Reproducible workflow

From the repository root:

```bash
python3 tools/library_audit/capture_baseline.py \
  --output tmp/library_audit/<commit>/baseline \
  --run-build

NUMSTABILITY_AUDIT_OUT=tmp/library_audit/<commit>/raw \
  lake env lean tools/library_audit/DeclarationGraph.lean

python3 tools/library_audit/analyze_graph.py \
  tmp/library_audit/<commit>/raw \
  --output tmp/library_audit/<commit>/metrics
```

Measure every module independently with existing imported `.olean` files but a
fresh temporary output artifact:

```bash
python3 tools/library_audit/capture_baseline.py \
  --output tmp/library_audit/<commit>/baseline \
  --time-modules
```

Module timing is sequential and resumable. Each completed module is appended to
`module_compile_times.csv`; rerunning the command skips recorded modules.
Use repeatable `--module NumStability.Path.To.Module` arguments to time a
bounded pilot or refactor wave without recompiling every source.

## Graph semantics

Every declaration edge is directed:

```text
A -> B means the type or body/proof of A directly references B.
```

- An **apparent leaf** has no incoming NumStability declaration edge. Nothing in
  the audited build references it, but it may still be an intentional public
  endpoint.
- A **project-foundational declaration** has no outgoing NumStability edge. It
  may still depend on Lean, Mathlib, Std, Batteries, or another external module.
- A **project-isolated declaration** has neither incoming nor outgoing
  NumStability edges.
- **Module utilization** is the fraction of declarations in a module referenced
  by at least one declaration in a different NumStability module.
- **Connected-component coverage** is undirected reachability after forgetting
  edge direction. It does not establish that every declaration is reused.
- **Transitive project dependency count** is exact reachability in the
  declaration graph after strongly connected components are condensed.

Generated, internal, and private declarations remain in the raw outputs and are
labelled. Summary metrics report public declarations separately.

## Outputs

`DeclarationGraph.lean` creates:

- `declarations.csv`: declaration ownership, kind, visibility, and raw reference
  counts.
- `direct_dependencies.csv`: type/body provenance and target scope for every
  direct reference.
- `module_imports.csv`: direct imports recorded in compiled module metadata.

`analyze_graph.py` creates:

- `summary.json`: aggregate metrics and interpretation limitations.
- `declaration_metrics.csv`: incoming, outgoing, cross-module, component, and
  transitive metrics for every declaration.
- `module_metrics.csv`: module-level utilization and leaf counts.
- `apparent_leaves.csv`: review queue with empty classification fields.
- `module_dependency_comparison.csv`: import-versus-declaration-use comparison.
- `module_declaration_graph.dot` and `module_import_graph.dot`: graph views at
  module granularity.

Prepare a human-review queue without treating public endpoints as dead code:

```bash
python3 tools/library_audit/prepare_leaf_review.py \
  tmp/library_audit/<commit>/metrics/apparent_leaves.csv \
  --duplicates tmp/library_audit/<commit>/review/possible_duplicate_statements.csv \
  --output tmp/library_audit/<commit>/review/leaf_review.csv \
  --summary tmp/library_audit/<commit>/review/leaf_review_by_module.csv
```

On later runs, pass a manually reviewed CSV with `--manual`. Reviewed
classifications are preserved by declaration name. The accepted taxonomy is
`intended_public_endpoint`, `legitimate_final_result`,
`foundational_or_interface_declaration`, `unfinished_or_experimental`,
`generated_or_private_helper`, `possible_duplicate`, `genuinely_unused`, and
`unreviewed`.

Generate exact structural statement-equivalence candidates separately:

```bash
NUMSTABILITY_AUDIT_OUT=tmp/library_audit/<commit>/raw \
  lake env lean tools/library_audit/DeclarationFingerprints.lean

python3 tools/library_audit/find_duplicate_candidates.py \
  tmp/library_audit/<commit>/raw/statement_fingerprints.csv \
  --output tmp/library_audit/<commit>/review/possible_duplicate_statements.csv
```

Lean's expression hash is used only to locate a small comparison bucket. Two
statements receive the same equivalence identifier only after Lean expression
equality succeeds. Even then, the report labels them as candidates: aliases,
source-facing names, and specialized API endpoints may intentionally share the
same proposition.

The direct edge CSV is the lossless declaration graph. Transitive reachability is
computed from it instead of materializing a potentially quadratic edge table.

Compare two snapshots at every refactor-wave gate:

```bash
python3 tools/library_audit/compare_audits.py \
  --before-raw tmp/library_audit/before/raw \
  --before-metrics tmp/library_audit/before/metrics \
  --after-raw tmp/library_audit/after/raw \
  --after-metrics tmp/library_audit/after/metrics \
  --module-prefix NumStability.Path.To.Scope \
  --output tmp/library_audit/after/comparison.json \
  --markdown tmp/library_audit/after/COMPARISON.md
```

The comparison checks public-name preservation and stable public logical edges
separately from module-assignment and import-graph changes. This prevents a
file split from being misreported as newly created semantic reuse.

## Interpretation boundary

The logical declaration graph deliberately does not claim to capture syntax,
macros, tactics, attributes, or other elaboration-only dependencies. A direct
import without a logical declaration edge is therefore a review candidate, not
proof that the import is removable. Likewise, graph similarity can identify
possible duplicates but cannot prove semantic redundancy.
