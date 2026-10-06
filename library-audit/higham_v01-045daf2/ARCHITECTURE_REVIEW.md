# Architecture review of NumStability at `higham_v01`

## Audit boundary and graph language

This is a read-only, skill-contract audit-mode architecture review of the
exact presentation-branch commit
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e`, produced from a clean detached
worktree. The intended high-level dependency direction is:

```text
Examples -> Source -> Algorithms -> Analysis -> FloatingPoint
```

Every arrow in a declaration graph or declaration-derived matrix in this
audit has the orientation **consumer to dependency**:

```text
A -> B  means A directly references B in its elaborated type or body/proof.
```

Every arrow in a source- or compiled-import graph likewise goes from importer
to imported module. These two graph families must not be conflated. An
elaborated declaration edge proves formal reference and compositional
typechecking. An import can instead be required for notation, tactics, macros,
attributes, typeclass instances, or re-export. Conversely, a logical
declaration dependency can be available through a transitive import rather
than a direct one.

The main evidence families are:

- the static source snapshot, schema `numstability-static-architecture/1.0.0`,
  in [`static_architecture/`](static_architecture/);
- the recovered compiled graph snapshot, schema 1, in
  [`metrics/recovered_library_audit_schema/`](metrics/recovered_library_audit_schema/);
- the enriched elaborated graph, schema
  `numstability-elaborated-architecture/2.1.0`, in
  [`current_graph/metrics/`](current_graph/metrics/);
- statement-equivalence candidates in
  [`metrics/exact_statement_groups/`](metrics/exact_statement_groups/); and
- the predeclared client experiment in [`probes/`](probes/).

Path-derived layer, domain, and chapter categories are deterministic audit
classifications, not a semantic ontology. Static declaration starters are
source-syntax matches, not an elaborated declaration or authorship count.
Environment-public names are not automatically handwritten API.

### Analyzer validation correction

Validation against the independently acyclic source-import graph exposed a
defect inherited from the recovered July `analyze_graph.py`: its iterative DFS
marked all sibling children before completing any one child. On a DAG with a
cross-edge to a scheduled sibling, this can produce a non-finishing order and
false strongly connected components. The defect affects that analyzer's SCC,
transitive-reachability, and depth outputs, but not raw extraction, direct-edge
counts, incoming counts, cross-boundary counts, or union-find weak components.

The enriched v2 analyzer was corrected to use iterator-stack DFS and gained a
sibling-cross-edge DAG regression test. This report excludes SCC, transitive,
depth, and longest-path figures from the defective recovered run and relies on
the corrected v2 artifacts for those metrics. Phase 10A's cited aggregate
replay did not compute SCC/transitive/depth values and is unaffected. The test
record is [`current_graph/validation_tests.log`](current_graph/validation_tests.log),
and the invalidated-output notice is
[`metrics/recovered_library_audit_schema/INVALID_SCC_TRANSITIVE_NOTICE.md`](metrics/recovered_library_audit_schema/INVALID_SCC_TRANSITIVE_NOTICE.md).

## Executive architecture assessment

The reorganization is visible and substantial. It established a uniform
`Source/Higham/ChapterNN` hierarchy, moved source-labelled and workflow-labelled
paths in the reusable layers to declaration-free compatibility/re-export
surfaces, nearly tripled the number of modules without increasing normalized
source bytes, and retained an acyclic source-import graph. The complete
aggregate reaches every static declaration-bearing owner, while narrow
canonical modules support source-neutral external use in all 15 predeclared
client probes.

The result is not yet a perfectly separated five-layer architecture. Broad
`Analysis` and `Algorithms` aggregates re-export Source material, and 81 of
576 declaration-bearing modules physically under `FloatingPoint`, `Analysis`,
or `Algorithms` have at least one reverse-looking source import. The corrected
elaborated graph confirms that some of these are logical, not merely import
surfaces: 16,049/458,414 unique project declaration pairs (3.5010%) run against
the intended layer direction in the all-environment universe. Under the much
stricter filter requiring both endpoints to be confirmed source-written and
public, 15,306/359,542 pairs (4.2571%) still run against the intended
direction. Most of that filtered count is `Analysis -> Algorithms`, which may
partly reflect foundational or algorithm-adjacent material being physically
owned by Analysis rather than a simple forbidden dependency. Large numbers of
reverse-looking imports from declaration-free files are separately
attributable to migration surfaces and must not be counted as implementation
inversions.

## Actual hierarchy and ownership after reorganization

### Physical source inventory

The ignored-inclusive audit universe is `NumStability.lean` plus every tracked
`NumStability/**/*.lean` file. `rg --files -uu` and the tracked listing agreed
on the 2,838 subtree files; including the root gives 2,839 source modules.

| Physical layer | Modules | Physical lines | Code-bearing lines | Static declaration starters |
| --- | ---: | ---: | ---: | ---: |
| Root | 8 | 422 | 365 | 0 |
| FloatingPoint | 7 | 1,085 | 439 | 47 |
| Analysis | 448 | 405,930 | 249,606 | 9,566 |
| Algorithms | 944 | 608,335 | 173,874 | 7,416 |
| Source | 1,414 | 2,643,659 | 757,981 | 29,613 |
| Upstream compatibility | 5 | 1,406 | 1,092 | 77 |
| Historical `NumStability/Higham/**` | 13 | 109 | 17 | 0 |
| **Total** | **2,839** | **3,660,946** | **1,183,374** | **46,719** |

`code-bearing lines` are lines with non-whitespace remaining after the static
analyzer's comment/string lexical pass. They are not the historical scanner's
nonblank-line metric. The 3,660,946 physical lines include 2,315,180 blank
lines (63.24%); blank and comment-only categories can overlap inside block
comments and must not be summed as a partition.

The exact Phase 10A source parser independently measures 2,839 modules,
3,660,946 lines, 1,345,766 nonblank lines, and 69,455,337 normalized bytes.
Compared under that exact historical parser, module count is up 196.656% while
normalized bytes are down 0.194%. This supports a fine-grained split/ownership
interpretation more strongly than physical LOC alone. See
[`HISTORICAL_COMPARISON.md`](HISTORICAL_COMPARISON.md).

### Uniform Higham source layer

All 28 aggregate modules
`NumStability.Source.Higham.Chapter01` through `Chapter28` exist. Of the 1,414
Source modules, 1,405 (99.36%; numerator 1,405, denominator 1,414) use an exact
`Source.Higham.ChapterNN` path. The nine remaining modules are the
`Source.Higham` root and a coherent `CrossChapter` subtree. No competing
`ChNN` or `HighamChapterNN` spelling remains within the physical Source tree.
The complete chapter inventory is
[`static_architecture/chapter_hierarchy.csv`](static_architecture/chapter_hierarchy.csv).

This is strong evidence that source attribution now has a deliberate and
discoverable location. It does not establish the faithfulness of any wrapper
to Higham; that requires the separate PDF-first audit described by the skill's
source contract.

### Canonical owners versus migration surfaces

The strongest ownership evidence is the absence of matched source declaration
introducers along the old paths:

- 381 chapter/source-labelled paths under physical `Algorithms` and 12 under
  `Analysis` are all static declaration-free: 393/393;
- 113 workflow-token paths under `Algorithms` and five under `Analysis` are
  all static declaration-free. The token-aware set is `Actual`, `Final`,
  `Remaining`, `Whole`, `Bridge`, and `Closure`;
- all 14 historical `NumStability.Higham` root/tree paths are static
  declaration-free. The old root forwards to `NumStability.Source.Higham`.

The 393 modules are listed in
[`static_architecture/canonical_layer_source_label_name_signals.csv`](static_architecture/canonical_layer_source_label_name_signals.csv),
the workflow paths in
[`static_architecture/naming_workflow_signals.csv`](static_architecture/naming_workflow_signals.csv),
and the old Higham paths in
[`static_architecture/legacy_NumStability_Higham_modules.csv`](static_architecture/legacy_NumStability_Higham_modules.csv).

This supports the conservative statement that explicit source ownership was
moved away from hundreds of legacy paths while many import paths were
preserved. Static “declaration-free” means zero matched source introducers; it
does not by itself prove that no generated environment declaration is
attributed to the module, and it does not show whether external users still
need the path.

Across the whole tree, 1,204/2,839 modules (42.41%) have no static declaration
starter. A conservative path/docstring heuristic marks 576/1,204 (47.84%) as
compatibility candidates and a separate heuristic marks 479 as aggregate
entry-point candidates; the categories overlap and are not added. Six files
are empty/no-import reviewed destination modules with explanatory docstrings,
not placeholder definitions. See
[`static_architecture/declaration_free_modules.csv`](static_architecture/declaration_free_modules.csv),
[`static_architecture/compatibility_shim_candidates.csv`](static_architecture/compatibility_shim_candidates.csv),
and
[`static_architecture/empty_no_import_modules.csv`](static_architecture/empty_no_import_modules.csv).

### Naming and remaining ownership heterogeneity

The Source tree consistently uses numbered-source paths. Reusable paths are
substantially more concept-facing, but ownership is not uniform in every
family. The curated public sample places QR and least-squares declarations
under `Algorithms.LinearSystems`, whereas its LU theorem remains in
`Algorithms.LU.GaussianElimination`; other LU content also lives under
`Algorithms.LinearSystems.LU`. Cholesky likewise spans older and newer paths.
Most sampled declarations remain in the relatively flat `NumStability`
namespace despite deep module paths; one is under `FPModel` and one under
`RectLSNormalEquations`. The flat namespace is convenient after `open
NumStability`, but module paths do not reliably predict fully qualified names.
The audited commit's curated `docs/LIBRARY_LOOKUP.md` therefore contributes
materially to discoverability; the independent probes, rather than the
temporary worktree copy of that document, are retained as audit evidence.

## Source-import architecture

### Whole-tree import graph

The exact Phase 10A parser finds 18,818 unique internal source-import pairs,
11,516 external import occurrences, zero unresolved NumStability imports, and
zero cyclic strongly connected components. The static analyzer records the
same 18,818 internal pair count and the same absence of cycles. The external
count differs by ten because the static analyzer uses a stricter lexical
parser; only exact historical-parser figures are used in the historical
comparison.

There is no physical `NumStability/Examples` subtree and no source import of
benchmark or example code. Under the static parser, every external occurrence
targets Mathlib (11,499) or Batteries (7). This is source-level evidence
against accidental Examples/benchmark coupling, not a proof about arbitrary
runtime or build-system dependencies.

### Layer-to-layer source-import matrix

Rows are importing consumers; columns are imported dependencies.

| Consumer layer | Dependency layer | Direct source-import pairs | Intended direction? |
| --- | --- | ---: | --- |
| Algorithms | Algorithms | 2,793 | same layer |
| Algorithms | Analysis | 1,421 | yes |
| Algorithms | FloatingPoint | 139 | yes |
| Algorithms | Source | 1,091 | apparent reverse; mostly import-only migration surfaces |
| Analysis | Analysis | 1,241 | same layer |
| Analysis | FloatingPoint | 41 | yes |
| Analysis | Algorithms | 203 | apparent reverse |
| Analysis | Source | 251 | apparent reverse |
| FloatingPoint | FloatingPoint | 10 | same layer |
| FloatingPoint | Analysis | 11 | apparent reverse |
| Source | Source | 5,683 | same layer |
| Source | Algorithms | 2,991 | yes |
| Source | Analysis | 2,606 | yes |
| Source | FloatingPoint | 283 | yes |

The full matrix, including root, historical compatibility, and upstream
categories, is
[`static_architecture/layer_source_import_matrix.csv`](static_architecture/layer_source_import_matrix.csv).

### Declaration-bearing apparent inversions

Compatibility and implementation cases are reported separately. Among 576
declaration-bearing modules physically in Algorithms, Analysis, or
FloatingPoint, 81 (14.06%) have at least one direct source import against the
intended direction; there are 280 such pairs.

| Importing implementation layer | Imported higher layer | Pairs | Distinct importers | Importer denominator |
| --- | --- | ---: | ---: | ---: |
| Algorithms | Source | 70 | 21 | 325 declaration-bearing Algorithms modules; 21/325 = 6.46% |
| Analysis | Algorithms | 177 | 54 | 246 declaration-bearing Analysis modules |
| Analysis | Source | 22 | 9 | 246 declaration-bearing Analysis modules |
| FloatingPoint | Analysis | 11 | 4 | 5 declaration-bearing FloatingPoint modules; 4/5 = 80.0% |

The two Analysis rows overlap: 56/246 Analysis modules (22.76%) are affected by
one or both. The complete 280-row worklist is
[`static_architecture/implementation_layer_inversion_candidates.csv`](static_architecture/implementation_layer_inversion_candidates.csv).
The focused Algorithms-to-Source set is
[`static_architecture/Algorithms_to_Source_implementation_import_inversions.csv`](static_architecture/Algorithms_to_Source_implementation_import_inversions.csv).

Representative candidates include:

- `Algorithms.LinearSystems.LeastSquares.Equality.Basic`, documented as
  canonical reusable content, importing six Chapter 19/21 Source modules;
- `Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.Executor.Core`,
  importing thirteen Source modules;
- `Analysis.Perturbation.LeastSquares.Basic`, importing fourteen Algorithms
  modules; and
- `FloatingPoint.FusedMultiplyAdd.Core`, importing five Analysis modules,
  several beneath `Analysis.FloatingPointArithmetic`.

These source-import rows are architectural review signals, not conclusions
that every imported module supplies a declaration constant to the importer.
The FloatingPoint case may also signal mislocated foundational arithmetic
content rather than an algorithmic dependency. The following elaborated join
provides the stronger evidence.

### Layer-to-layer elaborated dependency matrix

The table below counts unique ordered project declaration pairs. Rows are
consumer layers and columns are dependency layers; zero means no cell appears
in the raw matrix. Thus `Source -> Algorithms` follows the intended direction,
whereas `Algorithms -> Source` runs against it.

| Consumer → dependency | FloatingPoint | Analysis | Algorithms | Source | Root |
| --- | ---: | ---: | ---: | ---: | ---: |
| FloatingPoint | 343 | **146** | 0 | 0 | 0 |
| Analysis | 4,128 | 68,029 | **13,998** | **791** | 0 |
| Algorithms | 4,508 | 13,507 | 43,703 | **1,114** | 0 |
| Source | 18,562 | 71,085 | 49,424 | 168,575 | 1 |
| Root | 0 | 0 | 0 | 0 | 500 |

Bold cells run against the intended direction. They sum to
16,049/458,414 unique all-environment pairs (3.5010%). The denominator is the
entire project-to-project direct-pair universe. The full rows, including
overlapping `type_pairs`, `body_pairs`, `both_pairs`, and distinct endpoint
counts, are in
[`current_graph/metrics/layer_dependency_matrix.csv`](current_graph/metrics/layer_dependency_matrix.csv).
The A4-oriented vector rendering is
[`figures/layer_dependency_diagram.svg`](figures/layer_dependency_diagram.svg);
its arrows use this same consumer-to-dependency orientation.

| Reverse cell | Unique pairs | Type pairs | Body/proof pairs | Both |
| --- | ---: | ---: | ---: | ---: |
| Algorithms → Source | 1,114 | 511 | 1,004 | 401 |
| Analysis → Algorithms | 13,998 | 11,854 | 12,371 | 10,227 |
| Analysis → Source | 791 | 718 | 783 | 710 |
| FloatingPoint → Analysis | 146 | 106 | 135 | 95 |

Type and body/proof columns overlap; `Both` is their intersection. The
all-environment matrix includes private, internal, reserved, and generated
declarations. A stricter join of
[`current_graph/metrics/direct_project_dependencies.csv.gz`](current_graph/metrics/direct_project_dependencies.csv.gz)
(`source`, `target`, layer and type/body columns) with
[`current_graph/metrics/declaration_origins_and_authorship.csv`](current_graph/metrics/declaration_origins_and_authorship.csv)
(`is_public=true` and `authorship_class=confirmed_source_written` for both
endpoints) yields the following review universe:

| Reverse cell, both endpoints confirmed source-written public | Unique pairs | Distinct consumer declarations | Consumer-layer denominator | Consumer coverage | Consumer modules | Dependency modules |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Algorithms → Source | 972 | 237 | 7,829 | 3.0272% | 20 | 42 |
| Analysis → Algorithms | 13,436 | 1,715 | 9,654 | 17.7647% | 32 | 39 |
| Analysis → Source | 780 | 432 | 9,654 | 4.4748% | 5 | 9 |
| FloatingPoint → Analysis | 118 | 39 | 64 | 60.9375% | 4 | 6 |
| **Total** | **15,306** | not additive | not additive | not additive | not additive | not additive |

The filtered reverse pairs are 15,306/359,542 (4.2571%) of all direct pairs
whose two endpoints are confirmed source-written public declarations. The
consumer percentages instead use the confirmed source-written-public
declaration count of the row's physical layer; rows can share consumers and
must not be added. The classifier is deliberately conservative: a nonreserved
declaration must have a direct Lean selection range whose exact source slice
matches its terminal declaration name (or an exact namespace-qualified
suffix). A matching range is declaration-origin evidence, not proof of human
authorship; macro-produced declarations may inherit ranges.

These results establish real elaborated upward references and replace an
import-only suspicion with formal dependency evidence. They do not show that
every pair is architecturally mistaken. In particular, the large
`Analysis -> Algorithms` cell calls for responsibility-level inspection:
some declarations classed by path as Analysis may formalize the stability of
an algorithm, while some algorithmic primitives may be owned too high. No move
or import deletion follows automatically from these counts.

### Declaration-free reverse imports

Separately, 528 declaration-free canonical-path modules produce 1,124
reverse-looking source-import pairs. Explicit compatibility wording identifies
921/1,124 (81.94%) of them. The remaining 203 require classification as
aggregates, re-exports, or undocumented shims. It would be incorrect to add
these to the 280 implementation candidates and call all 1,404 canonical-path
reverse pairs implementation violations. The raw separation is in
[`static_architecture/import_only_layer_inversion_candidates.csv`](static_architecture/import_only_layer_inversion_candidates.csv).

The static join finds zero direct imports from a declaration-bearing
FloatingPoint/Analysis/Algorithms module to any module carrying the
conservative `compatibility_candidate_static=true` classification, and zero to
the historical `NumStability.Higham` tree. This supports the claim that the
explicit compatibility layer is not upstream of canonical implementations.
It does not eliminate the separately measured dependencies on
declaration-bearing Source modules, nor does it recommend removing
compatibility files;
unknown external importers are outside the compiled project graph. The join
uses `importer_module`/`imported_module` in `source_imports.csv` and physical
layer, declaration-free, and compatibility flags in `modules.csv`.

## Source wrappers and delegation

Of 1,054 declaration-bearing Source modules, 867 (82.26%) directly import at
least one lower layer and 1,015 (96.30%) reach a lower layer transitively.
Thirty-nine (3.70%) have no lower-layer source-import reach. Direct lower-layer
pairs from declaration-bearing Source modules are 2,930 to Algorithms, 2,535
to Analysis, and 277 to FloatingPoint (5,742 total; modules can occur in more
than one category).

This establishes that the source layer is structurally connected to reusable
layers, but it does not establish thin proof delegation. Thin delegation
requires a Source declaration's proof body to contain a canonical declaration,
ideally combined with exact-statement evidence where the wrapper is meant to
preserve the same proposition. The elaborated dependency and representative
chain artifacts provide that stronger evidence case by case; no whole-layer
“wrapper percentage” is inferred from imports.

The declaration graph supplies a stronger whole-layer consumption result. Of
30,289 confirmed source-written public declarations owned by Source, 22,062
(72.8383%) directly reference at least one confirmed source-written public
declaration in Algorithms, Analysis, or FloatingPoint. This join contains
119,339 unique declaration pairs (84,220 type, 102,711 body/proof, 67,592 in
both) and reaches 5,118 distinct lower-layer declarations. By target layer the
pairs are 43,605 to Algorithms, 60,024 to Analysis, and 15,710 to
FloatingPoint. The numerator is distinct Source consumers, not edges; the
denominator is the confirmed source-written-public Source universe. The raw
columns and filters are the same two-artifact join described above.

This establishes broad formal consumption by source-facing results and is
strong evidence that the Source layer is not merely a disconnected catalogue.
It still does not say that 72.8383% are thin aliases: one declaration can use a
lower result as only one ingredient in a substantial independent source proof,
and source faithfulness is outside this architecture measurement.

The static size classifier, defined before use, marks 253 Source modules
“small surface candidates” (at most 100 code-bearing lines and at most five
declaration starters), 471 medium, and 330 substantial (over 500 code-bearing
lines or over 20 starters). These are review strata, not canonical/wrapper
role assignments. Some Source modules can legitimately contain independent
book-specific constructions, counterexamples, or corrected formulations.

The skill's exact-statement priority review sharpens the delegation evidence
without turning equality into a removal rule. Among 1,710 exact elaborated
statement groups (3,533 public theorem/axiom/opaque members), 1,419 groups
contain at least one direct body/proof reference from one member to another;
291 do not. There are 1,480 such same-statement body edges, 829 cross-module
and 651 intra-module. Of these, 771 run from Source to a lower reusable layer
(755 to Algorithms, eight to Analysis, eight to FloatingPoint); four run from
a reusable layer to Source. These are especially strong candidates for
source-wrapper-to-canonical delegation because statement equality and a direct
proof-term reference coincide. They remain candidates: identical propositions
can intentionally have different source, namespace, documentation, or API
roles. The retained review tables are under
[`current_graph/priority_reviews/`](current_graph/priority_reviews/), especially
`same_statement_body_edges.csv`, `canonical_member_review.csv`, and
`exact_statement_groups.csv`.

## Elaboration-level cohesion and module boundaries

The recovered extractor provides the raw snapshot over the environment formed
by importing `NumStability`; the corrected v2 analyzer supplies the enriched
classification and graph metrics. Raw declaration columns are in
[`raw/declarations.csv.gz`](raw/declarations.csv.gz), and raw direct pairs are
in [`raw/direct_dependencies.csv.gz`](raw/direct_dependencies.csv.gz) with
`source`, `target`, owner modules, target scope, overlapping
`occurs_in_type`/`occurs_in_body` flags, and `same_module`.

### Inventory and direct graph

The elaborated universe contains 77,246 project-owned declarations in 1,649
owner modules. It includes 58,120 environment-public declarations under the
current `is_internal=false && is_private=false` filter; 49,573 declarations
meet the conservative confirmed-source-written classifier, of which 47,890
are public. The 27,673 generated-or-authorship-unresolved declarations include
7,691 reserved names. There are 75,557 declarations
with bodies and 1,689 without, 39,157 with docstrings, and no declaration whose
environment metadata marks it unsafe. The raw-kind inventory is 62,152
theorems, 13,405 definitions, 711 constructors, 486 inductives, 486 recursors,
and six axioms; refined mutually exclusive kinds are reported separately in
[`current_graph/metrics/declaration_inventory.csv`](current_graph/metrics/declaration_inventory.csv).

The direct project graph has 458,414 unique ordered pairs: 283,049 type pairs,
406,528 body/proof pairs, and 231,163 occurring in both; 268,231 are
cross-module and 190,183 intra-module. The type/body counts overlap by design.
Other boundary counts are 177,264 cross-layer, 177,642 cross-domain, 4,507
cross-chapter, and 148,458 cross-top-namespace pairs. These are classification
counts over all environment declarations, not source-written-public rates.

### Directional reuse by declaration universe

| Universe and exact filter | Incoming from any project declaration | Used from another owner module | Used from another layer | Used from multiple modules | Used from multiple domains |
| --- | ---: | ---: | ---: | ---: | ---: |
| All project-owned environment declarations | 50,532/77,246 (65.4170%) | 13,549/77,246 (17.5401%) | 6,276/77,246 (8.1247%) | 10,143/77,246 (13.1308%) | 5,520/77,246 (7.1460%) |
| Environment-public (`!internal && !private`) | 39,012/58,120 (67.1232%) | 12,966/58,120 (22.3090%) | 6,103/58,120 (10.5007%) | 9,565/58,120 (16.4573%) | 5,264/58,120 (9.0571%) |
| Confirmed source-written public | 35,889/47,890 (74.9405%) | 12,584/47,890 (26.2769%) | 5,962/47,890 (12.4494%) | 9,260/47,890 (19.3360%) | 5,126/47,890 (10.7037%) |

The formulas count distinct target declarations satisfying the named incoming
condition, never raw edge occurrences. Every denominator is the row's exact
declaration universe. The authoritative numerators, denominators, filters, and
raw-column declaration are in
[`current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv`](current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv),
schema `numstability-coverage-metric-contract/1.0.0`; its
[`summary`](current_graph/metrics/incoming_and_cross_boundary_coverage_contract_summary.json)
records the formula, exact universe and metric filters, materialized and
underlying raw columns, input hashes, and validation of all 27 rows. The older
[`incoming_and_cross_boundary_coverage.csv`](current_graph/metrics/incoming_and_cross_boundary_coverage.csv)
contains the same 27 numerator/denominator measurements but lacks that complete
provenance contract.
The higher rate in the stricter universe is evidence of internal consumption
among declarations confidently tied to source introducers; it is not an API
quality score.

### Components, chains, and corrected depth

| Induced universe | Weak components | Largest component | Coverage |
| --- | ---: | ---: | ---: |
| All project-owned environment declarations | 5,592 | 69,427/77,246 | 89.8778% |
| Environment-public | 348 | 55,915/58,120 | 96.2061% |
| Confirmed source-written, public and nonpublic | 319 | 48,066/49,573 | 96.9600% |
| Confirmed source-written public | 318 | 46,445/47,890 | 96.9827% |

The all, environment-public, and source-written-public rows are universe-
induced weak components from
[`current_graph/metrics/components.csv`](current_graph/metrics/components.csv).
The all-source-written row is the separate exhaustive induced scan in
[`source_written_components_summary.json`](current_graph/metrics/source_written_components_summary.json),
with memberships and size distribution in
[`source_written_component_memberships.csv.gz`](current_graph/metrics/source_written_component_memberships.csv.gz)
and
[`source_written_component_size_distribution.csv`](current_graph/metrics/source_written_component_size_distribution.csv).
Its edge filter retains 368,602 direct pairs whose two endpoints are among the
49,573 confirmed-source-written declarations. The next-largest weak-component
sizes in table order are 266, 143, 158, and 124. Of the component counts,
5,450/5,592 all-universe components, 196/348 public-induced components,
168/319 source-written components, and 164/318
confirmed-source-written-public-induced components are singletons. These
ratios describe the distribution of components, not the fraction of
declarations isolated. Project-graph isolates are instead 5,450/77,246
(7.0554%), 170/58,120 (0.2925%), and 143/47,890 (0.2986%) for the three
original analyzer universes. An induced-public singleton can still connect to
an excluded private or generated declaration, explaining the distinction.

Large-component membership means connectedness after forgetting edge
direction, not consumption or usefulness. Directional chain evidence is
separate: 68,598/77,246 all declarations (88.8046%), 56,246/58,120
environment-public declarations (96.7756%), and 46,811/47,890 confirmed
source-written public declarations (97.7469%) participate in a nontrivial
multi-step chain. Here the numerator is a declaration whose corrected
SCC-condensed dependency or downstream depth is at least two; the raw formula
and denominators are in the coverage CSV.

The corrected declaration graph has 77,245 strongly connected components and
only one nontrivial component, of size two. Its members are the internal,
no-direct-range definitions
`NumStability.evenCoeffsAsc._unsafe_rec` and
`NumStability.oddCoeffsAsc._unsafe_rec`, both owned by
`Source.Higham.Chapter05.Problem03.EvenOddSplitting.Basic`. Despite their names,
the metadata field `is_unsafe` is false; this audit does not classify them as
unsafe. Membership and metadata are in
[`current_graph/metrics/strong_component_memberships.csv.gz`](current_graph/metrics/strong_component_memberships.csv.gz)
and
[`current_graph/metrics/declaration_metrics.csv.gz`](current_graph/metrics/declaration_metrics.csv.gz)
(`strong_component_all`, `strong_component_size`, authorship, and unsafe
columns).

The induced confirmed-source-written graph has 49,573 strong components,
largest size one, and therefore no nontrivial strong component. This does not
contradict the two-node all-environment cycle: both members of that cycle are
internal declarations without direct source ranges and are excluded by the
conservative source-origin filter. The source-written component pass validates
toy weak/strong graphs, exact universe coverage, and agreement with the v2
source-written-public weak distribution; its tool and input hashes are in the
linked summary.

The exact SCC-condensed maximum dependency depth, maximum downstream depth,
and retained longest path are all 65 edges under the corrected iterator-stack
algorithm. Median confirmed-source-written-public dependency depth is seven;
p95 is 34. The deepest retained path is an automatically selected chain of
Chapter 3 IEEE trace results, so its length demonstrates proof-term staging but
is not necessarily the best mathematical exposition. See
[`current_graph/metrics/fan_and_depth_distributions.csv`](current_graph/metrics/fan_and_depth_distributions.csv)
and
[`current_graph/metrics/longest_dependency_path.csv`](current_graph/metrics/longest_dependency_path.csv).

Universe-separated top-100 rankings are retained in
[`reuse_leaders_by_universe.csv`](current_graph/metrics/reuse_leaders_by_universe.csv),
with formulas, filters, tool/input hashes, and validation in
[`reuse_leaders_by_universe_summary.json`](current_graph/metrics/reuse_leaders_by_universe_summary.json).
The table has 3,200 rows: four ranked declaration universes times eight metrics
times 100 ranks. Consumer counts always range over all 77,246 project-owned
environment declarations. `NumStability.FPModel` ranks first under all four
universe filters both for direct fan-in (13,255 distinct direct consumers) and
transitive reach (13,992 declarations in 532 modules, 22 domains, and 23
chapters). `NumStability.BasicOp` reaches the widest layer count (four), while
`NumStability.FloatingPointFormat` has the maximum downstream depth (65).
These rankings are strong internal-consumption evidence, not public-interface
or source-faithfulness judgments. The optional
`reused_low_in_hierarchy_product` is exactly
`transitive_downstream_consumer_count * (1 + downstream_depth_scc_condensation)`;
it is a
ranking heuristic, not a cohesion score, and is not aggregated across the
library.

### Compiled imports versus logical module dependencies

The compiled environment contains 16,512 direct project import pairs and
8,765 cross-module logical module pairs. Of the import pairs, 10,179 have no
direct logical declaration pair. This is a review list, not an import-removal
list: notation, tactics, attributes, macros, and instances are not represented
as declaration constants. Conversely, 2,432 logical module pairs lack a direct
compiled import; 2,411 are available through transitive import closure. The
remaining 21 module pairs comprise 27 declaration pairs classified as lacking
compiled-import reachability; none of those 27 has both endpoints confirmed
source-written. They should be treated as generated/ownership diagnostics,
not claimed as source-level import violations. Exact classifications and
counts are in
[`current_graph/metrics/module_import_vs_logical_dependencies.csv`](current_graph/metrics/module_import_vs_logical_dependencies.csv).

The compiled project-import graph has no nontrivial SCC. The declaration-derived
logical module graph has one two-module SCC:
`NumStability.Algorithms.CondEstimation` and
`NumStability.Source.Higham.Chapter15.Equation06.LAPACKCounterexample.Basic`.
Inspection of the two directions ties it to generated/reserved auxiliaries:
`NumStability.oneNormPowerMethod.eq_def` references a private reserved match
splitter owned by the Source module, while the Source theorem
`NumStability.Higham15.H15_eq15_6_lapackNormEstimator` references the reserved
generated helper `NumStability.argmaxAbs.congr_simp`. No edge in this module
cycle has both endpoints confirmed source-written, so it is not evidence of a
source-written implementation cycle. The module SCC row is in
[`current_graph/metrics/module_graph_components.csv`](current_graph/metrics/module_graph_components.csv);
the supporting declaration pairs are in the enriched direct-edge CSV.
They are also isolated explicitly in
[`current_graph/metrics/logical_module_scc_edge_evidence.csv`](current_graph/metrics/logical_module_scc_edge_evidence.csv).

## Module size, density, and review candidates

Nearest-rank whole-tree static distributions are:

| Metric | p50 | p75 | p90 | p95 | p99 | max |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Physical lines | 106 | 522 | 2,005 | 7,858 | 26,235 | 57,688 |
| Code-bearing lines | 51 | 237 | 689 | 1,261 | 6,160 | 51,482 |
| Static declaration starters | 2 | 11 | 30 | 51 | 238 | 1,832 |
| Direct internal imports | 3 | 7 | 16 | 23 | 58 | 171 |

For the 1,649 declaration-bearing owner modules with nonzero code-bearing
lines, elaborated environment declarations per 100 code-bearing lines have
nearest-rank p25/p50/p75/p95 values 4.3127/7.6923/13.0137/30.2632, with a
maximum of 132.5301. The numerator includes generated declarations, while the
line denominator is the static lexical code-bearing count, so density is a
navigation/inspection signal rather than proof complexity. The per-module raw
columns are `environment_declarations`, `code_bearing_lines`, and
`declarations_per_100_code_lines` in
[`current_graph/metrics/module_metrics.csv`](current_graph/metrics/module_metrics.csv).

Using the skill's source-line review thresholds, 101 modules exceed 10,000
physical lines and 49 exceed 25,000; only 16 and seven, respectively, exceed
those thresholds in code-bearing lines. Eighty-five physical-line candidates
have no more than 10,000 code-bearing lines. For example,
`Source.Higham.Chapter07.Equation26.DistanceToSingularity.Results` has 26,251
physical lines but 37 code-bearing lines and 99.3% blank lines. The largest
substantive module,
`Source.Higham.Chapter11.Section01.Tridiagonal`, has 57,688 physical lines,
51,482 code-bearing lines, and 1,832 static declaration starters. Size signals
review priority; they do not independently justify a split.

No automated count of modules with “unrelated responsibilities” is reported.
The audit's domain label is derived once from each module path, so using it to
prove within-module semantic homogeneity would be circular; flat declaration
names also make namespace diversity an unreliable proxy. The large substantive
modules and the coupling candidates below are therefore inspection worklists,
not claims that their contents are mathematically unrelated. Establishing that
claim requires statement/docstring sampling and an explicit responsibility
classification.

There are 202 modules satisfying the predeclared “many imports, few
declarations” formula: at least 20 direct imports and at most five static
declaration starters. Of these, 156 are declaration-bearing. Several
underdetermined-system endpoints import roughly 79–82 modules for one to five
declarations. They may be legitimate high-level endpoints, but their compile
cost, prerequisite surface, and responsibility deserve targeted review. Raw
rows and formula are in
[`static_architecture/many_imports_few_declarations.csv`](static_architecture/many_imports_few_declarations.csv).

Using logical dependencies rather than declaration count, 85 loaded modules
have at least 20 direct compiled project imports but at most five direct
logical dependency modules; 59 of the 85 own at least one environment
declaration. The formula is evaluated on
`direct_compiled_project_import_count`,
`direct_logical_dependency_module_count`, and `environment_declarations` in
`module_metrics.csv`. The two broad layer aggregates lead the all-module set
with 171 and 143 imports and no owned declarations; among declaration-bearing
modules, several underdetermined-system modules import 58–61 project modules
while having only one to five logical dependency modules. These are prime
review candidates for re-export, elaboration-only, tactic, notation, and
instance requirements. They are not automatic unused-import findings.

For a complementary coupling review, this report defines a candidate as a
declaration-bearing module with at least 500 intra-module declaration pairs
but at most five environment-public declarations directly consumed from
another module. Eleven modules meet that formula; seven have zero such
externally consumed public declarations and four have one to five. The largest
internal counts are 21,862 for
`Source.Higham.Chapter11.Section01.Tridiagonal` (one externally consumed
public declaration), 3,062 for
`Analysis.Perturbation.LeastSquares.Equality.RowwiseBackwardError` (zero),
1,689 for the Chapter 2 exhaustive Binary64 division-round-trip results (two),
1,664 for the Chapter 4 ordering-example core (zero), and 1,239 for
`Analysis.BeneficialRounding` (three). This can indicate a cohesive internal
implementation behind a small consumed surface, or a large endpoint module
whose public results are not internally consumed; it is not automatically a
defect. The formula uses `internal_edge_count` and
`external_api_declarations` in the same module-metrics artifact.

The canonical implementation layers show little evidence of broad `.All`
imports: the static analyzer found two, both six-module Analysis aggregates
used by `Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results`.
Nine of the other `.All` uses in declaration-bearing modules are in Source.
This is a strength, while broad root aggregates remain intentionally wide.

### Fresh-output timing sample

A predeclared 30-module sample was compiled after deleting each target
module's own output while retaining already built imported dependencies. All
30/30 targets succeeded. These are **fresh target-output, cached-dependency**
timings, neither a clean library build nor a library-wide census. Median was
9.265 s, p90 46.484 s, and p95 54.218 s; 6/30 exceeded 20 s and 4/30 exceeded
40 s. The slowest sampled targets were
`Source.Higham.Chapter09.Section11` (56.84 s),
`Source.Higham.Chapter11.Section01.Tridiagonal` (55.95 s), the Chapter 20
Theorem 3 QR-solve module (52.10 s), and `Source.Higham.Chapter19.Core`
(45.86 s). The `NumStability` root target took 28.24 s and
`Analysis.Perturbation.LeastSquares.Basic` 27.23 s.

The overlap between the 55.95 s Tridiagonal hotspot, its 51,482 code-bearing
lines, 1,968 environment declarations, 21,862 internal pairs, and one
externally consumed public declaration makes it the clearest combined
size/coupling/timing review candidate. That does not establish that splitting
it would improve total build time; dependency parallelism and downstream
recompilation require a separate controlled intervention. Definitions,
classification, and raw columns are in
[`TIMINGS_AND_PROOF_HYGIENE.md`](TIMINGS_AND_PROOF_HYGIENE.md) and
[`timings/fresh_module_timings_effective.csv`](timings/fresh_module_timings_effective.csv).

## Public endpoints and re-export layers

Every listed root entry file is static declaration-free. Static import closure
includes the entry module itself.

| Entry point | Direct internal imports | Reached modules | Reached declaration-bearing modules | Reached static declaration starters |
| --- | ---: | ---: | ---: | ---: |
| `NumStability` | 1 | 2,130 | 1,635/1,635 | 46,719/46,719 |
| `NumStability.All` | 4 | 2,129 | 1,635/1,635 | 46,719/46,719 |
| `NumStability.Algorithms` | 171 | 1,774 | 1,474/1,635 | 43,552/46,719 |
| `NumStability.Analysis` | 143 | 728 | 609/1,635 | 25,011/46,719 |
| `NumStability.FloatingPoint` | 4 | 17 | 14/1,635 | 1,302/46,719 |
| `NumStability.Core` | 6 | 17 | 14/1,635 | 818/46,719 |
| `NumStability.Source` | 35 | 1,885 | 1,569/1,635 | 45,326/46,719 |
| `NumStability.Source.Higham` | 63 | 1,884 | 1,569/1,635 | 45,326/46,719 |
| `NumStability.Higham` | 1 | 1,885 | 1,569/1,635 | 45,326/46,719 |

All 710 modules outside the `NumStability.All` closure are static
declaration-free, so the aggregate reaches all 1,635 static
declaration-bearing modules and all 46,719 starters. This demonstrates complete
static ownership coverage, not universal ergonomic convenience.

The complete declaration-level census covers all 479 predeclared entry points
and all three declaration universes. Root results are:

| Entry module | Reachable all project declarations | Reachable environment-public | Reachable confirmed source-written public |
| --- | ---: | ---: | ---: |
| `NumStability` | 77,246/77,246 (100%) | 58,120/58,120 (100%) | 47,890/47,890 (100%) |
| `NumStability.All` | 77,246/77,246 (100%) | 58,120/58,120 (100%) | 47,890/47,890 (100%) |
| `NumStability.Core` | 1,298/77,246 (1.6803%) | 1,007/58,120 (1.7326%) | 849/47,890 (1.7728%) |
| `NumStability.FloatingPoint` | 2,026/77,246 (2.6228%) | 1,653/58,120 (2.8441%) | 1,347/47,890 (2.8127%) |
| `NumStability.Analysis` | 38,224/77,246 (49.4835%) | 29,543/58,120 (50.8310%) | 25,467/47,890 (53.1781%) |
| `NumStability.Algorithms` | 71,703/77,246 (92.8242%) | 54,149/58,120 (93.1676%) | 44,770/47,890 (93.4851%) |
| `NumStability.Source` | 75,072/77,246 (97.1856%) | 56,401/58,120 (97.0423%) | 46,499/47,890 (97.0954%) |
| `NumStability.Source.Higham` | 75,072/77,246 (97.1856%) | 56,401/58,120 (97.0423%) | 46,499/47,890 (97.0954%) |
| `NumStability.Higham` | 75,072/77,246 (97.1856%) | 56,401/58,120 (97.0423%) | 46,499/47,890 (97.0954%) |

For each cell, the numerator is `reachable_declarations`, the denominator is
`universe_declarations`, and the row's universe is explicit in
[`public_entrypoint_exposure_all.csv`](current_graph/metrics/public_entrypoint_exposure_all.csv).
The census contains 1,437 rows: 479 entries times three universes. It uses the
compiled transitive project-import closure for 439 entries. The remaining 40
entries are declaration-free and use a validated static closure; static and
compiled closures agree on all 439 observed entries, and all declaration-
bearing modules in the fallback closures have compiled ownership data. This
supersedes 117 earlier zero rows for unobserved entries in
`public_entrypoint_exposure.csv`; they were a method artifact, not zero
exposure. The method, old-row reproduction, zero observed closure mismatches,
and input/tool hashes are in
[`public_type_exposure_summary.json`](current_graph/metrics/public_type_exposure_summary.json).

These exposure rates show breadth, not ergonomics. They also expose why
`Algorithms` and `Analysis` are not pure domain surfaces: their broad closures
include substantial Source material. A declaration being reachable by an
entry module does not show that its name is discoverable or that a client can
apply it conveniently.

The aggregate roots are not pure layer boundaries. `NumStability.Algorithms`
directly imports 79 Algorithms, 19 Analysis, and 73 Source modules, then
reaches 1,123 Source modules transitively. `NumStability.Analysis` directly
imports 62 Analysis, ten Algorithms, 69 Source, and two FloatingPoint modules.
`Algorithms.Summation` reaches 25 Source modules; the broad least-squares
aggregate reaches 35. An external user wanting a canonical/source-neutral
surface should therefore prefer the narrow owner module.

Useful narrow aggregate entries include `Algorithms.LinearSystems.QR`,
`Algorithms.LinearSystems.LU.BlockLU`, `Algorithms.MatrixEquations`,
`Algorithms.NormEstimation`, `Analysis.MatrixNorms`, and
`FloatingPoint.FusedMultiplyAdd.All`, in addition to every
`Source.Higham.ChapterNN` source aggregate. Their static closure is recorded in
[`static_architecture/entry_points.csv`](static_architecture/entry_points.csv).

## Direct public-consumability evidence

A sample of 15 important source-inspected canonical declarations was frozen
before execution. It spans floating-point models, gamma bounds, summation, dot
products, vector and matrix norms, perturbation, matrix multiplication,
triangular solve, LU, QR, least squares, condition estimation, iterative
refinement, and matrix inversion.

- 15/15 were environment-public and had bodies;
- 15/15 compiled under an independent narrow-module `#check`;
- 15/15 separately compiled fresh-output minimal client theorems;
- all 15 narrow source-import closures contained zero Source modules;
- all 49 direct project type dependencies of the selected declarations were
  environment-public and outside Source and static compatibility modules; and
- 14/15 declaration introducers had a conservatively detected adjacent
  docstring.

This is strong direct evidence that representative canonical APIs are
practically consumable when their narrow owner is known. It is not a
library-wide success percentage, a theorem-discovery test, or evidence that
prerequisite certificates are easy to construct. The public report and all
client sources/logs are in
[`PUBLIC_API_CONSUMABILITY.md`](PUBLIC_API_CONSUMABILITY.md) and
[`probes/`](probes/).

The exhaustive direct-type pass adds a different architecture signal. Its
canonical universe is the 17,547 confirmed-source-written public declarations
whose effective layer is `FloatingPoint`, `Analysis`, or `Algorithms`.
Of these, 605/17,547 (3.4479%) directly expose at least one Source-layer
declaration in their elaborated type, across 1,150 unique direct type edges to
81 distinct Source targets. This is stronger than an import-only observation:
the rows are elaborated declaration dependencies in
[`public_type_exposure_edges.csv`](current_graph/metrics/public_type_exposure_edges.csv)
with `exposure_canonical_to_source=true`. It remains an ownership review set,
not an automatic API defect; intentional source-facing certificates or
misclassified responsibilities may explain individual cases. The complete
scan also found zero direct canonical type edges to static compatibility
candidates or Examples. Counts, the exact universe filter, overlapping review
signals, and validation are in the linked
[`summary`](current_graph/metrics/public_type_exposure_summary.json).

Observed friction includes explicit gamma-validity, dimension, inverse,
triangularity, and nonbreakdown proofs; raw `Fin n -> ...` matrices/vectors;
custom `CVec`, `CMatrix`, `WithLp`, `ENNReal`, and certificate predicates; and
deep module paths coexisting with flatter declaration names. High-level APIs
often consume certificates rather than constructing them. This is
mathematically explicit and compositional, but can make client statements
long.

## Exact-statement groups and ownership review

The recovered fingerprint extractor groups public theorem/axiom/opaque
declarations only after Lean expression equality succeeds; expression hashes
are merely buckets. The current candidate file contains 1,710 equivalence
groups and 3,533 member declarations: 1,636 groups of size two, 36 of size
three, 37 of size four, and one of size five. Of the 1,710 groups, 918 contain
members from more than one owner module. Raw members are in
[`metrics/exact_statement_groups/possible_duplicate_statements.csv`](metrics/exact_statement_groups/possible_duplicate_statements.csv).

The skill-prescribed priority pass retains every group and classifies evidence,
not disposition: 1,382 groups have a unique nonreserved sink in their
same-statement body-reference graph; 33 have an ambiguous forwarding graph;
158 have no same-statement body edge; 132 mix reserved and nonreserved members;
four are reserved-only; and one contains a nonreserved project isolate. The
categories partition all 1,710 groups. Across group members, 5,306 incoming
project edges supply additional consumer evidence. The same pass separates
170 public project isolates into 143 nonreserved and 27 reserved names; 142 of
the nonreserved isolates have the skill's explicit source-text signal. That
regex-backed signal is review evidence, not an authorship proof. Counts and
formulas are recorded in
[`current_graph/priority_reviews/summary.json`](current_graph/priority_reviews/summary.json).

These are review candidates, not 1,710 redundancies. A source-labelled wrapper,
a compatibility alias, two distinct printed Higham labels, or an intentionally
independent proof can share the same proposition. The fingerprint schema also
uses environment visibility rather than explicit authorship and can retain
generated names. Canonical/source/compatibility roles require statement,
proof-body, source, docstring, incoming-user, and PDF review. A direct body edge
between equal-statement members is evidence of proof delegation, not by itself
authorization to remove either name.

## Architectural strengths

1. The Higham source hierarchy is complete and uniformly named across all 28
   chapters.
2. Hundreds of old source-labelled/workflow-labelled reusable paths are now
   declaration-free migration surfaces, separating explicit ownership from
   import compatibility.
3. Exact historical-schema evidence shows much finer module decomposition
   with nearly unchanged normalized source bytes.
4. Both historical and current source scanners find no import cycles.
5. The complete aggregate reaches every static declaration-bearing module.
6. 22,062/30,289 confirmed source-written public Source declarations directly
   consume at least one confirmed source-written public lower-layer result;
   771 exact-statement body edges specifically run Source-to-lower.
7. Canonical implementation modules rarely import broad `.All` umbrellas.
8. Representative narrow canonical APIs compiled in 15/15 independent client
   probes without Source or compatibility names in their immediate type
   surface.
9. The elaborated graph contains substantial direct and cross-module internal
   consumption; this is a connected, compositional body of formal declarations
   rather than merely a set of files that happen to compile independently.

## Residual concerns and review priorities

1. Review the 15,306 direction-opposing pairs with both endpoints confirmed
   source-written public, prioritizing responsibility-level samples from the
   large `Analysis -> Algorithms` cell and the 972 `Algorithms -> Source`
   pairs. A reverse edge is evidence to inspect, not a verdict.
2. Separate legitimate foundational content currently under Analysis from
   true `FloatingPoint -> Analysis` ownership inversions; 39/64 confirmed
   source-written public FloatingPoint declarations directly depend on at
   least one confirmed source-written public Analysis declaration, making path
   ownership especially important.
3. Make broad Algorithms/Analysis aggregates' source-re-export behavior
   explicit in public documentation; narrow owners already offer a cleaner
   path.
4. Review the 203 reverse-looking import-only pairs without explicit
   compatibility wording and document aggregate/shim roles.
5. Review modules with 79–82 imports for one to five declarations using fresh
   target timings and logical dependency counts before drawing performance
   conclusions.
6. Investigate the largest code-bearing modules for coherent responsibility
   boundaries; raw physical size alone is misleading.
7. Complete ownership review for exact-statement groups that cross canonical
   and Source/compatibility modules; preserve book-facing names unless an
   approved canonical replacement and migration policy exist.
8. Improve discoverability where deep module paths and flat declaration names
   diverge, while preserving public names absent explicit migration authority.
9. Provide constructors or helper lemmas for common high-level certificates
   where client probes expose long prerequisite bundles.
10. Investigate the 21 logical module pairs without compiled-import
    reachability and the one generated-auxiliary logical module cycle as
    extractor/ownership diagnostics; neither currently contains a pair with
    both endpoints confirmed source-written.

These are audit findings only. No import removal, move, rename, declaration
consolidation, or source edit is authorized or recommended solely by a metric.

## Interpretation safeguards

- Successful compilation proves acceptance by the recorded Lean environment;
  it does not prove faithfulness to Higham.
- A later declaration referencing an earlier declaration proves formal reuse
  and compositional typechecking, not independent source faithfulness.
- Error propagation through a dependency chain is evidence of integration,
  not a substitute for a source-faithfulness audit.
- Weak connectedness is not reuse.
- An import edge is not necessarily a logical theorem dependency.
- An import with no direct logical pair can still be required for elaboration.
- No incoming project edge does not imply redundancy; it may mark an intended
  external endpoint.
- Generated environment declarations are not handwritten public API.
- Direct and transitive dependencies must be reported separately.
- Exact-statement equality does not prove semantic or API redundancy.
- High fan-in is internal-consumption evidence, not interface-quality proof.
- A successful client probe demonstrates usability only for that probe and
  environment.

## Artifact and recorded-content guide

| Question | Primary artifact and recorded contents |
| --- | --- |
| Files, LOC, density, layer/path classification | [`static_architecture/modules.csv`](static_architecture/modules.csv): `module`, `source_path`, layer fields, line fields, declaration/import counts |
| Source imports and direction | [`static_architecture/source_imports.csv`](static_architecture/source_imports.csv): importer/imported module and layers, source line |
| Layer source-import matrix | [`static_architecture/layer_source_import_matrix.csv`](static_architecture/layer_source_import_matrix.csv): importer/dependency category, pair count |
| Compiled declarations | [`raw/declarations.csv.gz`](raw/declarations.csv.gz): name, owner, kind, visibility, body flag, raw type/body reference counts |
| Direct elaborated dependencies | [`raw/direct_dependencies.csv.gz`](raw/direct_dependencies.csv.gz): source/target, owner modules, target scope, type/body flags, module equality |
| Compiled imports | [`raw/module_imports.csv.gz`](raw/module_imports.csv.gz): consumer module, dependency module, target scope |
| Import versus logical module dependencies | [`current_graph/metrics/module_import_vs_logical_dependencies.csv`](current_graph/metrics/module_import_vs_logical_dependencies.csv): import/logical flags, type/body pairs, transitive availability, classification |
| Enriched module density/coupling | [`current_graph/metrics/module_metrics.csv`](current_graph/metrics/module_metrics.csv): LOC, environment/public/source-written counts, import/logical counts, internal and external API counts |
| Layer/domain/chapter logical matrices | [`current_graph/metrics/layer_dependency_matrix.csv`](current_graph/metrics/layer_dependency_matrix.csv), [`current_graph/metrics/domain_dependency_matrix.csv`](current_graph/metrics/domain_dependency_matrix.csv), [`current_graph/metrics/chapter_dependency_matrix.csv`](current_graph/metrics/chapter_dependency_matrix.csv) |
| Authorship classifications | [`current_graph/metrics/declaration_origins_and_authorship.csv`](current_graph/metrics/declaration_origins_and_authorship.csv): reserved flag, source range/token, conservative class and evidence |
| Denominator-complete incoming/cross-boundary coverage | [`current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv`](current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv): exact universe and metric filters, numerators, denominators, percentages, materialized/raw provenance; [`summary`](current_graph/metrics/incoming_and_cross_boundary_coverage_contract_summary.json) |
| Exact-statement review candidates | [`metrics/exact_statement_groups/possible_duplicate_statements.csv`](metrics/exact_statement_groups/possible_duplicate_statements.csv): group/equivalence id, member, owner and kind |
| Exact-statement delegation/role signals | [`current_graph/priority_reviews/summary.json`](current_graph/priority_reviews/summary.json), [`current_graph/priority_reviews/same_statement_body_edges.csv`](current_graph/priority_reviews/same_statement_body_edges.csv), [`current_graph/priority_reviews/canonical_member_review.csv`](current_graph/priority_reviews/canonical_member_review.csv) |
| WCC, SCC, depth and reuse distributions | [`current_graph/metrics/components.csv`](current_graph/metrics/components.csv), [`current_graph/metrics/declaration_metrics.csv.gz`](current_graph/metrics/declaration_metrics.csv.gz), [`current_graph/metrics/fan_and_depth_distributions.csv`](current_graph/metrics/fan_and_depth_distributions.csv) |
| Full confirmed-source-written components | [`current_graph/metrics/source_written_components_summary.json`](current_graph/metrics/source_written_components_summary.json), [`current_graph/metrics/source_written_component_memberships.csv.gz`](current_graph/metrics/source_written_component_memberships.csv.gz), [`current_graph/metrics/source_written_component_size_distribution.csv`](current_graph/metrics/source_written_component_size_distribution.csv) |
| Reuse leaders by declaration universe | [`current_graph/metrics/reuse_leaders_by_universe.csv`](current_graph/metrics/reuse_leaders_by_universe.csv): universe, rank metric, rank/value, declaration metadata, direct/transitive reach, depths and provenance; [`summary`](current_graph/metrics/reuse_leaders_by_universe_summary.json) |
| Entry-point declaration exposure | [`current_graph/metrics/public_entrypoint_exposure_all.csv`](current_graph/metrics/public_entrypoint_exposure_all.csv): all 479 entries, three declaration universes, closure basis, numerator/denominator and status |
| Public direct-type exposure | [`current_graph/metrics/public_type_exposure_declarations.csv`](current_graph/metrics/public_type_exposure_declarations.csv), [`current_graph/metrics/public_type_exposure_edges.csv`](current_graph/metrics/public_type_exposure_edges.csv), [`current_graph/metrics/environment_public_type_nonpublic_exposure_edges.csv`](current_graph/metrics/environment_public_type_nonpublic_exposure_edges.csv), and [`summary`](current_graph/metrics/public_type_exposure_summary.json) |
| Fresh-output timing sample | [`timings/fresh_module_timings_effective.csv`](timings/fresh_module_timings_effective.csv): `cache_class`, command, status, wall/real/user/sys time, output hashes |
| Public clients and friction | [`probes/results.csv`](probes/results.csv): declaration, import, check/client status, source/doc/type-surface evidence, friction |
| A4 figures and generation metadata | [`figures/README.md`](figures/README.md), [`figures/layer_dependency_diagram.svg`](figures/layer_dependency_diagram.svg), [`figures/domain_dependency_heatmap.svg`](figures/domain_dependency_heatmap.svg) |

The detailed methods, validation, and source-only limitations are in
[`static_architecture/STATIC_ARCHITECTURE.md`](static_architecture/STATIC_ARCHITECTURE.md).
