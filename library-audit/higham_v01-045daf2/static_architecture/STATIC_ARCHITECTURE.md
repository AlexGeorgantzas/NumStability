# NumStability static architecture and public-entry-point audit

## Audit identity and claim boundary

This is a fresh, read-only static-source snapshot of commit
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e` (tree
`be637aeb2c6ca84bcf714b5ef38ea7292a4b50a1`) in a clean detached worktree.
At the metadata check, local `higham_v01` and `origin/higham_v01` both resolved
to the same full commit. The final analyzer run completed at
`2026-09-03T11:29:27+03:00` on macOS 26.5.2, arm64, using Python 3.14.6.

The analyzer schema is `numstability-static-architecture/1.0.0`; its SHA-256
is `dfba978902ba0bbc19453eede1e01c74c7b9a59cc4bcdd96bb4e89198b8d7efe`.
All embedded validation assertions passed. See [provenance.json](provenance.json),
[validation.json](validation.json), and [COMMANDS.md](COMMANDS.md).

The edge orientation in every import table is:

```text
importer / consumer module -> imported module
```

These are **source-import edges**, not elaborated declaration dependencies.
They can reflect declaration availability, notation, tactics, macros,
attributes, or instances. No claim below treats a shared import or import
reachability as proof that one theorem uses another. The elaborated graph must
be consulted for that stronger claim.

## Headline findings

1. **The post-reorganization source hierarchy is concrete and coherent.** All
   28 `NumStability.Source.Higham.ChapterNN` aggregate modules exist. Of 1,414
   physical `Source` modules, 1,405 (99.36%; numerator 1,405, denominator
   1,414) lie under an exact `Chapter01`--`Chapter28` path. The remaining nine
   are the `Source.Higham` root and a coherent `CrossChapter` subtree.

2. **There is strong static evidence that old source-labelled canonical paths
   were retained as import surfaces rather than declaration owners.** The
   analyzer found 393 chapter-labelled paths in the physical `Algorithms`,
   `Analysis`, and `FloatingPoint` layers; all 393 have zero matched source
   declaration introducers. The 14 historical `NumStability.Higham` root/tree
   modules are also all static declaration-free and forward to
   `NumStability.Source.Higham` or canonical/domain modules. This is evidence
   about source ownership and compatibility structure, not a proof that the
   compiled environment attributes zero generated declarations to each file.

3. **The complete-tree entry point covers all static declaration-bearing
   modules.** `NumStability.All` reaches 2,129/2,839 modules (74.99%) when the
   entry itself is included. All 710 modules outside that import closure are
   static declaration-free; consequently it reaches 1,635/1,635 static
   declaration-bearing modules and all 46,719 matched declaration starters.
   This is stronger than mere filename sampling, but it is not an elaborated
   public-name count and does not replace client compilation probes.

4. **The intended layer direction is not fully realized by implementation
   modules.** Among the 576 declaration-bearing modules physically in
   `Algorithms`, `Analysis`, or `FloatingPoint`, 81 (14.06%) have at least one
   direct source import against
   `Examples -> Source -> Algorithms -> Analysis -> FloatingPoint`. There are
   280 such edges. Most reverse-looking edges overall are instead from
   import-only files: 1,124 edges from 528 declaration-free canonical-path
   modules, of which 921 (81.94%) originate in modules detected by explicit
   compatibility wording. The implementation and compatibility cases must not
   be conflated.

5. **Source modules are usually connected by imports to lower reusable
   layers, but import structure alone cannot prove thin proof delegation.** Of
   1,054 declaration-bearing `Source` modules, 867 (82.26%) directly import an
   `Algorithms`, `Analysis`, or `FloatingPoint` module; 1,015 (96.30%) reach a
   lower layer transitively. The remaining 39 (3.70%) have no such source-import
   path. An elaborated body edge is needed before calling any wrapper thin or
   independently implemented.

6. **The source-import graph is acyclic.** Across 18,818 internal import edges
   and 2,839 nodes, there are zero cyclic strongly connected components. This
   supports build-order modularity; it says nothing by itself about theorem
   reuse or proof cohesion.

## Static inventory

The exact universe is `NumStability.lean` plus every tracked `*.lean` file
below `NumStability/`: 2,839 files/modules. Ignored-inclusive discovery with
`rg --files -uu` and the tracked listing agree on the 2,838 files below the
directory. No historical audit measurements were inputs.

`code-bearing lines` means lines containing non-whitespace after the analyzer's
nested-comment and string-content lexical pass. `static declaration starters`
are source lines matching the recorded theorem/lemma/def/etc. introducer
grammar. They do not include generated environment declarations and are not
an authorship verdict.

| Physical layer | Modules | Physical lines | Blank lines | Code-bearing lines | Static declaration starters |
| --- | ---: | ---: | ---: | ---: | ---: |
| Root | 8 | 422 | 16 | 365 | 0 |
| FloatingPoint | 7 | 1,085 | 512 | 439 | 47 |
| Analysis | 448 | 405,930 | 126,101 | 249,606 | 9,566 |
| Algorithms | 944 | 608,335 | 400,560 | 173,874 | 7,416 |
| Source | 1,414 | 2,643,659 | 1,787,803 | 757,981 | 29,613 |
| Upstream | 5 | 1,406 | 162 | 1,092 | 77 |
| Other (`NumStability/Higham/**`) | 13 | 109 | 26 | 17 | 0 |
| **Total** | **2,839** | **3,660,946** | **2,315,180** | **1,183,374** | **46,719** |

Blank-line and comment-only counts are lexical categories and can overlap for
visually blank lines inside a block comment; they should not be summed as a
partition. Blank lines account for 63.24% of physical lines. This makes raw
physical LOC a particularly poor proxy for proof complexity in this snapshot.

Static declaration-starter kinds are: 35,177 theorems, 2,181 lemmas, 8,546
definitions, 232 abbreviations, 365 structures, 80 inductives, and 138
instances. The source grammar found zero `axiom`, `constant`, `opaque`, class,
or `example` starters. These are source-syntax counts; the elaborated inventory
is authoritative for actual environment kinds and generated declarations.

### Module-size distribution

Nearest-rank module percentiles are recorded in `summary.json`:

| Metric | p50 | p75 | p90 | p95 | p99 | max |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Physical lines | 106 | 522 | 2,005 | 7,858 | 26,235 | 57,688 |
| Code-bearing lines | 51 | 237 | 689 | 1,261 | 6,160 | 51,482 |
| Static declaration starters | 2 | 11 | 30 | 51 | 238 | 1,832 |
| Direct internal imports | 3 | 7 | 16 | 23 | 58 | 171 |

Under the skill contract's physical-line thresholds, 101 modules exceed
10,000 lines and 49 exceed 25,000. Only 16 exceed 10,000 code-bearing lines and
seven exceed 25,000 code-bearing lines. Eighty-five physical-line review
candidates fall below 10,001 code-bearing lines, largely because of extreme
vertical whitespace. For example,
`Source.Higham.Chapter07.Equation26.DistanceToSingularity.Results` contains
26,251 physical lines but 37 code-bearing lines and 99.3% blank lines. The
largest substantive module is
`Source.Higham.Chapter11.Section01.Tridiagonal` (57,688 physical, 51,482
code-bearing lines, 1,832 static declaration starters). Size is a review
signal, not sufficient evidence for a split.

The chapter table makes the whitespace effect reproducible. Chapter 7 has
1,007,906 physical but 24,709 code-bearing lines (96.9% raw blank lines),
Chapter 16 has 336,470 physical but 24,909 code-bearing lines, and Chapter 21
has 201,805 physical but 21,137 code-bearing lines. In contrast, Chapters 11
and 9 contain 147,993 and 109,737 code-bearing lines respectively. Any thesis
LOC claim should therefore report both physical and code-bearing definitions.

## Reorganization evidence

### Canonical source tree

The path spelling is uniform in the physical source layer: 1,405 modules use
exact `ChapterNN` spelling. There are no `ChNN`, `HighamChapterNN`, or other
noncanonical chapter-name signals inside the physical `Source` tree. The nine
nonchapter modules are:

- `NumStability.Source.Higham`;
- `NumStability.Source.Higham.CrossChapter`;
- seven modules beneath `CrossChapter` for LU solver weights, no-guard dot
  products, practical condition bounds, and symmetric-indefinite LU bridges.

Every chapter aggregate exists, with per-chapter module, physical/code-line,
declaration-starter, direct-import, and reachable-module counts in
[chapter_hierarchy.csv](chapter_hierarchy.csv).

### Compatibility and migrated ownership

There are 1,204/2,839 (42.41%) modules with zero static declaration starters.
Of these, 576/1,204 (47.84%) satisfy a conservative compatibility-path/docstring
heuristic and 479 satisfy the separately defined aggregate-entry-point
heuristic. These categories overlap and must not be added.

The strongest reorganization signal is independent of that heuristic:

- 381 chapter/source-labelled `Algorithms` paths and 12 such `Analysis` paths
  are all static declaration-free (393/393);
- 113 workflow-term paths in `Algorithms` and five in `Analysis` are all
  static declaration-free. The terms are tokenized `Actual`, `Final`,
  `Remaining`, `Whole`, `Bridge`, and `Closure`; substring false positives such
  as `Householder` are excluded by validation;
- all 14 historical `NumStability.Higham` entry/path modules are static
  declaration-free. Thirteen are under the old tree and the root
  `NumStability.Higham` forwards to `NumStability.Source.Higham`.

These facts support the thesis-safe statement that the completed
reorganization moved explicit source declaration ownership away from hundreds
of source-labelled legacy paths while preserving many old import paths. They
do not prove that every such path is required by external users, nor that the
compiled environment attributes no generated declarations to them.

Six files are static empty no-import entry points. Their docstrings explicitly
describe reviewed empty destinations or generated semantic entry points; the
source hygiene scan did not classify them as placeholder definitions. They are
listed in [empty_no_import_modules.csv](empty_no_import_modules.csv).

## Layering and import direction

The intended direction is:

```text
Examples -> Source -> Algorithms -> Analysis -> FloatingPoint
```

With consumer-to-imported orientation, an `Algorithms -> Analysis` source
import follows the intended direction; an `Algorithms -> Source` source import
is an apparent inversion. Compatibility shims are separated from declaration-
bearing implementation modules.

### Project source-import matrix

| Importer | Imported | Direct source-import edges | Static interpretation |
| --- | --- | ---: | --- |
| Algorithms | Algorithms | 2,793 | same layer |
| Algorithms | Analysis | 1,421 | intended direction |
| Algorithms | FloatingPoint | 139 | intended direction |
| Algorithms | Source | 1,091 | apparent reverse; mostly import-only surfaces |
| Analysis | Analysis | 1,241 | same layer |
| Analysis | FloatingPoint | 41 | intended direction |
| Analysis | Algorithms | 203 | apparent reverse |
| Analysis | Source | 251 | apparent reverse |
| FloatingPoint | FloatingPoint | 10 | same layer |
| FloatingPoint | Analysis | 11 | apparent reverse |
| Source | Source | 5,683 | same layer |
| Source | Algorithms | 2,991 | intended direction |
| Source | Analysis | 2,606 | intended direction |
| Source | FloatingPoint | 283 | intended direction |

The complete matrix, including root, compatibility, and upstream categories,
is [layer_source_import_matrix.csv](layer_source_import_matrix.csv).

### Declaration-bearing reverse-layer candidates

| Physical importer layer | Imported higher layer | Edges | Distinct importer modules | Relevant declaration-bearing module denominator |
| --- | --- | ---: | ---: | ---: |
| Algorithms | Source | 70 | 21 | 325 Algorithms modules (6.46% affected) |
| Analysis | Algorithms | 177 | 54 | 246 Analysis modules |
| Analysis | Source | 22 | 9 | 246 Analysis modules |
| FloatingPoint | Analysis | 11 | 4 | 5 FloatingPoint modules (80.0% affected) |

There are 56 distinct affected Analysis modules after overlap between its two
rows (22.76% of 246). Representative, source-verifiable cases include:

- `Algorithms.LinearSystems.LeastSquares.Equality.Basic`, whose own module
  documentation calls it canonical reusable content, directly imports six
  `Source.Higham` modules from Chapters 19 and 21;
- `Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.Executor.Core`
  directly imports thirteen `Source.Higham` modules;
- `Analysis.Perturbation.LeastSquares.Basic` directly imports fourteen
  `Algorithms` modules;
- `FloatingPoint.FusedMultiplyAdd.Core` directly imports five `Analysis`
  modules, several currently located under
  `Analysis.FloatingPointArithmetic`.

These rows are architectural review evidence. They do not prove that a proof
term actually references a declaration in the imported higher layer. A
declaration-graph join is required to separate logical inversion from imports
needed only during elaboration. Conversely, the `FloatingPoint -> Analysis`
pattern is a plausible ownership signal: foundational floating-point material
currently living below an `Analysis/FloatingPointArithmetic` path forces the
nominal foundational layer to import upward.

### Import-only reverse-layer candidates

Separately, 528 declaration-free canonical-layer modules account for 1,124
reverse-direction source-import edges. Explicit compatibility wording detects
921/1,124 (81.94%) of those edges. This supports the intended interpretation
that much of the raw inversion count comes from migration surfaces, while the
remaining 203 edges require manual classification as aggregates, re-exports,
or undocumented shims. It would be incorrect to report all 1,404
canonical-path reverse edges as implementation-layer violations.

### Source wrappers and lower layers

For the 1,054 declaration-bearing Source modules:

- 867 (82.26%) directly import a lower layer;
- 1,015 (96.30%) reach a lower layer through the source-import graph;
- 39 (3.70%) do not reach a lower layer;
- declaration-bearing Source modules contribute 2,930 direct imports to
  Algorithms, 2,535 to Analysis, and 277 to FloatingPoint (5,742 lower-layer
  edges total, with modules allowed to appear in several categories).

Static size buckets, defined before use, identify 253 small source-surface
candidates (at most 100 code-bearing lines and at most five declaration
starters), 471 medium modules, and 330 substantial review candidates (over 500
code-bearing lines or over 20 declaration starters). These labels do not
decide whether proofs delegate. Use body edges and exact-statement/delegation
artifacts for that question.

## Public entry points and static consumability

Every listed root entry point is static declaration-free. Reachability counts
include the entry module itself; declaration counts below are static source
starters, not environment-public declarations.

| Entry point | Direct internal imports | Reachable modules | Reachable declaration-bearing modules | Reachable static declaration starters | Notable transitive breadth |
| --- | ---: | ---: | ---: | ---: | --- |
| `NumStability` | 1 | 2,130 | 1,635/1,635 | 46,719/46,719 | Compatibility root over `All` |
| `NumStability.All` | 4 | 2,129 | 1,635/1,635 | 46,719/46,719 | Complete declaration-bearing static surface |
| `NumStability.Algorithms` | 171 | 1,774 | 1,474/1,635 | 43,552/46,719 | Reaches 1,123 Source modules |
| `NumStability.Analysis` | 143 | 728 | 609/1,635 | 25,011/46,719 | Reaches 128 Algorithms and 253 Source modules |
| `NumStability.FloatingPoint` | 4 | 17 | 14/1,635 | 1,302/46,719 | Reaches nine Analysis modules |
| `NumStability.Core` | 6 | 17 | 14/1,635 | 818/46,719 | Focused Analysis/FP core |
| `NumStability.Source` | 35 | 1,885 | 1,569/1,635 | 45,326/46,719 | Reaches 308 Algorithms and 211 Analysis modules |
| `NumStability.Source.Higham` | 63 | 1,884 | 1,569/1,635 | 45,326/46,719 | Canonical Higham entry |
| `NumStability.Higham` | 1 | 1,885 | 1,569/1,635 | 45,326/46,719 | Historical compatibility entry |

The complete-tree behavior is a public-consumability strength: static
declaration owners are not stranded outside `NumStability.All`. At the same
time, the domain aggregates are not clean layer boundaries. For example,
`NumStability.Algorithms` directly imports 79 Algorithms, 19 Analysis, and 73
Source modules, while `NumStability.Analysis` directly imports 62 Analysis, 10
Algorithms, 69 Source, and two FloatingPoint modules. Those facts conflict
with the comments describing them simply as the Algorithms subtree and the
reusable Analysis subtree. An external user seeking a narrow, source-independent
surface may therefore need a more specific domain module.

Useful narrower entry points do exist. Examples in
[entry_points.csv](entry_points.csv) include:

- `Algorithms.Summation` (eight direct imports; 104-module closure);
- `Algorithms.LinearSystems.QR` (17 direct imports; 44-module closure);
- `Algorithms.LinearSystems.LU.BlockLU` (16 direct imports; 55-module closure);
- `Algorithms.MatrixEquations` (one direct import; 128-module closure);
- `Algorithms.NormEstimation` (three direct imports; 111-module closure);
- `Analysis.MatrixNorms` (11 direct imports; 69-module closure);
- `FloatingPoint.FusedMultiplyAdd.All` (two direct imports; 13-module closure);
- every `Source.Higham.ChapterNN` aggregate.

Some nominally narrow domains still reach Source because lower modules contain
inversions: `Algorithms.Summation` reaches 25 Source modules, and
`Algorithms.LinearSystems` reaches 142. This is a static warning about import
breadth, not evidence that clients need source-labelled declarations in their
terms.

The analyzer found 479 static aggregate candidates. Among declaration-bearing
implementation modules, 82 imports target one of these detected aggregates;
47 have a transitive source-import width of at least 50 modules, and all 47
occur in the Source layer. Canonical implementation layers have only two such
detected aggregate imports, both narrow six-module `.All` imports from
`Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results`. A
separate conventional-name check found 11 `.All` imports in ten implementation
modules; nine are Source uses and two are the same narrow Analysis uses. Thus
the static evidence does not show broad umbrella imports inside canonical
Algorithms or FloatingPoint implementation modules.

There are 202 modules satisfying the predeclared review formula “at least 20
direct imports and at most five static declaration starters”; 156 are
declaration-bearing. Several underdetermined linear-system endpoint modules
have roughly 79--82 imports for one to five declarations. These may be useful
high-level endpoints, but their incremental-compilation and API-breadth cost
deserves review using fresh module timings and elaborated logical edges.

## Domain and external-dependency inventory

Path-derived domain classification is deterministic but heuristic. Counts are:

| Domain guess | Modules | Domain guess | Modules |
| --- | ---: | --- | ---: |
| Higham source other | 904 | Other | 282 |
| Norms/conditioning | 206 | Least squares/underdetermined | 176 |
| Matrix equations | 151 | Matrix powers/functions | 145 |
| Symmetric indefinite | 128 | LU | 114 |
| Test matrices | 103 | Spectral | 102 |
| Floating point/rounding | 100 | Cholesky | 92 |
| Summation | 87 | QR | 77 |
| Probability/statistics | 49 | Perturbation/error bounds | 41 |
| Polynomials | 25 | Matrix multiplication | 17 |
| FFT/circulant | 14 | Dot product | 12 |
| Arithmetic | 7 | Nonlinear | 7 |

Because precedence is path-regex based, these categories must not be treated as
mathematical ontology. The raw module assignment and domain import matrix are
provided for audit/reclassification.

There is no physical `NumStability/Examples` subtree in this commit and no
NumStability source import to benchmark or example code. All 11,506 external
import occurrences resolve by prefix to Mathlib (11,499) or Batteries (seven),
covering 304 distinct Mathlib modules and three distinct Batteries modules.
This is defensible evidence against accidental benchmark-layer coupling at the
source-import level.

## Static proof-hygiene evidence

The nested-comment/string-aware lexical scan found:

- zero code occurrences of `sorry`, `admit`, or `sorryAx`;
- zero code occurrences of the placeholder words `placeholder`, `todo`,
  `fixme`, `dummy`, or `unimplemented`;
- zero code occurrences of `unsafe`;
- zero static `axiom` or `constant` declaration starters;
- 40 `sorry` and 40 `admit` occurrences in comments;
- 11 placeholder-word occurrences in comments;
- 94 `axiom`/`axioms` word occurrences in comments;
- five code occurrences of `axioms`, all in `#print axioms ...` diagnostic
  commands in
  `Source.Higham.Chapter11.BunchKaufman.SourceCorrection`, not axiom
  declarations.

This supports a source-hygiene claim only. The compiled-environment audit must
determine actual axioms, declarations without bodies, and theorem proof-term
assumptions. In particular, opacity is not treated as a placeholder.

## Publication-safe interpretation

Safe conclusions from this static evidence include:

- the reorganization created a uniform Higham source hierarchy and shifted
  explicit declaration ownership away from hundreds of old source-labelled
  canonical paths;
- it retained a large compatibility/re-export surface;
- the source import graph is acyclic;
- the complete aggregate reaches every static declaration-bearing module;
- most declaration-bearing Source modules import or transitively reach lower
  reusable layers;
- residual reverse-layer imports remain in declaration-bearing modules and
  should be joined with elaborated dependency edges before being classified as
  logical architectural violations;
- public aggregates vary greatly in breadth, so narrow domain imports are
  materially relevant to client ergonomics.

This evidence does **not** establish that:

- an import is a theorem dependency;
- a declaration is public, source-written, or generated;
- a Source result directly delegates its proof to a canonical result;
- an import with no logical edge is removable;
- a declaration-free module is unnecessary to external users;
- a module's path-derived domain is mathematically exclusive;
- compile success, source reuse, or entry-point visibility proves faithfulness
  to Higham;
- `NumStability.All` is universally convenient merely because it reaches all
  static declaration owners.

## Raw artifact guide

| Artifact | Contents |
| --- | --- |
| [modules.csv](modules.csv) | Every module, path hash, layer, chapter/domain guess, LOC, imports, static declaration/command counts, and aggregate/compatibility signals |
| [source_imports.csv](source_imports.csv) | Every parsed source import with file/line, layer classification, and explicit nonlogical-edge warning |
| [root_entry_points.csv](root_entry_points.csv) | Root/aggregate direct imports and transitive module/static-declaration reachability |
| [entry_points.csv](entry_points.csv) | All 479 detected aggregate/entry-point candidates |
| [modules_not_reachable_from_NumStability_All.csv](modules_not_reachable_from_NumStability_All.csv) | The 710 out-of-closure modules, all static declaration-free |
| [layer_source_import_matrix.csv](layer_source_import_matrix.csv) | Layer-to-layer source-import matrix |
| [implementation_layer_inversion_candidates.csv](implementation_layer_inversion_candidates.csv) | 280 reverse-direction imports from declaration-bearing canonical-layer modules |
| [Algorithms_to_Source_implementation_import_inversions.csv](Algorithms_to_Source_implementation_import_inversions.csv) | Focused 70-edge, 21-module Algorithms-to-Source review set |
| [import_only_layer_inversion_candidates.csv](import_only_layer_inversion_candidates.csv) | 1,124 reverse-direction imports from declaration-free canonical-layer paths |
| [canonical_layer_source_import_reachability.csv](canonical_layer_source_import_reachability.csv) | Direct/transitive higher-layer reachability by canonical-layer module |
| [source_to_algorithms_imports.csv](source_to_algorithms_imports.csv) | All direct Source-to-Algorithms import rows |
| [source_module_static_profiles.csv](source_module_static_profiles.csv) | Lower-layer reach and static thinness/size signals for declaration-bearing Source modules |
| [declaration_free_modules.csv](declaration_free_modules.csv) | All 1,204 static declaration-free modules |
| [compatibility_shim_candidates.csv](compatibility_shim_candidates.csv) | Conservative 576-module compatibility heuristic |
| [legacy_NumStability_Higham_modules.csv](legacy_NumStability_Higham_modules.csv) | All 14 historical Higham import paths and targets |
| [canonical_layer_source_label_name_signals.csv](canonical_layer_source_label_name_signals.csv) | All 393 chapter/source-labelled paths remaining under canonical layers |
| [naming_workflow_signals.csv](naming_workflow_signals.csv) | Token-aware Actual/Final/Remaining/Whole/Bridge/Closure path signals |
| [module_size_review_candidates.csv](module_size_review_candidates.csv) | Contract-threshold module-size review set with blank fractions and code density |
| [many_imports_few_declarations.csv](many_imports_few_declarations.csv) | Explicit >=20 imports, <=5 static declarations review set |
| [detected_aggregate_imports_in_implementation_modules.csv](detected_aggregate_imports_in_implementation_modules.csv) | Aggregate imports and source-import closure widths |
| [broad_aggregate_imports_in_implementation_modules.csv](broad_aggregate_imports_in_implementation_modules.csv) | Conventional umbrella/`.All` import review set |
| [source_import_sccs.csv](source_import_sccs.csv) | Source-import strongly connected components (all trivial) |
| [chapter_hierarchy.csv](chapter_hierarchy.csv) | Chapter01--Chapter28 presence, size, declarations, direct imports, reachability |
| [domain_guess_source_import_matrix.csv](domain_guess_source_import_matrix.csv) | Heuristic domain-level source-import matrix |
| [chapter_guess_source_import_matrix.csv](chapter_guess_source_import_matrix.csv) | Chapter-name-level source-import matrix |
| [proof_hygiene_static_occurrences.csv](proof_hygiene_static_occurrences.csv) | Every hygiene-term occurrence with code/comment/string classification |
| [static_declaration_starters.csv](static_declaration_starters.csv) | Source declaration-introducer matches; not the elaborated declaration universe |
| [summary.json](summary.json) | Machine-readable totals, formulas, distributions, scope, and limitations |

