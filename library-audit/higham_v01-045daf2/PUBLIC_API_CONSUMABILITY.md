# Public API consumability audit

## Executive finding

At commit `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`, a predeclared,
stratified sample of 15 explicitly source-written canonical declarations was
both visible and usable from standalone external Lean files through narrow
owner-module imports. All 15 independent `#check` files compiled, and all 15
separately compiled client files contained an accepted theorem/example that
applied the selected declaration. All outputs were fresh probe outputs; imported
dependencies were cached artifacts from the isolated worktree.

This supports the conservative thesis claim that **representative public APIs
from floating-point foundations, reusable analysis, and numerical algorithms
can be consumed compositionally through narrow imports in the recorded Lean
environment**. It is not a library-wide usability rate: the sample was
purposefully stratified rather than random, and most client examples are thin
forwarding corollaries.

The separate exhaustive direct-type pass finds that 743/17,547 (4.2343%)
confirmed-source-written public declarations in the canonical
`FloatingPoint`/`Analysis`/`Algorithms` layers have at least one of the
overlapping audited review signals; 605/17,547 (3.4479%) directly expose a
Source-layer target. These are ownership and signature-review candidates, not
failed APIs or a consumability score.

The strongest residual consumability concern is import granularity. Narrow
canonical owners can be source-independent, but several advertised broad
aggregates transitively import substantial `Source/Higham` surfaces. Users who
want a clean reusable layer must know the exact owner module.

Full probe detail is in
[probes/PUBLIC_API_PROBES.md](./probes/PUBLIC_API_PROBES.md). Machine-readable
results are in [probes/summary.json](./probes/summary.json) and
[probes/results.csv](./probes/results.csv).

## Scope and declaration universe

Probe schema: `numstability-public-api-probes/v1`. The complementary exhaustive
direct-type and entry-point scan uses schema
`numstability-public-type-exposure/1.0.0`; its definitions, input hashes, tool
hash, outputs, and validation results are in
[public_type_exposure_summary.json](./current_graph/metrics/public_type_exposure_summary.json).

The probe universe is exactly the 15 declarations in
[probes/PREDECLARED_SAMPLE.csv](./probes/PREDECLARED_SAMPLE.csv). It was fixed
before compilation and spans:

- the floating-point operation model and gamma calculus;
- summation and dot products;
- vector and matrix norms;
- residual/perturbation theory;
- matrix multiplication;
- forward triangular substitution and LU factorization;
- QR and least-squares specifications;
- a one-norm condition estimator bound;
- iterative refinement; and
- inverse-based linear solving.

The sample excludes declarations under `NumStability.Source` or the legacy
`NumStability.Higham` tree, private/internal declarations, compiler-generated
names, and modules classified by the static analyzer as compatibility
candidates. Each selection has an exact source introducer and a matching
compiled-environment declaration row. One post-selection metadata correction
moved P13's recorded source line from its docstring start (84) to its theorem
introducer (94); no declaration, import, or probe changed. See
[probes/MANIFEST_CORRECTIONS.md](./probes/MANIFEST_CORRECTIONS.md).

The sample is an evidence-bearing case study, not a statistical sample of all
public declarations. Percentages below must not be generalized beyond these
denominators.

## Metric definitions and results

| Metric | Numerator | Denominator and exact universe | Formula/filter | Raw artifact and column |
|---|---:|---|---|---|
| Compiled environment-public selections | 15 | 15 predeclared declarations | `is_internal=false AND is_private=false` | [selected metadata](./probes/selected_declaration_environment_metadata.csv), `is_internal`, `is_private` |
| Selections with bodies | 15 | 15 predeclared declarations | `has_body=true` | same artifact, `has_body` |
| Independent visibility successes | 15 | 15 predeclared narrow-import check files | `check_status=pass` | [results](./probes/results.csv), `check_status` |
| External client-proof successes | 15 | 15 predeclared client files | `client_status=pass`; each file contains `#check` plus a theorem/example applying the API | same artifact, `client_status` |
| Exact source-line confirmations | 15 | 15 predeclared declarations | declaration basename occurs on recorded introducer line | same artifact, `source_line_validated` |
| Adjacent source docstrings | 14 | 15 predeclared declarations | conservative immediately preceding `/-- ... -/` detection | same artifact, `has_adjacent_source_docstring` |
| Source-free narrow import closures | 15 | 15 selected imports | zero modules named `NumStability.Source...` in static transitive project-import closure | [narrow import closure](./probes/narrow_import_closure.csv), `reachable_source_modules` |
| Selected signatures clean under audited project-target categories | 15 | 15 selected declaration types | zero direct project type targets that are private/internal, Source-layer, or in a static compatibility-candidate module | [results](./probes/results.csv), the three `direct_*_type_dependency_count` columns |
| Direct project type edges to environment-public targets | 49 | 49 compiled direct dependency rows with selected source, `occurs_in_type=true`, `target_scope=project` | target `is_internal=false AND is_private=false` | [selected type edges](./probes/selected_api_direct_project_type_dependencies.csv), target visibility columns |
| Direct project type edges outside Source | 49 | same 49 direct project type edges | target module does not start `NumStability.Source` | same artifact, `target_is_source_layer` |
| Direct project type edges outside static compatibility candidates | 49 | same 49 direct project type edges | target module absent from compatibility-candidate set | same artifact, `target_module_is_static_compatibility_candidate` |

For the compiled declaration graph, `A -> B` means that `A` directly references
`B`. The signature analysis above filters to edges occurring in `A`'s type. It
does not treat body-only proof dependencies as API exposure, and it does not
inspect only textual names.

## Visibility and practical use are separate

Each API has two retained files under [probes/src](./probes/src):

1. `*_check.lean` imports only the selected module and performs a fully
   qualified `#check`.
2. `*_client.lean` repeats the `#check` and adds a minimal external
   theorem/example that applies the declaration with its actual hypotheses.

The files were compiled independently and have separate statuses, timings,
logs, `.olean` files, and `.ilean` files. Therefore a failed application could
have been reported even if visibility succeeded. The harness validation makes
this distinction executable: a known-visible control compiled, while a file
whose `#check` succeeded but whose example deliberately had the wrong type
exited 1. Evidence is in
[probes/VALIDATION_RESULTS.csv](./probes/VALIDATION_RESULTS.csv) and
[probes/validation_output](./probes/validation_output).

A successful client proof is stronger evidence than `#check`: it checks the
selected import, name resolution, parameter elaboration, assumptions, notation,
and result type. It still establishes usability only for that exact client.

## Representative public APIs

| Area | Declaration | Narrow owner import | Minimal client use | Main explicit requirements |
|---|---|---|---|---|
| Floating-point model | `NumStability.FPModel.model_basicOp` | `NumStability.FloatingPoint.Model` | obtain a bounded relative-error witness for a primitive operation | division branch carries a conditional nonzero-denominator proof |
| Gamma | `NumStability.gamma_nonneg` | `NumStability.Analysis.Rounding` | prove nonnegativity of `gamma fp n` | `gammaValid fp n` |
| Summation | `NumStability.fl_sum_error` | `NumStability.Analysis.Summation.ErrorBounds` | obtain bounded termwise perturbations for the sequential sum | `FPModel`, `Fin n -> Real`, gamma guard; conclusion exposes `Fin.foldl` |
| Dot product | `NumStability.dotProduct_error_bound` | `NumStability.Algorithms.DotProduct` | apply the componentwise forward-error inequality | two finite vectors and gamma guard |
| Vector norm | `NumStability.complexVecLpNorm_two_ofLp_eq` | `NumStability.Analysis.VectorNorms.Basic` | bridge the custom complex L2 norm to `EuclideanSpace` | `WithLp`, `ENNReal`, custom `CVec` representation |
| Matrix norm | `NumStability.complexMatrixLpNorm_upper_bound_by_columnMax_lpNorm` | `NumStability.Analysis.MatrixNorms.Lp` | produce a mixed subordinate bound | custom norm predicates and `1 <= p` |
| Perturbation | `NumStability.forward_error_from_residual` | `NumStability.Analysis.PerturbationTheory` | bound forward error using a residual and left inverse | function matrices, `IsLeftInverse`, pointwise exact system proof |
| Matrix multiplication | `NumStability.matMul_error_bound` | `NumStability.Algorithms.MatMul` | apply the gamma-scaled entrywise product bound | three dimensions, function matrices, gamma guard |
| Triangular solve | `NumStability.forwardSub_backward_error` | `NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution` | obtain an existential matrix perturbation and exact perturbed solve | nonzero diagonal, pointwise triangularity, gamma guard |
| LU | `NumStability.lu_backward_error_gamma` | `NumStability.Algorithms.LU.GaussianElimination` | turn `LUBackwardError` into an explicit perturbation | pre-existing factorization error certificate |
| QR | `NumStability.givensRotation_orthogonal` | `NumStability.Algorithms.LinearSystems.QR.GivensSpec` | construct an `IsOrthogonal` certificate | distinct finite indices and `c^2+s^2=1` |
| Least squares | `NumStability.RectLSNormalEquations.isLeastSquaresMinimizer` | `NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations` | derive global minimality from normal equations | custom normal-equation/minimizer predicates |
| Condition number | `NumStability.condOneNumber_ge_scaled_estimator` | `NumStability.Analysis.ConditionEstimatorLowerBound` | apply the scaled LAPACK-estimator lower bound | positive dimension; supplied matrices `A` and `B` |
| Iterative refinement | `NumStability.one_step_refinement_error_identity` | `NumStability.Algorithms.LinearSystems.IterativeRefinement.Core` | derive the exact one-step error identity | exact solution, residual, perturbed correction solve, and update equations |
| Matrix inversion | `NumStability.inversion_residual_bound` | `NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion` | obtain the inverse-based solve residual bound | `IsRightInverse` and gamma guard |

All individual source paths, line numbers, assumptions, helpers, commands,
hashes, and friction notes are recorded row-by-row in
[probes/results.csv](./probes/results.csv).

## Intended public roots and aggregates

The branch's curated lookup guide,
[_worktree/docs/LIBRARY_LOOKUP.md](./_worktree/docs/LIBRARY_LOOKUP.md), names
these root surfaces:

| Import | Intended role | Audit observation |
|---|---|---|
| `NumStability.Core` | small shared foundation | declaration-free aggregate; source-clean static closure |
| `NumStability.FloatingPoint` | models and operation laws | declaration-free aggregate; source-clean static closure |
| `NumStability.Analysis` | general error, norm, conditioning, perturbation, probability, and operator theory | declaration-free aggregate, but broad closure reaches Source modules |
| `NumStability.Algorithms` | algorithms and their correctness/error analyses | declaration-free aggregate, but very broad closure reaches Source modules |
| `NumStability.Source` | numbered-source correspondence | deliberate Source entry point |
| `NumStability.Source.Higham` | complete Higham correspondence | preferred Higham-specific source entry point |
| `NumStability.All` | all supported domains | deliberate complete-tree aggregate |
| `NumStability` | package-wide convenience import | static compatibility candidate forwarding to `NumStability.All` |
| `NumStability.Higham` | historical Higham entry point | static compatibility candidate; prefer `NumStability.Source.Higham` |

Representative domain-specific public entry points documented by the branch
include:

- `NumStability.Analysis.Rounding` for unit-roundoff and gamma calculus;
- `NumStability.Analysis.VectorNorms` and
  `NumStability.Analysis.MatrixNorms` for norm families;
- `NumStability.Analysis.PerturbationTheory` for linear-system residual and
  perturbation bounds;
- `NumStability.Algorithms.Summation` and
  `NumStability.Algorithms.DotProduct` for scalar reductions;
- `NumStability.Algorithms.MatMul` and `NumStability.Algorithms.MatVec` for
  matrix arithmetic;
- `NumStability.Algorithms.LinearSystems.Triangular`,
  `NumStability.Algorithms.LinearSystems.LU`,
  `NumStability.Algorithms.LinearSystems.Cholesky`, and
  `NumStability.Algorithms.LinearSystems.QR` for solver/factorization families;
- `NumStability.Algorithms.LinearSystems.LeastSquares` for least squares;
- `NumStability.Algorithms.MatrixInversion` for inverse-based algorithms;
- `NumStability.Algorithms.MatrixEquations` for Sylvester/Lyapunov families;
  and
- narrow norm-estimation modules such as
  `NumStability.Algorithms.NormEstimation.OneNorm.LAPACK.Basic`.

For implementation and focused clients, the branch's guide explicitly prefers
the narrow semantic owner over the aggregate. The successful probes follow
that rule.

## Narrow versus broad import evidence

The import figures in this section are static source-import transitive
reachability counts. They are not elaborated declaration counts, visibility
counts, or theorem-dependency edges.

| Entry point | Project modules reached, including entry | Declaration-bearing modules reached | Static declaration starters reached | Source modules reached |
|---|---:|---:|---:|---:|
| `NumStability.Core` | 17 | 14 | 818 | 0 |
| `NumStability.FloatingPoint` | 17 | 14 | 1,302 | 0 |
| `NumStability.Analysis` | 728 | 609 | 25,011 | 253 |
| `NumStability.Algorithms` | 1,774 | 1,474 | 43,552 | 1,123 |
| `NumStability.Source` | 1,885 | 1,569 | 45,326 | 1,355 |
| `NumStability.Source.Higham` | 1,884 | 1,569 | 45,326 | 1,354 |
| `NumStability.All` | 2,129 | 1,635 | 46,719 | 1,356 |
| `NumStability` | 2,130 | 1,635 | 46,719 | 1,356 |

Raw rows and their semantics are in
[probes/entrypoint_reachability_excerpt.csv](./probes/entrypoint_reachability_excerpt.csv),
derived from
[static_architecture/entry_points.csv](./static_architecture/entry_points.csv)
and
[static_architecture/source_imports.csv](./static_architecture/source_imports.csv).

The complete declaration-exposure census is
[public_entrypoint_exposure_all.csv](./current_graph/metrics/public_entrypoint_exposure_all.csv).
It contains 1,437 rows: each of the 479 predeclared entry modules is measured
against all project-owned environment declarations, environment-public
declarations, and confirmed-source-written public declarations. Of the 479
closures, 439 come from the compiled module-import graph; the remaining 40
entry files are declaration-free and use a static closure only after the
static and compiled closures agreed for all 439 observed entries and every
declaration-bearing fallback module had compiled ownership data. The new table
reproduces all 939 previously observed rows and supersedes 117 old zero rows
that represented unobserved entries rather than zero exposure. No
static/compiled closure mismatch was observed. Closure exposure measures
availability by owner module, not practical usability.

| Root entry | Reachable environment-public | Reachable confirmed-source-written public | Closure basis |
|---|---:|---:|---|
| `NumStability` | 58,120/58,120 (100%) | 47,890/47,890 (100%) | compiled |
| `NumStability.All` | 58,120/58,120 (100%) | 47,890/47,890 (100%) | compiled |
| `NumStability.Core` | 1,007/58,120 (1.7326%) | 849/47,890 (1.7728%) | validated declaration-free static fallback |
| `NumStability.FloatingPoint` | 1,653/58,120 (2.8441%) | 1,347/47,890 (2.8127%) | compiled |
| `NumStability.Analysis` | 29,543/58,120 (50.8310%) | 25,467/47,890 (53.1781%) | compiled |
| `NumStability.Algorithms` | 54,149/58,120 (93.1676%) | 44,770/47,890 (93.4851%) | compiled |
| `NumStability.Source` | 56,401/58,120 (97.0423%) | 46,499/47,890 (97.0954%) | compiled |
| `NumStability.Source.Higham` | 56,401/58,120 (97.0423%) | 46,499/47,890 (97.0954%) | compiled |
| `NumStability.Higham` | 56,401/58,120 (97.0423%) | 46,499/47,890 (97.0954%) | validated declaration-free static fallback |

For every percentage in this table, the numerator is `reachable_declarations`,
the denominator is `universe_declarations`, and the universe is named by the
corresponding row of `public_entrypoint_exposure_all.csv`; `closure_basis` and
`coverage_status` record the method. The CSV contains the analogous three-row
measurement for every documented and `.All` aggregate, not just these roots.

Two domain aggregates illustrate the practical distinction:

- `NumStability.Algorithms.Summation` reaches 104 project modules and 25
  Source modules. Its docstring acknowledges that it retains Chapter 4 source
  declarations. The P03 owner
  `NumStability.Analysis.Summation.ErrorBounds` reaches four project modules
  and no Source module.
- `NumStability.Algorithms.LinearSystems.LeastSquares` reaches 153 project
  modules and 35 Source modules despite describing itself as a reusable
  canonical aggregate. The P12 owner `...LeastSquares.NormalEquations` reaches
  49 project modules and no Source module.

All 15 selected owner imports had zero Source modules in their static closure,
although their closure sizes ranged from 1 to 49 project modules. Therefore
"narrow owner" means conceptually focused and source-neutral here, not
necessarily a tiny transitive dependency footprint.

Accordingly, 0/15 declarations in the predeclared probe sample were available
only through an unexpectedly broad import: each compiled from its narrow owner
module. This audit did not compute the narrowest viable import for every public
declaration, so it does not identify a library-wide zero set or claim that no
other public declaration requires an unexpectedly broad import.

An import with no elaborated logical edge may still supply notation, tactics,
macros, attributes, or instances. These findings identify review and user-
experience concerns; they do not prove that any import is removable.

## Canonical, source, aggregate, and legacy roles

- Canonical reusable mathematics is intended to live under
  `FloatingPoint`, `Analysis`, and `Algorithms`, with concept-facing names.
- `Source/Higham/ChapterNN` is the deliberate source-labelled layer. It should
  preserve numbered-source traceability and delegate to canonical results when
  appropriate.
- `All`, `Analysis`, `Algorithms`, and family aggregates are re-export surfaces,
  not declaration owners in the sampled root files.
- `NumStability` and `NumStability.Higham` are explicit compatibility entry
  points; the latter is superseded by `NumStability.Source.Higham`.
- The old `Algorithms.QR`, `Algorithms.LeastSquares`, and
  `Algorithms.Sylvester` trees are statically import-only surfaces; substantive
  ownership is under `Algorithms.LinearSystems.QR`,
  `Algorithms.LinearSystems.LeastSquares`, and
  `Algorithms.MatrixEquations.Sylvester`.
- Reorganization is not uniform across every family. The curated canonical LU
  owner used by P10 remains `Algorithms.LU.GaussianElimination`, while other LU
  material also lives under `Algorithms.LinearSystems.LU`; Cholesky ownership
  is similarly split between older and newer paths.

These role claims are supported by the curated lookup plus the static module
profiles and compatibility worklists in
[static_architecture](./static_architecture). Static declaration-free
classification is not the same as a compiled-environment proof of zero owned
declarations; the full architecture audit reports that distinction separately.

## Signature exposure

The 15 selected signatures contain 49 direct project-to-project type edges.
The compiled metadata shows:

- 49/49 targets are environment-public;
- 49/49 targets are outside `NumStability.Source`; and
- 49/49 targets are outside modules in the static compatibility-candidate set.

Thus none of these selected types directly exposes a project declaration in
the audited private/internal, Source, or compatibility categories. This is a
positive sign for the selected canonical surface.

It does not mean the signatures are abstraction-light. Several intentionally
public types expose implementation-shaped or library-specific vocabulary:
`Fin.foldl`, raw functions `Fin n -> ...` as vectors and matrices, `CVec`,
`CMatrix`, `WithLp`, `ENNReal`, `MixedSubordinateMatrixBound`,
`LUBackwardError`, `RectLSNormalEquations`, and inverse/orthogonality
certificates. These are public abstractions rather than private leaks, but they
affect onboarding and interoperability.

### Exhaustive direct-type exposure

The exhaustive pass keeps environment visibility and conservative
source-origin evidence separate. A direct type edge is an elaborated project
pair `A -> B` with `occurs_in_type=true`; it is not a textual occurrence,
import edge, or transitive unfolding result.

| Source-declaration universe | Sources with at least one nonpublic direct project type target | Nonpublic-target edges | Distinct nonpublic targets | Also in body | Type only | Edges to private targets |
|---|---:|---:|---:|---:|---:|---:|
| All environment-public declarations, generated/unresolved retained | 2,259/58,120 (3.8868%) | 3,467 | 1,630 | 1,332 | 2,135 | 99 |
| Confirmed-source-written public declarations | 650/47,890 (1.3573%) | 882 | 231 | 808 | 74 | 85 |

The first row is supported by
[environment_public_type_nonpublic_exposure_edges.csv](./current_graph/metrics/environment_public_type_nonpublic_exposure_edges.csv),
especially `source`, `source_confirmed_source_written`, `target_is_internal`,
`target_is_private`, `target_authorship_class`, and `occurs_in_body_also`.
The second is supported by
[public_type_exposure_edges.csv](./current_graph/metrics/public_type_exposure_edges.csv),
especially `exposure_nonpublic_target`,
`exposure_generated_or_unresolved_nonpublic_target`,
`exposure_confirmed_source_written_nonpublic_target`, and
`occurs_in_body_also`. In that conservative second universe, the 882 edges
partition into 81 edges to confirmed-source-written nonpublic targets and 801
to generated-or-authorship-unresolved nonpublic targets. The broader
environment-public row instead has target-authorship counts 91, 3,373, and 3
for confirmed-source-written, internal-without-direct-range, and
range-token-mismatch targets respectively.

The conservative 47,890-declaration universe also yields the following
overlapping review signals. Counts before the slash are source declarations;
counts after it are unique direct type pairs:

| Direct-type review signal | Source declarations / edges | Declaration denominator |
|---|---:|---:|
| Nonpublic target | 650 / 882 | 47,890 confirmed-source-written public |
| Generated-or-authorship-unresolved target, of any visibility | 794 / 1,002 | 47,890 confirmed-source-written public |
| Reserved-name target | 0 / 0 | 47,890 confirmed-source-written public |
| Static compatibility-candidate target | 0 / 0 | 47,890 confirmed-source-written public |
| Examples-layer target | 0 / 0 | 47,890 confirmed-source-written public |
| Union of all recorded signals, including canonical-to-Source below | 1,452 / 2,233 | 47,890 confirmed-source-written public |

“Generated-or-authorship-unresolved” is deliberately broader than Lean's
reserved-name predicate and is not proof that a target was generated. The
separate reserved-name count is zero. Signal rows overlap and therefore must
not be added.

The most architecture-relevant subset contains exactly 17,547
confirmed-source-written public declarations whose effective layer is
`FloatingPoint`, `Analysis`, or `Algorithms`:

| Canonical direct-type review signal | Source declarations / 17,547 | Unique direct type edges |
|---|---:|---:|
| Nonpublic target | 75 (0.4274%) | 87 |
| Generated-or-authorship-unresolved target, of any visibility | 133 (0.7580%) | 149 |
| Source-layer target | 605 (3.4479%) | 1,150 |
| Reserved-name target | 0 (0%) | 0 |
| Static compatibility-candidate target | 0 (0%) | 0 |
| Examples-layer target | 0 (0%) | 0 |
| Union of all recorded signals | 743 (4.2343%) | 1,304 |

The nonpublic and generated/authorship-unresolved signals overlap for 70
source declarations and 82 edges. The Source signal is disjoint from both;
the union identities are therefore `75 + 133 - 70 + 605 = 743` declarations
and `87 + 149 - 82 + 1,150 = 1,304` edges. The full per-source aggregation is
[public_type_exposure_declarations.csv](./current_graph/metrics/public_type_exposure_declarations.csv),
with the raw signal columns named in its header.

These 743 declarations and 1,304 edges are a review set, not a cohesion score,
an API-failure rate, or 743 automatic defects. In particular, generated proof
helpers can be benign elaboration artifacts, and a Source-layer type target can
reflect intentional ownership debt. The scan does not pretty-print
user-visible signatures, unfold transitive dependencies, test name discovery,
or compile all possible clients. Those tasks remain manual or experimental.

## Naming, namespaces, documentation, and discoverability

The selected names are predominantly mathematical and concept-facing:
`gamma_nonneg`, `dotProduct_error_bound`, `forward_error_from_residual`,
`forwardSub_backward_error`, and `inversion_residual_bound` communicate their
roles without book numbering. No selected name requires a Higham theorem
number, compatibility namespace, or accidental generated name.

Module paths encode a deeper domain hierarchy, but most declarations still
live directly in the flat `NumStability` namespace. P01 is additionally under
`FPModel`; P12 is under `RectLSNormalEquations`. This keeps use concise after
`open NumStability`, but a user cannot always infer the qualified declaration
name from the filesystem path. The curated lookup and its executable
`LibraryLookupChecks.lean` materially improve discoverability.

Fourteen of the 15 selected declaration introducers have adjacent docstrings.
The sampled exception is `complexVecLpNorm_two_ofLp_eq`. This percentage is
only for the selected universe; it is not a library-wide documentation rate.

## API friction assessment

The retained reviewer labels classify five probes as low friction, seven as
moderate, and three as high. These labels are qualitative structured judgments,
not a cohesion or consumability score.

Observed strengths:

- all sample areas were usable without importing `NumStability`, `All`,
  `Source`, or a compatibility path;
- common side conditions are explicit rather than hidden;
- certificate types allow results to compose without exposing private helpers;
- method-style use works for `FPModel` and `RectLSNormalEquations`; and
- selected high-level refinement and inverse-solve endpoints elaborate in an
  external file.

Observed friction:

- users must frequently state `gammaValid`, positive-dimension, nonbreakdown,
  inverse, and triangularity proofs explicitly;
- vector/matrix arguments are often raw finite functions rather than Mathlib
  `Matrix` values;
- the norm surface has substantial custom vocabulary and representation
  bridges;
- high-level endpoint statements can require many intermediate objects and
  pointwise equations;
- some theorems consume a certificate without showing how a client obtains it
  from an executable algorithm; P10 assumes `LUBackwardError`; and
- broad exploratory aggregates can import source-labelled material, while the
  cleanest client experience requires knowing a narrow owner.

P13 deserves a precise interpretation: its client establishes a scaled
estimator bound for a supplied matrix `B`. Calling it the textbook condition
number of `A` additionally requires a proof that `B` is an inverse, supplied by
separate declarations.

## Suitability for extension

The successful clients indicate several families are suitable building blocks
for new proofs:

- `FPModel`, `gammaValid`, and gamma lemmas form a reusable lower-level error
  model;
- summation, dot-product, matrix-vector, and matrix-product bounds accept the
  same model and gamma guard;
- residual, inverse, orthogonality, LU-error, and normal-equation certificates
  give explicit interfaces between analysis and algorithms;
- vector/matrix norm predicates support downstream norm bounds; and
- iterative-refinement and inverse-solve endpoints expose conclusions that a
  client can restate and specialize.

This is extension suitability in the limited, machine-verified sense that an
external theorem can import and apply the declarations. It does not measure how
much proof effort is required to construct realistic certificates, how stable
the API is under future changes, or how ergonomic large downstream developments
would be.

## Commands, outputs, and timing classification

The exact 30 visibility/client compile command strings are recorded in
[probes/run_commands.tsv](./probes/run_commands.tsv). The harness source is
[probes/run_probes.sh](./probes/run_probes.sh), and broader command/provenance
notes are in [probes/COMMANDS.md](./probes/COMMANDS.md). All probe Lean sources,
logs, `.olean`, and `.ilean` files remain under [probes](./probes).

Each compile used the pattern:

```sh
/usr/bin/time -p -o <time-log> \
  lake env lean -R <probe-source-dir> \
  -o <previously-absent-output>.olean \
  -i <previously-absent-output>.ilean \
  <probe>.lean
```

Timing universe and classification:

- 15 independent visibility compilations: minimum 3.46 s, nearest-rank median
  4.35 s, nearest-rank p95 7.43 s, maximum 7.43 s, sum 67.81 s;
- 15 client compilations: minimum 3.40 s, nearest-rank median 4.32 s,
  nearest-rank p95 6.01 s, maximum 6.01 s, sum 66.09 s; and
- percentile formula: sorted values at index `ceil(p*n)-1`.

The probe outputs were fresh, but dependencies were cached within the isolated
worktree. These numbers measure standalone elaboration/loading in that state;
they are not clean compilation times, module-hotspot evidence, or directly
comparable to a fresh `lake build`.

The probe episode used Lean `4.29.0-rc3` at
`5d86aa4032284a5242470e95fbe25f1ff506763d`, Lake
`5.0.0-src+5d86aa4`, and Mathlib
`e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` on Darwin 25.5.0 arm64.
The isolated worktree remained clean. All artifacts are beneath the ignored
audit root; no Lean source, import, declaration, module, branch, commit, or
remote state was changed.

## Interpretation safeguards and limitations

- Successful compilation proves acceptance by the recorded Lean environment;
  it does not prove faithfulness to Higham or independent mathematical
  correctness.
- A successful `#check` proves visibility only.
- A compiled minimal client theorem is stronger evidence of importability and
  application, but not universal ease of use.
- The sample is predeclared and stratified, not random; 15/15 must not be
  reported as a library-wide 100% consumability rate.
- Most clients are forwarding corollaries. They test elaboration, not unaided
  theorem discovery or substantial new proof construction.
- Direct and transitive dependencies are distinct. The 49 signature rows are
  direct project type edges only; the exhaustive supplemental scan likewise
  reports direct project type pairs only.
- Static import reachability is not an elaborated declaration dependency or
  declaration-visibility graph.
- An import without a logical declaration edge may still be required for
  notation, tactics, macros, attributes, or instances.
- A clean selected type surface does not imply that all public declarations
  avoid implementation detail.
- Public implementation-shaped abstractions are not private/internal leaks,
  but can still create API friction.
- High internal fan-in or reuse would not automatically imply a good external
  interface; these probes provide separate external-consumer evidence.
- No incoming internal project edge would not imply that a public declaration
  is redundant; it may be an intended external endpoint.
- Exact-statement equality would not establish API redundancy; it was not used
  to select or reject these APIs.

## Artifact index

- [Detailed probe report](./probes/PUBLIC_API_PROBES.md)
- [Machine summary and formulas](./probes/summary.json)
- [Full per-probe table](./probes/results.csv)
- [Predeclared sample](./probes/PREDECLARED_SAMPLE.csv)
- [Compiled selected declaration metadata](./probes/selected_declaration_environment_metadata.csv)
- [Compiled direct project type-edge rows](./probes/selected_api_direct_project_type_dependencies.csv)
- [Narrow import closures](./probes/narrow_import_closure.csv)
- [Entry-point reachability excerpt](./probes/entrypoint_reachability_excerpt.csv)
- [Complete 479-entry declaration-exposure table](./current_graph/metrics/public_entrypoint_exposure_all.csv)
- [Public direct-type exposure summary](./current_graph/metrics/public_type_exposure_summary.json)
- [Source-written-public exposure candidates by declaration](./current_graph/metrics/public_type_exposure_declarations.csv)
- [Source-written-public exposure candidate edges](./current_graph/metrics/public_type_exposure_edges.csv)
- [All-environment-public nonpublic type edges](./current_graph/metrics/environment_public_type_nonpublic_exposure_edges.csv)
- [Public exposure validation log](./current_graph/public_type_exposure_validation.log)
- [Probe sources](./probes/src)
- [Probe outputs](./probes/build)
- [Logs and timings](./probes/logs)
- [Commands](./probes/COMMANDS.md)
- [Probe checksums](./probes/SHA256SUMS)
- [Curated library lookup](./_worktree/docs/LIBRARY_LOOKUP.md)
- [Static architecture report](./static_architecture/STATIC_ARCHITECTURE.md)
