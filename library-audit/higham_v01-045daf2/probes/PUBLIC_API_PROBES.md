# NumStability public API consumability probes

## Outcome

At commit `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`, all 15 predeclared
visibility probes and all 15 matching external client theorems compiled through
their selected narrow canonical modules. The exact universes and results are:

| Metric | Numerator | Denominator | Result | Raw evidence |
|---|---:|---:|---:|---|
| Environment-public selected declarations (`is_internal=false`, `is_private=false`) | 15 | 15 selected declarations | 100% | `selected_declaration_environment_metadata.csv`, columns `is_internal`, `is_private` |
| Independent narrow-import `#check` success | 15 | 15 predeclared probes | 100% | `results.csv`, `check_status` |
| Fresh-output external client-theorem success | 15 | 15 predeclared probes | 100% | `results.csv`, `client_status` |
| Selected declarations with compiled bodies | 15 | 15 selected declarations | 100% | `selected_declaration_environment_metadata.csv`, `has_body` |
| Exact source-introducer line confirmed | 15 | 15 selected declarations | 100% | `results.csv`, `source_line_validated` |
| Adjacent source docstring, conservatively detected | 14 | 15 selected declarations | 93.33% | `results.csv`, `has_adjacent_source_docstring` |
| Narrow import with zero `NumStability.Source` modules in static transitive import closure | 15 | 15 selected imports | 100% | `narrow_import_closure.csv`, `reachable_source_modules` |
| Selected API type with no direct private/internal, Source-layer, or compatibility-module project target | 15 | 15 selected declarations | 100% | `results.csv`, three `direct_*_type_dependency_count` columns |
| Direct project type edge to environment-public target | 49 | 49 selected direct project type edges | 100% | `selected_api_direct_project_type_dependencies.csv`, target visibility columns |
| Direct project type edge outside `Source` and static compatibility modules | 49 | 49 selected direct project type edges | 100% | same artifact, target module classification columns |

These are deliberately sample-specific claims. In thesis-safe form: **a
predeclared, stratified sample of 15 source-written canonical APIs spanning
floating-point foundations through high-level solver results was externally
visible and could be applied in separately compiled minimal client theorems
using source-clean narrow imports in the recorded Lean environment.** This is
direct evidence of practical consumability for those probes. It is not a
library-wide usability percentage and does not show how easily an unaided user
would discover the declarations.

## Reproducibility context

- Mode: read-only audit under the `numstability-library-reorganization` metric
  and architecture contracts.
- Worktree commit: `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`.
- Isolated worktree: `_worktree` adjacent to this `probes` directory.
- Worktree source status after probing: clean; `git status
  --porcelain=v1 --untracked-files=all` printed nothing.
- Lean: `4.29.0-rc3`, commit
  `5d86aa4032284a5242470e95fbe25f1ff506763d`, arm64 macOS release.
- Lake: `5.0.0-src+5d86aa4`.
- Mathlib: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.
- Host: Darwin 25.5.0, arm64.
- Probe episode: P01 log mtimes were 2026-09-03 11:40:25 and 11:40:31
  EEST; P02--P15 recorded starts/ends from 2026-09-03 08:41:14Z through
  08:43:19Z (11:41:14--11:43:19 EEST).
- Timing class: every probe target was a fresh `.olean`/`.ilean` output;
  imported dependencies were cached outputs in this isolated worktree. These
  timings are not clean library compile times.
- Schema: `numstability-public-api-probes/v1` in `SCHEMA.md` and
  `summary.json`.

The declaration/import selection was frozen in `PREDECLARED_SAMPLE.csv` before
compilation. One metadata-only correction changed P13's recorded line from the
start of its docstring (84) to its declaration introducer (94); selection,
import, and code did not change. See `MANIFEST_CORRECTIONS.md`.

## Method

The repository's curated `docs/LIBRARY_LOOKUP.md` and executable
`docs/LibraryLookupChecks.lean` supplied the declared public navigation surface.
The exact owning source was then inspected. Each selection was required to be:

1. explicitly introduced in source at the recorded line;
2. environment-public in the compiled metadata;
3. canonical and concept-facing, not under `Source/Higham`, not private or
   internal, and not owned by a static compatibility candidate;
4. importable through the narrow owner module rather than `NumStability`,
   `NumStability.All`, or a broad domain umbrella; and
5. representative of a requested mathematical area.

For each declaration, `*_check.lean` imports only the selected module and runs
a fully qualified `#check`. The separately compiled `*_client.lean` repeats the
`#check`, opens `NumStability`, and states a minimal external `example` that
applies the declaration with its real assumptions. This separation matters:
a `#check` shows visibility; acceptance of the example additionally checks name
resolution, parameter elaboration, assumptions, notation, and result type.

The negative control in `validation/KnownVisibleBadClient_client.lean`
successfully printed its `#check` but failed on an intentionally ill-typed
example (exit 1), confirming that the harness does not treat visibility as
client-theorem success.

## Stratified sample and results

All statuses below are `pass`. Source locations are declaration introducers.

| ID | Area | Declaration | Narrow import | Source | Check s | Client s | Friction |
|---|---|---|---|---|---:|---:|---|
| P01 | FP model/rounding | `NumStability.FPModel.model_basicOp` | `NumStability.FloatingPoint.Model` | `NumStability/FloatingPoint/Model.lean:110` | 3.91 | 6.01 | low |
| P02 | Gamma | `NumStability.gamma_nonneg` | `NumStability.Analysis.Rounding` | `NumStability/Analysis/Rounding.lean:78` | 3.55 | 3.51 | low |
| P03 | Summation | `NumStability.fl_sum_error` | `NumStability.Analysis.Summation.ErrorBounds` | `NumStability/Analysis/Summation/ErrorBounds.lean:468` | 4.28 | 3.88 | moderate |
| P04 | Dot product | `NumStability.dotProduct_error_bound` | `NumStability.Algorithms.DotProduct` | `NumStability/Algorithms/DotProduct.lean:581` | 7.43 | 4.96 | low |
| P05 | Vector norms | `NumStability.complexVecLpNorm_two_ofLp_eq` | `NumStability.Analysis.VectorNorms.Basic` | `NumStability/Analysis/VectorNorms/Basic.lean:88` | 4.13 | 4.20 | moderate |
| P06 | Matrix norms | `NumStability.complexMatrixLpNorm_upper_bound_by_columnMax_lpNorm` | `NumStability.Analysis.MatrixNorms.Lp` | `NumStability/Analysis/MatrixNorms/Lp.lean:2303` | 4.73 | 4.37 | high |
| P07 | Perturbation | `NumStability.forward_error_from_residual` | `NumStability.Analysis.PerturbationTheory` | `NumStability/Analysis/PerturbationTheory.lean:450` | 4.35 | 4.10 | moderate |
| P08 | Matrix multiplication | `NumStability.matMul_error_bound` | `NumStability.Algorithms.MatMul` | `NumStability/Algorithms/MatMul.lean:48` | 4.59 | 4.65 | moderate |
| P09 | Triangular solve | `NumStability.forwardSub_backward_error` | `NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution` | `NumStability/Algorithms/LinearSystems/Triangular/ForwardSubstitution.lean:585` | 3.62 | 3.40 | high |
| P10 | LU factorization | `NumStability.lu_backward_error_gamma` | `NumStability.Algorithms.LU.GaussianElimination` | `NumStability/Algorithms/LU/GaussianElimination.lean:529` | 4.66 | 4.59 | moderate |
| P11 | QR | `NumStability.givensRotation_orthogonal` | `NumStability.Algorithms.LinearSystems.QR.GivensSpec` | `NumStability/Algorithms/LinearSystems/QR/GivensSpec.lean:505` | 4.58 | 4.32 | low |
| P12 | Least squares | `NumStability.RectLSNormalEquations.isLeastSquaresMinimizer` | `NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations` | `NumStability/Algorithms/LinearSystems/LeastSquares/NormalEquations.lean:222` | 4.09 | 4.41 | low |
| P13 | Condition numbers | `NumStability.condOneNumber_ge_scaled_estimator` | `NumStability.Analysis.ConditionEstimatorLowerBound` | `NumStability/Analysis/ConditionEstimatorLowerBound.lean:94` | 4.64 | 3.70 | moderate |
| P14 | Iterative refinement endpoint | `NumStability.one_step_refinement_error_identity` | `NumStability.Algorithms.LinearSystems.IterativeRefinement.Core` | `NumStability/Algorithms/LinearSystems/IterativeRefinement/Core.lean:285` | 3.46 | 3.98 | high |
| P15 | Matrix-inversion endpoint | `NumStability.inversion_residual_bound` | `NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion` | `NumStability/Algorithms/MatrixInversion/Residuals/MatrixInversion.lean:241` | 5.79 | 6.01 | moderate |

The qualitative friction labels are structured reviewer judgments, not an
aggregate score: five low, seven moderate, and three high. Exact assumptions,
helper steps, normalized statement summaries, and rationales are columns in
`results.csv` and `PROBE_METADATA.csv`.

Timing summaries (nearest-rank percentile, `sorted[ceil(p*n)-1]`) were:

| Phase | Min s | Median s | P95 s | Max s | Sum s |
|---|---:|---:|---:|---:|---:|
| Independent `#check` | 3.46 | 4.35 | 7.43 | 7.43 | 67.81 |
| Client theorem | 3.40 | 4.32 | 6.01 | 6.01 | 66.09 |

These wall times mostly reflect loading cached dependency environments and
Lean process overhead. The 15-probe sample is too small and the run order too
uncontrolled for module-performance conclusions.

## What the clients exercised

- P01 applies the unified primitive-operation rounding model, including its
  conditional nonzero-denominator argument for division.
- P02 derives gamma nonnegativity from an explicit `gammaValid` proof.
- P03 obtains the perturbation function promised by sequential summation; the
  public conclusion visibly contains `Fin.foldl`.
- P04 and P08 apply the componentwise dot-product and matrix-product error
  inequalities at their full finite-dimensional types.
- P05 crosses the library's custom `CVec`/`WithLp` representation boundary to
  the Mathlib Euclidean-space norm.
- P06 constructs the custom `MixedSubordinateMatrixBound` conclusion with
  explicit exponent condition `1 <= p`.
- P07 supplies an `IsLeftInverse` and exact system equation to obtain a
  componentwise residual-to-forward-error bound.
- P09 obtains an existential matrix perturbation from explicit diagonal,
  triangularity, and gamma-validity conditions.
- P10 consumes a reusable `LUBackwardError` certificate and obtains an explicit
  perturbation. It does not execute an LU algorithm.
- P11 turns scalar Givens conditions into the custom `IsOrthogonal` result.
- P12 invokes the theorem as a method on a `RectLSNormalEquations` certificate.
- P13 applies the scaled estimator bound for a supplied matrix `B`. This alone
  does not establish that `B` is an inverse of `A`; a textbook inverse-based
  interpretation requires the separate inverse hypothesis/theorems.
- P14 supplies the exact solution, residual, perturbed correction solve, and
  update equations needed for the one-step refinement identity.
- P15 supplies an `IsRightInverse` and gamma guard to obtain a full nested-sum
  residual bound for an inverse-based solve.

Most clients are intentionally thin forwarding corollaries. That is useful for
testing importability and exact application, but it does not measure theorem
search, proof automation, or whether users can synthesize the prerequisite
certificates easily.

## Public type-surface evidence

The compiled declaration graph uses orientation `A -> B` for a direct
reference from consumer `A` to dependency `B`. Restricting to the 15 selected
declarations, `occurs_in_type=true`, and `target_scope=project` produced 49
unique direct project type edges. All 49 targets were environment-public; none
were private/internal, none were owned by `NumStability.Source`, and none were
owned by a static compatibility-candidate module.

This is defensible evidence that these 15 signatures do not directly leak the
three audited categories of project implementation detail. It does not show
that every public signature is clean, and it does not remove the visible API
burden of public implementation-shaped concepts such as `Fin.foldl`, raw
function matrices, `WithLp`, or custom error-certificate predicates.

## Entry points and post-reorganization effects

The repository documents `Core`, `FloatingPoint`, `Analysis`, `Algorithms`,
`Source`, `Source.Higham`, and `All` as primary entry points. `NumStability`
forwards to `All` and is explicitly a package-wide compatibility convenience;
`NumStability.Higham` is the historical compatibility entry point.

Static source-import reachability—not declaration visibility—shows:

| Entry point | Project modules reached incl. entry | Declaration-bearing modules reached | Static declaration starters reached | `Source` modules reached |
|---|---:|---:|---:|---:|
| `NumStability.Core` | 17 | 14 | 818 | 0 |
| `NumStability.FloatingPoint` | 17 | 14 | 1,302 | 0 |
| `NumStability.Analysis` | 728 | 609 | 25,011 | 253 |
| `NumStability.Algorithms` | 1,774 | 1,474 | 43,552 | 1,123 |
| `NumStability.Source` | 1,885 | 1,569 | 45,326 | 1,355 |
| `NumStability.All` | 2,129 | 1,635 | 46,719 | 1,356 |

Thus the broad `Analysis` and `Algorithms` roots are not source-independent
surfaces, even though direct narrow owner modules can be. Two domain examples
are especially useful:

- `NumStability.Algorithms.Summation` reaches 104 project modules, including 25
  `Source` modules. Its own documentation acknowledges that the broad family
  umbrella retains Chapter 4 source declarations.
- `NumStability.Algorithms.LinearSystems.LeastSquares` reaches 153 project
  modules, including 35 `Source` modules, despite describing itself as a
  canonical reusable aggregate. Its narrow `NormalEquations` owner used by P12
  reaches 49 project modules and zero `Source` modules.

Every selected narrow import had zero `Source` modules in its static transitive
closure. This supports the claim that source-neutral consumption is practical
when users know the exact owner. It also identifies residual public-surface
friction: broad exploratory imports blur the canonical/source boundary.
Import reachability is not a logical declaration edge; Source imports may be
present for re-export, notation, instances, attributes, tactics, or other
elaboration effects.

Post-reorganization ownership is not uniform. QR and least-squares owners in
this sample live under `Algorithms.LinearSystems`, while the curated canonical
LU owner remains `Algorithms.LU.GaussianElimination`. All selected declarations
are mostly in the flat `NumStability` namespace despite deep owner-module
paths; P01 is additionally nested under `FPModel`, and P12 under
`RectLSNormalEquations`. The flat namespace makes use short after `open
NumStability`, but filesystem hierarchy alone does not reveal the qualified
declaration name. The curated lookup document materially improves
discoverability.

## Consumability strengths

1. Representative foundations, analysis, and algorithms can all be imported
   without the package-wide convenience root.
2. All sampled declarations are compiled public theorems with bodies and exact
   source introducers, not inferred handwritten APIs from project ownership
   alone.
3. Narrow imports kept all sampled signatures and import closures away from
   Source/Higham and compatibility modules.
4. The signatures form reusable interfaces: gamma guards, inverse and
   factorization certificates, norm predicates, and solver error certificates
   can be passed between client results.
5. High-level refinement and inverse-solve results could be instantiated by an
   external file without opening private/internal namespaces or using
   source-numbered declarations.
6. Fourteen of the 15 sampled theorem introducers have adjacent source
   docstrings with mathematical intent. P05 is the one sampled exception.

## Residual concerns

1. Broad `Analysis`, `Algorithms`, summation, and least-squares aggregates can
   transitively import large Source surfaces. A consumer seeking the clean
   canonical layer must know the narrow owner.
2. Deep module paths coexist with a largely flat declaration namespace and
   some mixed pre/post-reorganization ownership, increasing lookup dependence.
3. Many APIs use raw `Fin n -> ...` function matrices/vectors rather than
   Mathlib `Matrix`, and some norm APIs expose `CVec`, `CMatrix`, `WithLp`,
   `ENNReal`, and custom predicate vocabulary.
4. Gamma validity, positive dimensions, inverse relations, triangularity, and
   nonbreakdown are explicit proof parameters. This is mathematically honest
   and compositional, but high-level client statements can become long.
5. Several strong endpoints consume certificates rather than producing them.
   P10, for example, assumes `LUBackwardError`; this probe does not show how
   conveniently a client obtains that certificate from an executable LU
   routine.
6. Minimal forwarding examples do not test robustness under alternative
   notation, automation, coercions, or larger downstream developments.

## Interpretation safeguards

- Compilation proves acceptance by the recorded Lean environment, not
  faithfulness to Higham or mathematical truth beyond Lean's trusted basis and
  assumptions.
- An externally compiled client application is stronger than `#check`, but it
  demonstrates usability only for that probe.
- Source-import reachability is distinct from elaborated theorem dependency.
- Zero Source modules in an import closure does not mean the module has a small
  dependency footprint: sampled closures ranged from 1 to 49 project modules.
- Absence of private/internal/Source targets in 49 direct type edges is a
  selected-signature result, not a global API theorem.
- High internal reuse or high fan-in would not by itself establish a good
  external interface; these probes address external elaboration separately.
- None of these results audits source-faithfulness.

## Artifacts

- `PREDECLARED_SAMPLE.csv`: fixed declaration/import universe.
- `src/`: all independent visibility and external client Lean sources.
- `build/`: 60 fresh probe output files (`.olean` and `.ilean`).
- `logs/`: stdout/stderr and `/usr/bin/time` records.
- `results.csv`: one fully specified row per API, including assumptions,
  commands, timings, hashes, type-surface counts, and friction.
- `selected_declaration_environment_metadata.csv`: compiled public/body/kind
  evidence for exactly the sample.
- `selected_api_direct_project_type_dependencies.csv`: the 49 raw compiled
  type-edge rows with target classifications.
- `narrow_import_closure.csv`: per-import source-closure evidence.
- `entrypoint_reachability_excerpt.csv`: compact root/domain aggregate evidence.
- `summary.json`: formulas, numerators, denominators, schema, hashes, timings,
  and limitations.
- `run_commands.tsv`, `run_status.tsv`, `COMMANDS.md`: execution record.
- `validation/`, `validation_output/`, `VALIDATION_RESULTS.csv`: positive and
  negative harness controls.
- `SHA256SUMS`: hashes of every stable probe artifact except itself.

The source tree was not edited; no import, declaration, module, commit, or
branch state was changed.
