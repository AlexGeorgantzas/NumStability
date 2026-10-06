# NumStability Library Lookup

This is the human-readable navigation index for the installable NumStability
library. It answers two questions:

1. Which module should be imported for a topic?
2. Where should a new declaration of that kind be placed?

It is intentionally curated rather than exhaustive. Use the module paths below
to enter the relevant subtree, then search that subtree for the exact
declaration. [`LibraryLookupChecks.lean`](LibraryLookupChecks.lean) is the
executable validation companion: it imports representative narrow modules and
checks that their public declarations remain available.

## Fast Path

1. Decide whether the result is reusable mathematics or correspondence to the
   Higham book.
2. Start in `NumStability.Analysis` for general theory,
   `NumStability.Algorithms` for an algorithm or its error analysis,
   `NumStability.FloatingPoint` for the primitive arithmetic model, and
   `NumStability.Source` for source-specific statements.
3. Search by mathematical term or declaration fragment:

   ```sh
   rg -n "term|declaration_fragment" NumStability/Analysis NumStability/Algorithms
   rg -n "theorem_number|source_term" NumStability/Source
   ```

4. Import the narrowest module that owns the declaration. Use an aggregate
   import only for exploration or when the whole domain is genuinely needed.
5. Confirm the import with `lake env lean your_file.lean`.

## Public Entry Points

| Import | Scope |
| --- | --- |
| `NumStability.Core` | Small common foundation used throughout the library. |
| `NumStability.FloatingPoint` | Floating-point models and operation laws. |
| `NumStability.Analysis` | General error, norm, conditioning, perturbation, probability, and operator theory. |
| `NumStability.Algorithms` | Numerical algorithms and their correctness or error results. |
| `NumStability.Source` | Source correspondence for Higham's book. |
| `NumStability.Source.Higham` | All Higham chapter correspondence. |
| `NumStability.All` | All supported library domains. |
| `NumStability` | Package-wide convenience import; currently forwards to `NumStability.All`. |
| `NumStability.Higham` | Historical compatibility entry point; prefer `NumStability.Source.Higham`. |

## Placement Map

| Declaration kind | Canonical subtree | Placement rule |
| --- | --- | --- |
| Primitive floating-point model or operation law | `NumStability/FloatingPoint/` | Put representation-independent arithmetic semantics here. |
| Reusable error definition or theorem | `NumStability/Analysis/` | Keep it independent of one named algorithm or publication. |
| Algorithm, execution model, or algorithm-specific bound | `NumStability/Algorithms/` | Place it with the algorithm family it analyzes. |
| Statement tied to a numbered Higham result | `NumStability/Source/Higham/` | State the source-facing result here and reuse canonical Analysis or Algorithms facts. |
| Imported prerequisite maintained locally | `NumStability/Upstream/` | Use only for an explicitly tracked upstream dependency. |

Do not place a reusable theorem in `Source` merely because a publication uses
it. Conversely, do not erase source-specific hypotheses or notation just to
move a source-correspondence statement into a generic module.

## Foundations And Analysis

| Need | Narrow module | Representative declarations |
| --- | --- | --- |
| Abstract floating-point model and basic operations | `NumStability.FloatingPoint.Model` | `FPModel`, `BasicOp` |
| Operation laws | `NumStability.FloatingPoint.OperationLaws` | Laws for model operations |
| Concrete formats and IEEE-style behavior | `NumStability.Analysis.FloatingPointArithmetic.Format` | `FloatingPointFormat` declarations |
| Unit-roundoff and gamma calculus | `NumStability.Analysis.Rounding` | `gamma`, `gammaValid` |
| Scalar error measures | `NumStability.Analysis.Error.Measures.All` | `absError`, `relError` |
| Stability and condition-number interfaces | `NumStability.Analysis.Stability` | `normwiseBackwardErrorBoundedVec`, `normwiseConditionNumberBoundedVec` |
| Vector norms | `NumStability.Analysis.VectorNorms` | `complexVecLpNorm` and vector-norm theory |
| Matrix norms | `NumStability.Analysis.MatrixNorms` | `complexMatrixLpNorm` and matrix-norm theory |
| Rectangular rank factorizations | `NumStability.Analysis.SingularValues.RectangularRankFactorization` | `RectRankFactorization`, orthonormal-completion infrastructure |
| Rectangular right-Gram SVD analysis | `NumStability.Analysis.SingularValues.RectangularGram` | `rectRightGram`, `rectRightGramBasisSingularValue` |
| Residual and perturbation bounds | `NumStability.Analysis.PerturbationTheory` | `forward_error_from_residual`, `oettli_prager` |
| Linear operators and spectra | `NumStability.Analysis.LinearOperators` | Operator, Schur, pseudospectral, and power theory |
| Schur theory | `NumStability.Analysis.LinearOperators.Schur` | `schur_triangulation` |
| Pseudospectral power bounds | `NumStability.Analysis.LinearOperators.Pseudospectra.PowerBounds` | `resolventPseudospectralRadius` |
| Matrix-power limits and semiconvergence | `NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.All` | `matPow_tendsto_zero_of_spectralRadius_lt_one` |
| Probability support | `NumStability.Analysis.Probability` | Probability lemmas used by statistical rounding and distributional analysis |
| Sample-variance statistics | `NumStability.Analysis.Statistics.SampleVariance.All` | Sample-variance definitions and results |
| Standard test matrices | `NumStability.Analysis.TestMatrices` | Hilbert, Pascal, Cauchy, companion, and related matrices |

## Algorithms

| Need | Narrow or domain module | Representative declarations |
| --- | --- | --- |
| Recursive and compensated summation | `NumStability.Algorithms.Summation` | `fl_recursiveSum`, `fl_sum_error` |
| Summation trees | `NumStability.Algorithms.Summation` | `SumTree.exactSum` |
| Dot products | `NumStability.Algorithms.DotProduct` | `fl_dotProduct`, `dotProduct_error_bound` |
| No-guard dot-product analysis | `NumStability.Algorithms.Arithmetic.DotProduct.NoGuard` | No-guard execution and bounds |
| Polynomial root-product evaluation | `NumStability.Algorithms.PolynomialEvaluation.RootProduct` | `rootProductEval` |
| Polynomial derivative evaluation | `NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds` | Horner derivative error bounds |
| Matrix-vector multiplication | `NumStability.Algorithms.MatVec` | `matVec_backward_error` |
| Matrix multiplication | `NumStability.Algorithms.MatMul` | `matMul_error_bound` |
| Gaussian elimination and LU factorization | `NumStability.Algorithms.LU.GaussianElimination` | `LUBackwardError`, `lu_backward_error_gamma` |
| Triangular systems | `NumStability.Algorithms.LinearSystems.Triangular` | `fl_forwardSub`, `forwardSub_backward_error` |
| LU-based linear solves | `NumStability.Algorithms.LinearSystems.LU` | LU solve and block-LU families |
| Cholesky solves | `NumStability.Algorithms.LinearSystems.Cholesky` | `CholeskyBackwardError`, Cholesky perturbation results |
| QR methods | `NumStability.Algorithms.LinearSystems.QR` | `givensRotation`, `householderScaleAlt` |
| Least squares | `NumStability.Algorithms.LinearSystems.LeastSquares` | `RectLSNormalEquations` and QR, normal-equation, refinement results |
| Minimum-norm underdetermined solves | `NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.Executor.Core` | Minimum-norm execution model |
| Symmetric-indefinite systems | `NumStability.Algorithms.LinearSystems.SymmetricIndefinite` | `BlockLDLTSpec`, `bunchParlettAlpha` |
| Iterative refinement | `NumStability.Algorithms.LinearSystems.IterativeRefinement.Core` | `fl_residual`, `one_step_refinement_error_identity` |
| Stationary iteration and semiconvergence | `NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.All` | Stationary-iteration convergence results |
| Matrix inversion | `NumStability.Algorithms.MatrixInversion` | Residual and inversion-error analysis |
| Matrix equations | `NumStability.Algorithms.MatrixEquations` | Sylvester and Lyapunov equations |
| One-norm estimation | `NumStability.Algorithms.NormEstimation.OneNorm.LAPACK.Basic` | `lapackNormEstimator` |
| p-norm power methods | `NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod` | `Ch15.PNormPair` |
| Matrix powers | `NumStability.Algorithms.MatrixPowers` | Computation and error bounds for powers |

## Higham Source Map

Each chapter aggregate below is importable. Import the chapter aggregate to
explore one chapter, then follow its imports to the narrow module that owns the
needed declaration.

| Chapter | Import | Main topics represented |
| --- | --- | --- |
| 1 | `NumStability.Source.Higham.Chapter01` | Error measures, motivating examples, nonrandom rounding |
| 2 | `NumStability.Source.Higham.Chapter02` | Floating-point systems, rounding, FMA, underflow |
| 3 | `NumStability.Source.Higham.Chapter03` | Products of local errors and gamma bounds |
| 4 | `NumStability.Source.Higham.Chapter04` | Summation and compensated summation |
| 5 | `NumStability.Source.Higham.Chapter05` | Polynomial evaluation |
| 6 | `NumStability.Source.Higham.Chapter06` | Vector and matrix norms |
| 7 | `NumStability.Source.Higham.Chapter07` | Conditioning and perturbation |
| 8 | `NumStability.Source.Higham.Chapter08` | Triangular systems |
| 9 | `NumStability.Source.Higham.Chapter09` | Gaussian elimination and LU factorization |
| 10 | `NumStability.Source.Higham.Chapter10` | Cholesky and positive semidefinite problems |
| 11 | `NumStability.Source.Higham.Chapter11` | Symmetric-indefinite factorization |
| 12 | `NumStability.Source.Higham.Chapter12` | Iterative refinement |
| 13 | `NumStability.Source.Higham.Chapter13` | Block LU factorization |
| 14 | `NumStability.Source.Higham.Chapter14` | Matrix inversion |
| 15 | `NumStability.Source.Higham.Chapter15` | Norm and condition estimation |
| 16 | `NumStability.Source.Higham.Chapter16` | Sylvester and Lyapunov equations |
| 17 | `NumStability.Source.Higham.Chapter17` | Stationary iteration and semiconvergence |
| 18 | `NumStability.Source.Higham.Chapter18` | Matrix powers and pseudospectra |
| 19 | `NumStability.Source.Higham.Chapter19` | QR factorization |
| 20 | `NumStability.Source.Higham.Chapter20` | Least-squares problems |
| 21 | `NumStability.Source.Higham.Chapter21` | Underdetermined and minimum-norm systems |
| 22 | `NumStability.Source.Higham.Chapter22` | Vandermonde and Hermite systems |
| 23 | `NumStability.Source.Higham.Chapter23` | Fast matrix multiplication |
| 24 | `NumStability.Source.Higham.Chapter24` | FFT and circulant systems |
| 25 | `NumStability.Source.Higham.Chapter25` | Eigenvalue and nonlinear-system conditioning |
| 26 | `NumStability.Source.Higham.Chapter26` | Cubic roots, interval methods, direct search |
| 27 | `NumStability.Source.Higham.Chapter27` | Software arithmetic, complex division, scaled norms |
| 28 | `NumStability.Source.Higham.Chapter28` | Test matrices and random matrices |

Representative source-facing declarations include
`Lemma66.lemma66_a_op2_le`,
`higham12_3_exact_one_step_residual_bound`,
`higham16_problem16_2_lyapunov_spd_unique`,
`higham22_vandermonde_det_ne_zero_iff`, and
`higham24Radix2FFT_eq_dftApply`.

## Local Prerequisites

The `NumStability/Upstream/Lindemann/` subtree contains the locally maintained
Lindemann prerequisite used by library results; it is not a general
source-coverage area. Import a required leaf such as
`NumStability.Upstream.Lindemann.Basic`, not the directory name.

## Verify A Lookup

Run the executable companion after changing imports, public names, or this map:

```sh
lake env lean docs/LibraryLookupChecks.lean
```

For an exact owner, search declarations rather than guessing from an aggregate
import:

```sh
rg -n "^(def|abbrev|structure|class|theorem|lemma) .*NAME" NumStability
```

The filesystem and successful Lean imports are authoritative. This document is
the fast index, not a substitute for checking the declaration's full type and
its direct imports.
