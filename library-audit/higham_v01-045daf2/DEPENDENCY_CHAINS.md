# Concrete dependency chains

Schema: `numstability-representative-dependency-chains/1.1.0`. Every arrow is `consumer -> dependency`: the declaration on the left directly references the declaration on the right in its elaborated type and/or body. Every adjacent edge below was validated against the compiled raw graph; start-to-later-node relationships are transitive when the path has more than one edge.

These paths establish formal reuse and compositional typechecking in the recorded Lean environment. They do not independently establish faithfulness to Higham, correctness of an informal translation, numerical sharpness, or universal API convenience.

## Stratified summary

| ID | Area | Edges | Modules | Layers | Evidence |
|---|---|---:|---:|---|---|
| C01 | dot products / summation | 1 | 2 | Algorithms;Analysis | short direct cross-module and cross-layer reuse |
| C02 | triangular solves / rounding | 2 | 3 | Algorithms;Analysis;FloatingPoint | cross-layer chain through a broad-fan-out theorem |
| C03 | matrix multiplication | 4 | 5 | Algorithms;Analysis;FloatingPoint | multi-module Algorithms -> Analysis -> FloatingPoint chain |
| C04 | matrix inversion | 5 | 5 | Algorithms;Analysis;FloatingPoint | deep algorithm-to-rounding chain |
| C05 | QR factorization and solve | 14 | 7 | Algorithms;FloatingPoint | deep 14-edge multi-module algorithmic chain |
| C06 | LU factorization and solves / Higham Chapters 9 and 12 | 7 | 3 | Analysis;Source | cross-chapter bridge plus seven-edge proof spine |
| C07 | polynomial derivative evaluation / Chapters 22 and 5 provenance | 2 | 3 | Algorithms;Analysis;Source | Source -> Algorithms -> Analysis reuse |
| C08 | Cholesky factorization and solve | 5 | 3 | Algorithms;Analysis | factorization-solver composition across modules |
| C09 | least squares | 2 | 1 | Algorithms | high-level endpoint with independent lower-result branches |
| C10 | condition estimation | 1 | 2 | Algorithms;Analysis | direct cross-module use and layer-direction review case |
| C11 | matrix and vector norms | 2 | 2 | Analysis | cross-module Analysis-layer reuse |
| C12 | FFT and circulant solvers / Higham Chapter 24 | 14 | 5 | Analysis;FloatingPoint;Source | deep Source -> Analysis -> FloatingPoint chain |

The deepest high-level endpoint spine is C05: it composes a QR-solve bound with a separate right-hand-side/back-substitution proof branch and a 14-edge factorization/Householder/norm/rounding path. C06 is the strongest thesis-relevant cross-chapter representative: a CrossChapter-owned theorem has independent direct branches into the Chapter 9 factorization development and the Chapter 12 solver-bound predicate. The declaration-level thesis figure therefore presents C06 for its explicit Chapter 9/12 bridge; that selection does not imply that C06 is deeper than C05.

## Compact downstream-reach table

Counts are for the chain's first declaration. Domain and chapter names are given in full in `representative_dependency_chains.csv`; this table reports their counts to remain readable.

| ID | Downstream declarations | Downstream modules | Downstream domains | Downstream chapters |
|---|---:|---:|---:|---:|
| C01 | 2200 | 93 | 14 | 14 |
| C02 | 2184 | 108 | 11 | 11 |
| C03 | 297 | 29 | 8 | 7 |
| C04 | 0 | 0 | 0 | 0 |
| C05 | 0 | 0 | 0 | 0 |
| C06 | 0 | 0 | 0 | 0 |
| C07 | 0 | 0 | 0 | 0 |
| C08 | 0 | 0 | 0 | 0 |
| C09 | 226 | 17 | 3 | 2 |
| C10 | 3 | 2 | 1 | 2 |
| C11 | 13 | 2 | 1 | 1 |
| C12 | 0 | 0 | 0 | 0 |

## Chapter 9 / Chapter 12 re-check

No direct/transitive consumer-to-dependency path from a Chapter12-owned declaration to a Chapter09-owned declaration was found. The verified LU/solver bridge is owned by Source.Higham.CrossChapter.LUSolverWeights.

## C01: Dot-product proof directly reuses the summation error theorem

Why this is reuse: The dot-product forward-error proof has a body edge to the separately owned summation error result.

```text
NumStability.dotProduct_error_bound
  -> NumStability.fl_sum_error_init
```

What it does not establish: One direct reference does not establish that the statement is faithful to Higham or that the API is universally convenient.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Algorithms.DotProduct` | `NumStability.Analysis.Summation.ErrorBounds` |

## C02: Triangular-solve error proof reaches the reusable gamma foundation

Why this is reuse: The algorithmic backward-error result consumes gamma_nonneg, which itself consumes the floating-point model's unit-roundoff nonnegativity law.

```text
NumStability.forwardSub_backward_error
  -> NumStability.gamma_nonneg
  -> NumStability.FPModel.u_nonneg
```

What it does not establish: High fan-in measures internal consumption, not user-interface quality or mathematical-source faithfulness.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution` | `NumStability.Analysis.Rounding` |
| 2 | body | `NumStability.Analysis.Rounding` | `NumStability.FloatingPoint.Model` |

## C03: Matrix multiplication composes mat-vec, dot-product, summation, and rounding results

Why this is reuse: Each adjacent compiled edge shows an algorithmic level reusing the immediately lower error-analysis result, ultimately reaching the primitive addition model.

```text
NumStability.matMul_error_bound
  -> NumStability.matVec_error_bound
  -> NumStability.dotProduct_error_bound
  -> NumStability.fl_sum_error_init
  -> NumStability.FPModel.model_add
```

What it does not establish: This selected spine does not enumerate every premise or branch used by the matrix-multiplication theorem.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Algorithms.MatMul` | `NumStability.Algorithms.MatVec` |
| 2 | body | `NumStability.Algorithms.MatVec` | `NumStability.Algorithms.DotProduct` |
| 3 | body | `NumStability.Algorithms.DotProduct` | `NumStability.Analysis.Summation.ErrorBounds` |
| 4 | body | `NumStability.Analysis.Summation.ErrorBounds` | `NumStability.FloatingPoint.Model` |

## C04: Matrix-inversion residual bound reuses mat-vec and dot-product stability

Why this is reuse: The high-level inversion residual result is connected by actual proof edges to reusable mat-vec, dot-product, summation, and primitive-rounding results.

```text
NumStability.inversion_residual_bound
  -> NumStability.matVec_backward_error
  -> NumStability.dotProduct_backward_stable_x
  -> NumStability.dotProduct_backward_error
  -> NumStability.fl_sum_error_init
  -> NumStability.FPModel.model_add
```

What it does not establish: The path proves syntactic proof-term reuse in this elaborated environment, not numerical sharpness or Higham fidelity.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion` | `NumStability.Algorithms.MatVec` |
| 2 | body | `NumStability.Algorithms.MatVec` | `NumStability.Algorithms.DotProduct` |
| 3 | body | `NumStability.Algorithms.DotProduct` | `NumStability.Algorithms.DotProduct` |
| 4 | body | `NumStability.Algorithms.DotProduct` | `NumStability.Analysis.Summation.ErrorBounds` |
| 5 | body | `NumStability.Analysis.Summation.ErrorBounds` | `NumStability.FloatingPoint.Model` |

## C05: QR solve bound descends through factorization, Householder, norm, and square-root analyses

Why this is reuse: The endpoint consumes a factorization-error branch whose compiled path crosses QRSolve, Householder QR, matrix-step, one-step, reflector, norm, and floating-point model modules.

```text
NumStability.fl_householderQR_solve_backward_error_gammaHigham_closedInputBounds_of_global_gammaValid
  -> NumStability.fl_householderQR_R_frobNorm_le_gammaHigham_of_global_gammaValid
  -> NumStability.fl_householderQR_witness_explicit_backward_error_gammaHigham_of_global_gammaValid
  -> NumStability.fl_householderQR_witness_explicit_backward_error_of_global_gammaValid
  -> NumStability.fl_householderQRPanel_R_explicit_backward_error
  -> NumStability.fl_householder_first_column_panel_step_error
  -> NumStability.fl_householderConstructApply_matrix_step_error_rect
  -> NumStability.fl_householderConstructApply_appError
  -> NumStability.fl_householderVectorError
  -> NumStability.fl_householderConstructionError
  -> NumStability.fl_householderVector_zero_relative_error
  -> NumStability.fl_householderScale_relative_error
  -> NumStability.fl_norm2_relative_error
  -> NumStability.fl_norm2_relative_error_sqrt_factor
  -> NumStability.FPModel.model_sqrt
```

What it does not establish: It is one dependency spine and does not alone establish completeness of the QR development or external usability.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Algorithms.LinearSystems.QR.QRSolve` | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` |
| 2 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` |
| 3 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` |
| 4 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` |
| 5 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` |
| 6 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` | `NumStability.Algorithms.LinearSystems.QR.HouseholderMatrixStep` |
| 7 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderMatrixStep` | `NumStability.Algorithms.LinearSystems.QR.HouseholderOneStep` |
| 8 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderOneStep` | `NumStability.Algorithms.LinearSystems.QR.HouseholderReflector` |
| 9 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderReflector` | `NumStability.Algorithms.LinearSystems.QR.HouseholderReflector` |
| 10 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderReflector` | `NumStability.Algorithms.LinearSystems.QR.HouseholderReflector` |
| 11 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderReflector` | `NumStability.Algorithms.LinearSystems.QR.HouseholderReflector` |
| 12 | body | `NumStability.Algorithms.LinearSystems.QR.HouseholderReflector` | `NumStability.Algorithms.Norm2` |
| 13 | body | `NumStability.Algorithms.Norm2` | `NumStability.Algorithms.Norm2` |
| 14 | body | `NumStability.Algorithms.Norm2` | `NumStability.FloatingPoint.Model` |

Additional direct branches:

- `NumStability.fl_householderQR_solve_backward_error_gammaHigham_closedInputBounds_of_global_gammaValid` -> `NumStability.fl_householderQR_solve_backward_error_gammaHigham_rhsClosedGrowth_of_global_gammaValid` (body): independent right-hand-side/back-substitution proof branch.

## C06: CrossChapter LU-solver bridge connects Chapter 12 semantics to Chapter 9 Doolittle bounds

Why this is reuse: The CrossChapter theorem has a body edge into the Chapter 9 Doolittle closure and a separate type/body edge to the Chapter 12 SolverWBound predicate; the Chapter 9 branch then reaches shared gamma calculus.

```text
NumStability.higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source
  -> NumStability.higham9_4_rectRoundedLoop_square_lu_solve_backward_error_source
  -> NumStability.higham9_3_rectRoundedLoop_square_to_LUBackwardError_source
  -> NumStability.higham9_3_rectRoundedLoop_source_backward_error
  -> NumStability.higham9_2_rectRoundedLoopSourceCertificate
  -> NumStability.higham9_2_rectFlDoolittleLEntry_source_residual_abs_le
  -> NumStability.higham9_2_flMulSubFold_div_source_residual_abs_le
  -> NumStability.gamma_mul
```

What it does not establish: There is no path from a Chapter12-owned declaration to a Chapter09-owned declaration; the genuine composition is intentionally owned by CrossChapter, and this says nothing by itself about book faithfulness.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Source.Higham.CrossChapter.LUSolverWeights.Doolittle` | `NumStability.Source.Higham.Chapter09.DoolittleClosure` |
| 2 | body | `NumStability.Source.Higham.Chapter09.DoolittleClosure` | `NumStability.Source.Higham.Chapter09.DoolittleClosure` |
| 3 | body | `NumStability.Source.Higham.Chapter09.DoolittleClosure` | `NumStability.Source.Higham.Chapter09.DoolittleClosure` |
| 4 | body | `NumStability.Source.Higham.Chapter09.DoolittleClosure` | `NumStability.Source.Higham.Chapter09.DoolittleClosure` |
| 5 | body | `NumStability.Source.Higham.Chapter09.DoolittleClosure` | `NumStability.Source.Higham.Chapter09.DoolittleClosure` |
| 6 | body | `NumStability.Source.Higham.Chapter09.DoolittleClosure` | `NumStability.Source.Higham.Chapter09.DoolittleClosure` |
| 7 | body | `NumStability.Source.Higham.Chapter09.DoolittleClosure` | `NumStability.Analysis.Rounding` |

Additional direct branches:

- `NumStability.higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source` -> `NumStability.higham12_1_SolverWBound` (both): Chapter 12 solver-bound predicate branch.
- `NumStability.higham12_6_lu_solve_SolverWBound` -> `NumStability.higham9_4_lu_solve_backward_error` (body): parallel abstract-factorization bridge.
- `NumStability.higham12_6_lu_solve_SolverWBound` -> `NumStability.higham12_1_SolverWBound` (both): parallel bridge's Chapter 12 predicate branch.

## C07: Chapter 22 refinement reuses a canonical derivative-evaluation error bound

Why this is reuse: A Chapter 22 source-layer theorem directly delegates to the algorithmic derivative error bound associated by name with Higham 5.7, which consumes the shared gamma theorem.

```text
NumStability.Ch22B.ch22b_horner_derivative_error_via_higham5_7
  -> NumStability.fl_hornerDerivativeDesc_snd_forward_error_bound_coupled
  -> NumStability.gamma_nonneg
```

What it does not establish: The target's source-labelled declaration name is a discoverability/ownership review signal; it does not make the result redundant.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Source.Higham.Chapter22.Section03.RealRefinement` | `NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds` |
| 2 | body | `NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds` | `NumStability.Analysis.Rounding` |

## C08: Cholesky solve stability reuses triangular solve and gamma results

Why this is reuse: The SPD Cholesky solve endpoint is proved through the generic Cholesky solve bound and then the separately owned back-substitution analysis and gamma product lemma.

```text
NumStability.cholesky_solve_spd_backward_stable
  -> NumStability.cholesky_solve_backward_error
  -> NumStability.cholesky_solve_backward_error_expanded
  -> NumStability.backSub_backward_error
  -> NumStability.backSub_row_tight
  -> NumStability.gamma_mul
```

What it does not establish: This path does not show that every Cholesky result is reused or that all constants are source-faithful.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic` | `NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic` |
| 2 | body | `NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic` | `NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic` |
| 3 | body | `NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic` | `NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution` |
| 4 | body | `NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution` | `NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution` |
| 5 | body | `NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution` | `NumStability.Analysis.Rounding` |

## C09: Normal equations endpoint composes orthogonality and norm nonnegativity branches

Why this is reuse: The minimizer theorem directly consumes the normal-equation orthogonality theorem; a separate body edge consumes vecNorm2Sq_nonneg in the matrix-algebra layer.

```text
NumStability.RectLSNormalEquations.isLeastSquaresMinimizer
  -> NumStability.RectLSNormalEquations.residual_orthogonal
  -> NumStability.RectLSNormalEquations.iff_residual_orthogonal
```

What it does not establish: The two branches document composition for this proof only, not optimal API design.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations` | `NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations` |
| 2 | body | `NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations` | `NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations` |

Additional direct branches:

- `NumStability.RectLSNormalEquations.isLeastSquaresMinimizer` -> `NumStability.vecNorm2Sq_nonneg` (body): independent squared-norm nonnegativity branch.

## C10: Condition-number theorem consumes the LAPACK estimator lower bound

Why this is reuse: The compiled proof body directly uses the separately owned LAPACK estimator bound.

```text
NumStability.condOneNumber_ge_scaled_estimator
  -> NumStability.lapackNormEstimator_lower_bound
```

What it does not establish: Because an Analysis-owned theorem depends on an Algorithms-owned theorem, this is also evidence of a residual edge against the intended layer direction, not an architectural strength by itself.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Analysis.ConditionEstimatorLowerBound` | `NumStability.Algorithms.CondEstimation` |

## C11: Matrix norm bound reuses vector norm inequalities and definitions

Why this is reuse: The matrix-norm theorem consumes a vector-norm inequality, which in turn references the canonical complex vector p-norm definition.

```text
NumStability.complexMatrixLpNorm_upper_bound_by_columnMax_lpNorm
  -> NumStability.complexVecOneNorm_le_card_rpow_mul_complexVecLpNorm
  -> NumStability.complexVecLpNorm
```

What it does not establish: This local chain does not quantify whether the norm API is discoverable to external users.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Analysis.MatrixNorms.Lp` | `NumStability.Analysis.VectorNorms.Basic` |
| 2 | both | `NumStability.Analysis.VectorNorms.Basic` | `NumStability.Analysis.VectorNorms.Basic` |

## C12: Chapter 24 circulant/FFT endpoint reaches complex arithmetic and primitive rounding

Why this is reuse: The Chapter 24 endpoint's proof spine successively reuses structured-stability results, a diagonal-solve specification, reusable complex arithmetic error lemmas, and the primitive floating-point addition law.

```text
NumStability.higham24_theorem24_3_literal_forward_error_multiple_kappa_u
  -> NumStability.higham24_theorem24_3_literal_quadraticRemainder
  -> NumStability.higham24_theorem24_3_literal_firstOrder
  -> NumStability.higham24_theorem24_3_literal_exactRadii
  -> NumStability.higham24_literalGeneratorPerturbation_norm_le
  -> NumStability.higham24_literalScalingInverse_norm_le
  -> NumStability.higham24_diagonalSolveRelativeError_spec
  -> NumStability.fl_complexDiv_rel_error_model
  -> NumStability.fl_complexDiv_error_bound
  -> NumStability.fl_complexDiv_normSq_error_le
  -> NumStability.fl_complexDiv_im_exact_error_le_gamma4
  -> NumStability.fl_complexDiv_im_error_le_gamma4
  -> NumStability.fl_complexDivDen_error_le_gamma2
  -> NumStability.fl_mul_add_error_le_gamma2
  -> NumStability.FPModel.model_add
```

What it does not establish: The path is evidence of integration, not a validation of Chapter 24 translation accuracy.

| Step | Edge class | Consumer module | Dependency module |
|---:|---|---|---|
| 1 | body | `NumStability.Source.Higham.Chapter24.CirculantForwardError` | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` |
| 2 | body | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` |
| 3 | body | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` |
| 4 | body | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` |
| 5 | body | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` |
| 6 | body | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` | `NumStability.Source.Higham.Chapter24.RoundedDiagonalSolve` |
| 7 | body | `NumStability.Source.Higham.Chapter24.RoundedDiagonalSolve` | `NumStability.Analysis.ComplexArithmetic` |
| 8 | body | `NumStability.Analysis.ComplexArithmetic` | `NumStability.Analysis.ComplexArithmetic` |
| 9 | body | `NumStability.Analysis.ComplexArithmetic` | `NumStability.Analysis.ComplexArithmetic` |
| 10 | body | `NumStability.Analysis.ComplexArithmetic` | `NumStability.Analysis.ComplexArithmetic` |
| 11 | body | `NumStability.Analysis.ComplexArithmetic` | `NumStability.Analysis.ComplexArithmetic` |
| 12 | body | `NumStability.Analysis.ComplexArithmetic` | `NumStability.Analysis.ComplexArithmetic` |
| 13 | body | `NumStability.Analysis.ComplexArithmetic` | `NumStability.Analysis.ComplexArithmetic` |
| 14 | body | `NumStability.Analysis.ComplexArithmetic` | `NumStability.FloatingPoint.Model` |

## Raw evidence

`representative_chain_nodes.csv` is the normative per-node table satisfying the declaration-kind, module, current file/line, layer, chapter/source-item, mathematical-role, normalized-statement, authorship, and downstream-reach fields. `representative_chain_edges.csv` is the normative per-edge table for direct/transitive status and type/body/both flags. `representative_chain_raw_compiled_rows.csv` preserves the exact selected rows and data-row numbers from the validated compiled raw graph. `representative_chain_branch_edges.csv` records the independent proof branches used in the interpretation.
