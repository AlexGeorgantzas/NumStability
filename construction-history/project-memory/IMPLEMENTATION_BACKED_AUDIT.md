# Implementation-Backed Stability Audit

Date: 2026-06-01

This is a working audit for the end-to-end rebuild.  It classifies whether each
algorithmic stability result is currently derived from a concrete rounded
`fl_*` implementation or only from a supplied contract/specification.

This file is internal thesis/project material.  It should not be copied into
benchmark workspaces.

## Standard

Target proof chain:

```text
FPModel primitives
-> concrete rounded fl_* algorithm
-> theorem proving the algorithm satisfies its contract
-> final stability theorem using that contract
```

Allowed assumptions:

- primitive `FPModel` rounding axioms, such as `model_add`, `model_mul`,
  `model_div`, and `model_sqrt`;
- mathematical hypotheses required by the theorem, such as nonsingularity,
  diagonal dominance, positive definiteness, or `gammaValid`.

Gap pattern:

- a high-level theorem takes `hLU`, `hChol`, `hSeq`, `hGram`, `hSolve`, or
  similar error contracts as inputs;
- the library has no separate theorem proving that a concrete rounded algorithm
  satisfies that contract.

Important source rule: always compare the proof boundary with the original
source.  If Higham or another source proves a lower-level bound, the Lean
rebuild should aim to prove that lower-level bound instead of permanently
taking it as a high-level assumption.  The QR/Householder gap in Higham
Chapter 18 is the motivating example.

## Status Vocabulary

- `implementation-backed`: concrete rounded algorithm and bridge theorem exist.
- `mostly implementation-backed`: the core algorithm is implementation-backed,
  but documentation/source checking or small bridges remain.
- `mixed`: some concrete rounded stages exist, but a major contract is still
  assumed.
- `contract/specification-transfer`: theorem packages or derives consequences
  from a supplied contract; not end-to-end.
- `exact/support`: exact algebra or perturbation infrastructure; no rounded
  algorithm is expected in that file.
- `unknown`: needs a deeper file-level read before classification.

## Foundation Layer

| Area | Files | Current Status | Notes |
| --- | --- | --- | --- |
| Floating-point model | `FP/Model.lean` | exact/support | Axiomatic Higham-style primitive model. This is the intended bottom assumption. |
| Gamma/rounding algebra | `Analysis/Rounding.lean`, `Analysis/Error.lean` | exact/support | Supports accumulation proofs. Check source references when touched. |
| Summation fold lemmas | `Analysis/Summation.lean`, `Analysis/SubtractionFold.lean` | mostly implementation-backed | Proves fold-level errors from repeated `fp.fl_add` / subtraction. |
| Stability predicates | `Analysis/Stability.lean` | exact/support | Definitions only; no algorithm implementation expected. |
| Matrix algebra/norms | `Analysis/MatrixAlgebra.lean` | exact/support | Exact matrix and norm infrastructure; should use Mathlib where possible. |

Audit update, 2026-06-01:

- Phase 1 foundation audit is complete.
- No implementation-backed gap was found in the foundation layer because these
  files are either primitive model assumptions, exact algebra, or fold lemmas
  derived from primitive `FPModel` operations.
- Documentation was tightened in `FP/Model.lean` and `Analysis/Rounding.lean`:
  `fl_add_zero` is marked as an extra exactness hypothesis, and `gammaValid` is
  described as model-parametric rather than IEEE-specific.

## Scalar And Vector Kernels

| Module | Rounded Implementation | Contract/Theorem | Status | Source/Boundary | Next Action |
| --- | --- | --- | --- | --- | --- |
| `RecursiveSum.lean` | `fl_recursiveSum`, `fl_partialSums` | `recursiveSum_backward_error`, forward/running bounds | implementation-backed | Higham Ch. 4 recursive summation | Verify source labels and use as summation baseline. |
| `PairwiseSum.lean` | `fl_pairwiseSum` | `pairwiseSum_backward_error`, forward bound | implementation-backed | Higham Ch. 4 pairwise summation | Verify source labels and dependency on tree/summation lemmas. |
| `SumTree.lean` | `SumTree.eval` uses `fp.fl_add` | tree backward/forward error theorems | implementation-backed | Higham Algorithm 4.1, eqs. 4.2-4.6 | Keep as generic summation framework. |
| `DotProduct.lean` | `fl_dotProduct` | `dotProduct_backward_error`, forward/stability results | implementation-backed | Higham Ch. 3 dot product error analysis | Positive template for the rebuild. |
| `OuterProduct.lean` | `fl_outerProduct` | outer-product error/backward results | implementation-backed | Higham-style elementwise multiplication model | Source-check exact theorem statement. |
| `Norm2.lean` | `fl_norm2Sq`, `fl_norm2` | `fl_norm2Sq_backward_error`, `fl_norm2Sq_relative_error`, `fl_norm2_relative_error_sqrt_factor`, `fl_norm2_relative_error` | implementation-backed | Uses dot product plus `model_sqrt`; needed for Householder | Reuse as the source-style norm bridge for Householder construction. |

Audit update, 2026-06-01:

- Phase 2 scalar/vector audit is complete.
- `RecursiveSum`, `PairwiseSum`, `SumTree`, `DotProduct`, and `OuterProduct`
  are implementation-backed relative to `FPModel`.
- `Norm2` is implementation-backed as a low-level rounded norm kernel, but the
  Householder-specific vector construction theorem remains future work.
- Later QR rebuild work added the Householder-facing norm bridges:
  `weighted_sum_relative_error_nonneg`, `fl_norm2Sq_relative_error`,
  `fl_norm2_relative_error_sqrt_factor`, `sqrt_one_add_sub_one_abs_le_abs`,
  `sqrt_one_add_mul_roundoff_gamma`, and `fl_norm2_relative_error`.  These
  prove the source step `fl(x^T x) = (1+θ_n)x^T x` and collapse the rounded
  square-root factor into the source-style norm result
  `fl(||x||_2) = ||x||_2(1+θ_{n+1})`.
- `OuterProduct.lean` should be read carefully: the componentwise forward bound
  is implementation-backed, and the later perturbation theorem is only row-wise.
  It is not a global backward-stability result for the rank-one outer-product
  algorithm, in agreement with Higham's discussion after equation (3.6).

## Basic Matrix Kernels

| Module | Rounded Implementation | Contract/Theorem | Status | Source/Boundary | Next Action |
| --- | --- | --- | --- | --- | --- |
| `MatVec.lean` | `fl_matVec` | `matVec_backward_error`, `matVec_error_bound` | implementation-backed | Derived from dot product | Confirm exact spec uses Mathlib-compatible notation where practical. |
| `MatMul.lean` | `fl_matMul` | `matMul_error_bound`, `matMul_backward_error_col` | implementation-backed | Derived from dot product | Confirm this is sufficient for Gram products and future QR/Cholesky updates. |

Audit update, 2026-06-01:

- Phase 3 basic matrix-kernel audit is complete.
- `MatVec` and `MatMul` are implementation-backed through the dot-product layer.
- `LeastSquares/LSNormalEquations.lean` now exposes
  `gramProductError_from_fl_matMul` and `gramVecError_from_fl_matVec`, proving
  the Gram contracts from concrete rounded kernels.  This converts the Gram
  part of normal equations from a supplied contract into an implementation-
  backed stage.  The Cholesky factorization stage remains contract-level.

## Triangular Solves And Derived Bounds

| Module | Rounded Implementation | Contract/Theorem | Status | Source/Boundary | Next Action |
| --- | --- | --- | --- | --- | --- |
| `TriangularSolve.lean` | `fl_backSub_steps`, `fl_backSub` | `backSub_backward_error*` | implementation-backed | Higham Ch. 8 back substitution | Audit source boundary and theorem variants. |
| `ForwardSub.lean` | `fl_forwardSub_steps`, `fl_forwardSub` | `forwardSub_backward_error` | implementation-backed | Higham Ch. 8 forward substitution analog | Audit source boundary and theorem variants. |
| `TriangularSolveCombined.lean` | uses forward/back substitution | `triangularSolve_backward_error` | mostly implementation-backed | Composition of Ch. 8 kernels | Check whether it assumes any hidden solve contract. |
| `TriangularForwardBound.lean` | derived from solve kernels | forward error results | mostly implementation-backed | Higham Ch. 8 forward bounds | Source-check theorem statements. |
| `TriangularForwardComparison.lean` | derived from solve kernels | comparison/mu bounds | mostly implementation-backed | Higham Ch. 8 comparison bounds | Source-check theorem statements. |
| `MMatrix.lean` | derived from forward substitution | M-matrix forward relative error | mostly implementation-backed | Higham Cor. 8.10 in mu-form | Already documents that Big-O simplification is not formalized. |
| `InverseBounds.lean` | exact/support | inverse/norm bounds | exact/support | Used by inverse and condition estimates | Audit only for source/reference quality. |

Audit update, 2026-06-01:

- Phase 4 triangular-solve audit is complete.
- `TriangularSolve.lean` and `ForwardSub.lean` are implementation-backed.  Their
  row specs are not unsupported assumptions: `fl_backSub_satisfies_spec` and
  `fl_forwardSub_satisfies_spec` prove those specs from the concrete recursive
  rounded algorithms before the backward-error theorems consume them.
- `TriangularSolveCombined.lean` only composes the proved forward- and
  back-substitution results.
- The forward-error and comparison files take exact mathematical hypotheses
  (`IsLeftInverse`, `IsInverse`, exact solution equation, diagonal dominance,
  M-matrix sign structure).  Those are normal theorem assumptions about the
  exact system rather than algorithmic stability contracts.
- `TriangularForwardComparison.lean` now labels the first comparison theorem as
  a backward-error-derived consequence and reserves Higham Theorem 8.9 for
  `forwardSub_forward_error_mu_bound`, the direct μ-bound.

## Orthogonal Transformations And QR

| Module | Rounded Implementation | Contract/Theorem | Status | Source/Boundary | Next Action |
| --- | --- | --- | --- | --- | --- |
| `QR/HouseholderReflector.lean` | exact `householderScale`/`householderVector`/`householderBeta`; rounded `fl_householderScale`, `fl_householderVector`, `fl_householderBeta` | `HouseholderConstructionError`, `fl_householderConstructionError`, `householderVectorError_from_construction`, `fl_householderVectorError`, exact beta equivalence, exact orthogonality, and unroll lemmas from `fl_norm2` plus `FPModel` primitives | implementation-backed for Lemma 18.1 construction and equation (18.3) normalized-vector model | Higham Ch. 18 Lemma 18.1 and equation (18.3) | Feed `HouseholderVectorError` into the concrete application proof for Lemma 18.2. |
| `QR/HouseholderApply.lean` | `fl_householderApply` | exact application identity, primitive-error unroll, matrix-form unroll, and `fl_householderApply_appError_of_matrix_bound` packaging bridge | implementation-backed kernel plus explicit remaining norm-bound obligation | Higham Ch. 18 Lemma 18.2 application boundary | Prove the Frobenius estimate for the concrete `householderApplyDeltaMatrix` from `HouseholderVectorError` and primitive rounding-error bounds. |
| `QR/HouseholderSpec.lean` | exact reflector plus normalized-vector bridge and abstract vector/app contracts | `householder_normalizedVector_eq`, `householderNormalizedVector_norm_sq`, `HouseholderVectorError`, `HouseholderAppError` | exact support plus application contract/specification-transfer | Higham Ch. 18 equation (18.3) and Lemma 18.2 | Equation (18.3) now has a construction bridge; next prove `fl_householderApply -> HouseholderAppError`. |
| `QR/HouseholderQR.lean` | `fl_householderQRPanel_R`, `fl_householderQR_R` | `fl_householderQRPanel_R_backward_error`, `fl_householderQR_R_backward_error`, `fl_householderQR_R_structured_backward_error`; legacy `householder_qr_backward` remains as a sequence wrapper | implementation-backed for the recursive Householder `R` algorithm under `HouseholderQRPanelReady`; legacy sequence theorem is still specification-transfer | Higham Ch. 18 Lemma 18.3 and Theorem 18.4 | Next expose/track concrete `Q` or reflector sequence output if solve-level algorithms need it. |
| `QR/GivensSpec.lean` | exact `givensC`/`givensS`; rounded `fl_givensC`/`fl_givensS`; `fl_givensApply` for supplied or computed coefficients | `givensCoeff_norm_sq`, `givensCoeff_zero_second`, `givensRotation_constructed_orthogonal`, `GivensCoeffError`, `fl_givensC_relative_error_conservative`, `fl_givensS_relative_error_conservative`, `fl_givensCoeffError_conservative`, `GivensAppError`, `fl_givensApply_supplied_app_error`, `fl_givensApply_coeffError_app_error`, `fl_givensApply_computed_app_error_conservative` | implementation-backed at the vector application layer with conservative constants; sharper Lemma 18.6 `gamma 4` and Lemma 18.7 `sqrt 2 * gamma 6` constants are still pending | Higham Ch. 18 equations (18.14), Lemma 18.6, Lemma 18.7 | Use the conservative computed-application bridge for sequence work, or first sharpen the coefficient/application constants if source-exact constants are required. |
| `QR/GivensMatrixStep.lean` | `fl_givensApplyMatrix`, `fl_givensApplyMatrixRect`, `fl_givensColumnStepMatrix`, `fl_givensColumnStepMatrixRect` | `ColumnwiseGivensStepError`, `fl_givensApply_computed_matrix_step_error`, `fl_givensColumnStep_matrix_step_error`, rectangular variants, residual aggregation lemmas | implementation-backed for one concrete Givens update applied columnwise, including coefficients read from the current matrix column | Higham Ch. 18 Lemma 18.7 lifted columnwise | Feed into Givens sequence/QR scheduling. |
| `QR/GivensQR.lean` | no full `fl_givens_qr`; supplied concrete update sequences and current-matrix column-step sequences supported | `GivensQRBackwardError`, `fl_givens_sequence_backward_error`, `fl_givens_sequence_backward_error_uniform`, `fl_givens_column_sequence_backward_error_uniform`, `fl_givens_panel_sequence_backward_error`, `fl_givens_panel_sequence_backward_error_uniform`, `fl_givens_column_panel_sequence_backward_error_uniform` | mixed: sequence accumulation is implementation-backed for supplied concrete Givens update sequences; final QR loop/schedule and triangular-shape proof are pending | Higham Ch. 18 Lemma 18.8 and Theorem 18.9 | Define the annihilation schedule and prove the produced sequence satisfies the update/shape assumptions. |
| `QR/QRSolve.lean` | `fl_householderQR_rhs`, `fl_householderQR_solve` | `HouseholderQRRhsPanelBackwardError`, `HouseholderQRPanelSolveBackwardError`, `fl_householderQRPanel_rhs_backward_error`, `fl_householderQR_rhs_backward_error`, `fl_householderQR_solve_components_backward_error`, `fl_householderQR_solve_backward_error`, `QRSolveBackwardError`, `qr_solve_backward_error_from_components`, `qr_solve_backward_from_components`, `qr_solve_perturbation_bound` | implementation-backed for concrete Householder QR solve under explicit readiness, nonzero-diagonal, positive-dimension, and gamma assumptions; bound is recursive/conservative rather than collapsed to the textbook asymptotic form | Higham Ch. 18 Theorem 18.5 | Optionally source-collapse/simplify recursive constants; next main rebuild target can move to Givens QR or Cholesky/LU factorization gaps. |

QR audit update, 2026-06-01:

- Low-level QR rebuild has started at the Householder reflector-construction
  boundary.
- Added `QR/HouseholderReflector.lean`, which defines concrete rounded kernels
  for Householder construction.
- Source-alignment correction: Higham Lemma 18.1 computes
  `s = sign(x_0)||x||_2`, `v_0 = fl_add x_0 s_hat`, and
  `beta_hat = fl_div 1 (fl_mul s_hat v_hat_0)`.  The earlier dot-product beta
  path `2/fl_dotProduct(v,v)` is an alternate algorithm and does not justify
  the source constant `γ_{4n+8}`.
- Source-alignment correction: applying `sign(x_0)` is treated as exact in
  Higham's operation count.  Therefore `fl_householderScale` is now an exact
  sign change applied to `fl_norm2`, not a rounded `fp.fl_mul`.
- The new unroll lemmas are implementation-backed from existing lower layers:
  `fl_householderScale_unroll_of_gammaValid_two_mul` uses `fl_norm2`, the
  square-root model, and exact sign application;
  `fl_householderVector_zero_unroll` uses one rounded addition; and
  `fl_householderBeta_unroll` uses one rounded multiplication plus one rounded
  division.
- Added `QR/HouseholderApply.lean`, which defines the concrete rounded
  operation `b - beta * v * (v^T b)` and unrolls it into dot-product,
  multiplication, and subtraction errors.
- These are not yet Higham Lemma 18.1 or Lemma 18.2 as stability theorems.  The
  next missing bridges are the perturbation/error bound for the constructed
  reflector and the proof that `fl_householderApply` satisfies
  `HouseholderAppError`.

QR audit update, 2026-06-02:

- Source image inspection of Higham Ch. 18 confirmed the exact missing boundary.
  Lemma 18.2 assumes equation (18.3): `v_hat = v + Δv`,
  `|Δv| ≤ γ_cm |v|`, with normalized `‖v‖₂ = sqrt 2`, and then proves the
  Householder application backward error.
- Added `HouseholderVectorError` to `HouseholderSpec.lean` to represent equation
  (18.3) explicitly.
- Added `householder_matMulVec_eq` to `HouseholderApply.lean`, proving the exact
  algebraic target `P b = b - beta * v * (v^T b)` for
  `P = I - beta * v v^T`.
- Added exact Householder construction definitions and the exact normalization
  bridge: `householderBeta_mul_norm_sq`, `householder_normalizedVector_eq`, and
  `householderNormalizedVector_norm_sq`.  This proves that the library's
  unnormalized `I - beta v v^T` form is algebraically compatible with Higham's
  normalized `I - v v^T` equation (18.3) form.
- Added `householder_exact_orthogonal`, proving that the exact
  `householderBeta`/`householderVector` construction satisfies the existing
  `householder_orthogonal` side condition when `v^T v` is nonzero.
- Added `HouseholderConstructionError` for the exact Higham Lemma 18.1 contract:
  tail equality, first-component relative error bounded by `γ_{n+2}`, and beta
  relative error bounded by `γ_{4n+8}`.
- Added exact source-alignment lemmas `householderScale_mul_self`,
  `householderVector_norm_sq_eq_two_scale_mul`, and
  `householderBetaFromScale_eq_householderBeta`, connecting Higham's beta
  formula `1/(s*v_0)` to the reflector formula `2/(v^T v)`.
- Added `householderVector_zero_abs_eq`, proving the exact no-cancellation fact
  for the first component: `|x_0+s| = |x_0| + |s|`.
- Added `fl_householderScale_relative_error_sqrt_factor`, composing the new
  `fl_norm2` square-root-factor bridge with the exact sign application in
  `fl_householderScale`.
- Added `fl_householderVector_tail_eq_householderVector`, proving the easy
  exact-copy part of Lemma 18.1: all non-first components of the rounded
  Householder vector agree with the exact vector.
- Added `fl_householderScale_relative_error` and
  `fl_householderVector_zero_relative_error`, proving the scale and
  first-component parts of Higham Lemma 18.1 from the concrete rounded norm and
  vector kernels.  The first-component theorem assumes `x ≠ 0`, using the exact
  no-cancellation fact to show `x_0+s` is nonzero before forming a relative
  error.
- Added `gamma_inv_mul_roundoff` in `Rounding.lean`, a reusable lemma that
  combines a reciprocal of a `γ_k`-perturbed denominator with the final rounded
  division while staying within `γ_{2k}`.  This is what keeps the beta theorem
  at Higham's `γ_{4n+8}` constant instead of weakening it by one operation.
- Added `fl_householderBeta_denominator_relative_error`,
  `fl_householderBeta_relative_error`, and `fl_householderConstructionError`.
  Therefore Higham Lemma 18.1 is now implementation-backed in the library for
  nonzero input vectors: the concrete rounded construction proves tail equality,
  first-component `γ_{n+2}` perturbation, and beta `γ_{4n+8}` perturbation.
- Added `householderApplyRoundedMatrix`,
  `householderApplyDeltaMatrix`, `fl_householderApply_matrix_unroll`, and
  `fl_householderApply_appError_of_matrix_bound`.  The application kernel is
  now connected to a concrete perturbation matrix determined by primitive
  rounding errors.  The remaining Lemma 18.2 work is the real Frobenius estimate
  for that delta matrix from `HouseholderVectorError`; the packaging bridge does
  not claim this bound has been proved.
- Added exact Frobenius helper lemmas, equation (18.3) relative-factor
  consequences, and normalized application entrywise gamma theorems.  The
  application proof is now reduced to the final Frobenius summation estimate
  for the concrete `householderApplyDeltaMatrix`.
- Added the final normalized Frobenius estimate and
  `fl_householderApply_normalized_appError`.  The one-reflector application
  bridge is now implementation-backed once equation (18.3) is available.  The
  remaining low-level QR task is to connect the concrete Householder
  construction theorem `fl_householderVectorError` directly to this application
  theorem, then lift from one reflector to a sequence.
- Added `HouseholderOneStep.lean` and
  `fl_householderConstructApply_appError`, so concrete Householder construction
  plus concrete application now satisfies the one-reflector
  `HouseholderAppError` contract.  The next QR gap is no longer the single
  reflector; it is the repeated-reflector sequence bridge into
  `OrthogonalSequenceBackwardError`.
- Added `sqrt_one_add_mul_relative_gamma`, plus
  `householderVectorError_from_construction` and `fl_householderVectorError`.
  Therefore Higham equation (18.3) is now implementation-backed for nonzero
  input vectors after algebraic normalization:
  `sqrt(beta_hat) v_hat = sqrt(beta) v + Δv`, with
  `|Δv| ≤ γ_{5n+10}|sqrt(beta)v|` under the stronger
  `gammaValid fp (8*n+16)` side condition.  The explicit `γ_{5n+10}` is a
  concrete version of Higham's generic `γ_{cm}`.
- Decision: do not add a vacuous bridge theorem that manufactures an arbitrary
  perturbation matrix after the fact.  The real bridge must first prove
  the concrete application kernel satisfies `HouseholderAppError` using
  `HouseholderVectorError`; the vector-error side is now available.
- Added `QR/HouseholderMatrixStep.lean` after the one-vector application bridge.
  The new `ColumnwiseHouseholderStepError` records exactly what the concrete
  matrix-column application proves: for each output column there is a bounded
  perturbation `ΔP_j`, and `ΔP_j` may depend on the column.  This is
  source-aligned with Higham Lemma 18.3, where Lemma 18.2 is applied to each
  column before the perturbations are aggregated.
- Remaining QR gap: the older `orthogonal_sequence_one_step` theorem assumes a
  single perturbation matrix `ΔP` for the whole matrix step.  That is stronger
  than the current concrete columnwise result.  The next proof should therefore
  introduce a columnwise sequence theorem or refine the existing sequence
  contract before claiming a full implementation-backed Householder QR result.
- Added exact aggregation from columnwise residuals to a single residual matrix:
  if `E[:,j] = Δ_j A[:,j]` and `‖Δ_j‖_F ≤ c` for every column, then
  `‖E‖_F ≤ c‖A‖_F`.  Consequently a concrete columnwise Householder matrix
  step now yields `A_hat = P*A + E` with `‖E‖_F ≤ c‖A‖_F`.
- Remaining QR gap after this improvement: repeated residual accumulation
  across several orthogonal reflector steps, followed by the algebraic
  conversion to the final `A + ΔA = Q R_hat` form.
- Added residual-form one-step accumulation in `HouseholderQR.lean`.  A step
  stated as `A_next = P*A_hat + E`, `‖E‖_F ≤ c‖A_hat‖_F` now advances the
  invariant `A_hat = Qᵀ(A+ΔA)`.  The columnwise Householder contract feeds this
  theorem directly.  This is the correct bridge shape after Higham Lemma 18.2
  because the perturbation matrix may vary by column.
- Added repeated residual accumulation with the recurrence
  `residualAccumBound`.  This proves the sequence theorem without dropping
  higher-order terms.  The public Higham-style `r*c`/`γ_cm` statement should be
  recovered only after a sourced gamma-collapse/first-order simplification
  lemma is added.
- Added repeated concrete Householder reflector sequence theorem
  `fl_householder_sequence_backward_error`.  This theorem consumes concrete
  `fl_householderApplyMatrix` updates and the implementation-backed
  construction/application bound for each nonzero `xseq k`.
- Added rectangular panel update infrastructure.  This matters because the real
  Householder QR loop applies an `m × m` reflector to an `m × p` trailing panel;
  using only the square full-matrix theorem would hide that dependency.
- Added rectangular orthogonal sequence infrastructure and
  `fl_householder_panel_sequence_backward_error`.  This closes another part of
  the QR gap: repeated concrete rounded Householder panel updates now have a
  proved rectangular backward-error sequence theorem.
- Remaining QR gap after this improvement: formalize the actual Householder QR
  loop that chooses `xseq` from trailing columns, preserves the intended
  submatrix structure, proves triangularization, and then packages the final
  result as `HouseholderQRBackwardError`.

## Cholesky

| Module | Rounded Implementation | Contract/Theorem | Status | Source/Boundary | Next Action |
| --- | --- | --- | --- | --- | --- |
| `Cholesky/CholeskySpec.lean` | no concrete rounded Cholesky factorization identified | `CholeskyBackwardError` and consequences | contract/specification-transfer | Higham Cholesky analysis | Build concrete Cholesky factorization kernel later; needs `fl_sqrt`, division, dot/update kernels. |
| `Cholesky/CholeskySolve.lean` | uses concrete triangular solves | assumes `hChol : CholeskyBackwardError` | mixed | Solve stage is implementation-backed; factorization is assumed | Rebuild factorization before calling solve end-to-end. |
| `Cholesky/CholeskyPerturbation.lean` | exact/support | perturbation lemmas | exact/support | Source-check only | No rounded algorithm expected. |
| `Cholesky/CholeskyPSD.lean` | no concrete rounded factorization identified | pivoted/PSD contracts and theorems | contract/specification-transfer | Source-check Cholesky PSD material | Depends on base Cholesky bridge. |
| `Cholesky/CholeskyDemmel.lean` | none identified | consumes `CholeskyBackwardError` | contract/specification-transfer | Demmel-style Cholesky consequences | Revisit after Cholesky bridge. |
| `Cholesky/CholeskyNonsym.lean` | unknown | nonsymmetric variants | unknown | Needs file-level read | Defer until base Cholesky audited. |
| `Cholesky/CholeskyIndefinite.lean` | no concrete block LDLT factorization identified | `BlockLDLTBackwardError` | contract/specification-transfer | Source-check Bunch-Kaufman/LDLT source | Revisit after LU/Cholesky foundations. |

## LU And Gaussian Elimination

| Module | Rounded Implementation | Contract/Theorem | Status | Source/Boundary | Next Action |
| --- | --- | --- | --- | --- | --- |
| `LU/GaussianElimination.lean` | no concrete rounded GE implementation identified | `LUFactSpec`, `LUBackwardError`, `PermutedLUBackwardError` | contract/specification-transfer | Higham Ch. 9 GE/LU backward error | Need concrete no-pivot and pivoted GE kernels plus bridge to `LUBackwardError`. |
| `LU/Doolittle.lean` | no concrete rounded Doolittle bridge identified | consumes `LUBackwardError` | contract/specification-transfer | Higham Ch. 9 | Rebuild after GE/Doolittle implementation bridge. |
| `LU/TridiagonalRecurrence.lean` | `tridiag_lu_aux`, `tridiag_lu` use `fl_div`, `fl_mul`, `fl_sub` | structural/growth results; bridge to `LUBackwardError` unclear | mixed | Higham §9.5 Algorithm 9.1 | Candidate first LU factorization bridge because concrete recurrence exists. |
| `LU/Tridiagonal.lean` | no new concrete implementation | consumes `LUBackwardError` | contract/specification-transfer | Higham tridiagonal/banded LU bounds | Rebuild after tridiagonal recurrence bridge. |
| `LU/TridiagonalCond.lean` | exact/support | condition/inverse structure | exact/support | Higham Ch. 14.5 | Source-check only; not a rounded FP algorithm. |
| `LU/GrowthFactor.lean` | mostly exact/support | growth-factor consequences, many consume `hLU` | mixed/contract-transfer | Higham Ch. 9 growth factor | Revisit after `LUBackwardError` bridge. |
| `LU/LUSolve.lean` | uses concrete triangular solves | assumes `hLU : LUBackwardError` | mixed | Higham Theorem 9.4 | End-to-end only after LU factorization bridge. |
| `LU/BlockLU.lean` | block specs and contracts | `BlockLUBackwardError`, block fact specs | mixed/contract-transfer | Higham/block LU material | Defer until scalar LU bridge exists. |
| `LU/SpecialMatrices.lean` | exact/support plus `hLU` consumers | special matrix consequences | mixed/contract-transfer | Higham special matrix LU results | Revisit after LU bridge. |

## Least Squares

| Module | Rounded Implementation | Contract/Theorem | Status | Source/Boundary | Next Action |
| --- | --- | --- | --- | --- | --- |
| `LeastSquares/LSNormalEquations.lean` | uses triangular solves but assumes Gram and Cholesky contracts | `GramProductError`, `GramVecError`, `hChol` | mixed/contract-transfer | Higham least-squares/normal equations | Prove Gram contracts from `fl_matMul`/`fl_matVec`; then depends on Cholesky bridge. |
| `LeastSquares/LSPerturbation.lean` | exact/support | perturbation structures/results | exact/support | Source-check SVD/perturbation material | No rounded algorithm expected in this file. |
| `LeastSquares/LSQRSolve.lean` | no concrete QR solve implementation | `LSQRSolveBackwardError` | contract/specification-transfer | QR-based least squares | Rebuild only after QR bridge. |

## Matrix Inversion, Gauss-Jordan, And Refinement

| Module | Rounded Implementation | Contract/Theorem | Status | Source/Boundary | Next Action |
| --- | --- | --- | --- | --- | --- |
| `MatrixInversion.lean` | method specs and some derived solve uses | `Method2Spec`, `BlockMethod1BSpec`, `hLU` consumers | mixed/contract-transfer | Higham matrix inversion material | Revisit after triangular solve and LU bridges. |
| `GaussJordan.lean` | stage specs; no full concrete GJE bridge identified | `GJEStage2Spec`, `hLU` consumers | mixed/contract-transfer | Higham/Gauss-Jordan material | Defer until LU and matrix inversion pieces are stable. |
| `IterativeRefinement.lean` | `fl_residual` exists | `ResidualError`, `SolverSpec`, `ComponentwiseBackwardError` | mixed | Higham iterative refinement Ch. 11 | First prove residual contract from `fl_residual`; solver remains abstract unless a concrete solver is supplied. |

## Other Higher-Level Algorithms

| Module | Rounded Implementation | Contract/Theorem | Status | Source/Boundary | Next Action |
| --- | --- | --- | --- | --- | --- |
| `StationaryIteration.lean` | mostly exact iteration/specs | `SplittingSpec`, local error assumptions | mixed/exact | Iterative methods | Revisit after low-level solve/residual infrastructure. |
| `MatrixPowers.lean` | exact algorithms/specs | `JordanFormSpec` and exact bounds | exact/support with abstract spec | Matrix powers/Jordan analysis | Source-check; not immediate FP stability target. |
| `CondEstimation.lean` | exact estimator algorithms | lower-bound theorems | exact/support | Higham Ch. 14 condition estimation | Not a rounded stability proof unless FP estimator is later modeled. |
| `Sylvester/*` | mostly exact perturbation/backward structures | Sylvester specs/backward perturbation | exact/support or contract-transfer | Sylvester perturbation theory | Defer until main linear algebra kernels are rebuilt. |
| `Underdetermined/*` | no concrete full solve identified | assumes Cholesky/solve contracts | contract/specification-transfer | Higham Ch. 20 style results | Rebuild after Cholesky/QR choices. |
| `FastMatMul.lean` | no concrete rounded Strassen/Winograd implementation identified | error-bound structures | contract/specification-transfer | Fast matrix multiplication sources | Defer; requires separate source audit and concrete algorithm definitions. |

## Immediate Conclusions

1. The low-level scalar/vector and basic matrix kernels are mostly healthy and
   should be verified first.
2. Triangular solves appear substantially implementation-backed and are the next
   major dependency to audit carefully.
3. QR, Cholesky, general LU, least squares, matrix inversion, and several
   high-level algorithms are not yet end-to-end.  They often package or consume
   contracts rather than proving those contracts from concrete rounded code.
4. The first high-level rebuild target should not be full QR immediately.  The
   logical next steps are base-kernel audit, triangular-solve audit, then either
   tridiagonal LU recurrence or Householder low-level kernels.
