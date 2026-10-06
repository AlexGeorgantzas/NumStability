# Implementation-Backed Repass Ledger

Date: 2026-06-01

This is the execution ledger for turning the library from contract-heavy
formalization into implementation-backed stability analysis.  It should be used
together with `thesis/IMPLEMENTATION_BACKED_AUDIT.md` and the local Codex skill
`lean-fp-stability-audit`.

This ledger is intentionally living documentation.  It should be updated during
the repass whenever a higher-level proof exposes a missing lower-level rounded
operation, bridge theorem, source reference, or dependency that was not visible
from the initial audit.

## Working Rules

- Work bottom-up.
- Update this ledger as new low-level requirements are discovered.
- Do not delete useful contracts; add bridge theorems from concrete `fl_*`
  implementations to those contracts.
- If a needed lower-level rounded operation is missing, build that layer first.
- Before treating a bound as an assumption, check the original source.  If the
  source proves it, the Lean rebuild should eventually prove it too.
- Keep source references precise: chapter, theorem, lemma, equation, or
  algorithm number.
- A module is not end-to-end until the bridge theorem exists.

## Acceptance Criteria For A Rebuilt Algorithm

For each algorithm/result:

- [ ] Exact mathematical specification is identified.
- [ ] Concrete rounded `fl_*` implementation exists.
- [ ] Main stability contract is identified or created.
- [ ] Bridge theorem proves the concrete implementation satisfies the contract.
- [ ] Final theorem uses the proved bridge, not an unsupplied contract.
- [ ] Source reference is recorded.
- [ ] Targeted Lean file builds.
- [ ] Changed files contain no real `sorry`, `admit`, `axiom`, or `opaque`.

## Phase 0: Hygiene And Baseline

- [ ] Decide whether to commit `.codex/PROJECT_MEMORY.md` memory updates before
  major Lean edits.
- [ ] Remove or ignore local `.DS_Store` noise before commits.
- [ ] Run `lake build` and record the current warning profile.
- [ ] Scan for real `sorry`, `admit`, `axiom`, and `opaque`.
- [ ] Keep the stable fallback tag/branch note visible in project memory.

## Phase 1: Foundation Audit

Goal: confirm the primitive model and exact infrastructure are acceptable
bottom assumptions.

- [x] `FP/Model.lean`: confirm each primitive assumption is sourced and
  documented.  Special attention: `fl_add_zero` and `model_sqrt`.
- [x] `Analysis/Rounding.lean`: source-check gamma algebra.
- [x] `Analysis/Error.lean`: source-check basic error definitions/lemmas.
- [x] `Analysis/Summation.lean`: confirm fold error proofs are derived from
  `fp.model_add`.
- [x] `Analysis/SubtractionFold.lean`: confirm subtraction fold proofs are
  derived from `fp.model_sub`.
- [x] `Analysis/Stability.lean`: confirm these are definitions/predicates only.
- [x] `Analysis/MatrixAlgebra.lean`: confirm exact algebra uses Mathlib where
  practical and wrappers are documented as wrappers.

Phase 1 result, 2026-06-01:

- Foundation status: acceptable bottom layer.
- `FPModel` remains the intended axiomatic base.  `model_sqrt` is aligned with
  Higham §2.2 after (2.4), where square root is normally included in the same
  standard model.  `fl_add_zero` is explicitly documented as an extra exactness
  hypothesis, not a consequence of (2.4).
- `Rounding.lean` gamma algebra is sourced to Higham Lemmas 3.1 and 3.3, with
  `gammaValid` kept explicit and model-parametric.
- `Summation.lean` and `SubtractionFold.lean` are implementation-backed
  foundation lemmas: the fold bounds are derived from repeated `fp.model_add`
  or `fp.model_sub`.
- `Stability.lean` is predicate infrastructure; no rounded implementation is
  expected there.
- `MatrixAlgebra.lean` is exact support.  Its norm wrappers are documented as
  compatibility bridges over Mathlib rather than independent exact norms.
- Targeted validation passed:
  `lake env lean` on `FP/Model.lean`, `Analysis/Rounding.lean`,
  `Analysis/Error.lean`, `Analysis/Summation.lean`,
  `Analysis/SubtractionFold.lean`, `Analysis/Stability.lean`, and
  `Analysis/MatrixAlgebra.lean`.

## Phase 2: Scalar And Vector Kernels

Goal: establish the positive template before climbing.

- [x] `RecursiveSum.lean`: verify `fl_recursiveSum` -> backward/forward theorems.
- [x] `PairwiseSum.lean`: verify `fl_pairwiseSum` -> backward/forward theorems.
- [x] `SumTree.lean`: verify `SumTree.eval` using `fp.fl_add` -> tree bounds.
- [x] `DotProduct.lean`: confirm as canonical implementation-backed example.
- [x] `OuterProduct.lean`: verify `fl_outerProduct` -> error/backward theorem.
- [x] `Norm2.lean`: decide the next needed theorem for Householder construction.
- [ ] If `Norm2.lean` needs stronger bounds, prove them before QR work.

Likely output:

- a small source/reference cleanup pass;
- possibly new `Norm2` bridge lemmas for Householder vector construction.

Phase 2 result, 2026-06-01:

- Scalar/vector kernel audit is complete.
- `RecursiveSum`, `PairwiseSum`, `SumTree`, `DotProduct`, `OuterProduct`, and
  `Norm2` all have concrete rounded definitions and targeted file validation
  passed.
- `DotProduct.lean` is confirmed as the canonical implementation-backed
  example: `fl_dotProduct` is proved stable through `dotProduct_backward_error`.
- Source-boundary cleanup:
  `DotProduct.lean` now points the core inner-product bound to Higham §3.1
  rather than §3.5.
- Source-boundary cleanup:
  `OuterProduct.lean` now documents that its row-wise perturbation theorem is
  not full backward stability of the outer-product algorithm.  This matches
  Higham's statement after equation (3.6) that the computed outer product
  generally cannot be represented as `(x + Δx)(y + Δy)ᵀ`.
- `Norm2.lean` is implementation-backed as a kernel: `fl_norm2Sq` uses
  `fl_dotProduct`, and `fl_norm2` uses `fp.fl_sqrt`.  The stronger
  Householder-specific norm/vector construction theorem is intentionally left
  open until the Chapter 18 source boundary is checked.

## Phase 3: Basic Matrix Kernels

Goal: ensure matrix-vector and matrix-matrix products are implementation-backed
and ready for Gram products, residuals, and matrix updates.

- [x] `MatVec.lean`: verify `fl_matVec` uses `fl_dotProduct` and proves the
  advertised backward/error bounds.
- [x] `MatMul.lean`: verify `fl_matMul` uses `fl_dotProduct` and proves the
  advertised bounds.
- [x] Check whether the current matrix kernels are enough to prove
  `GramProductError` and `GramVecError` in least squares.
- [x] If Gram-specific bridge lemmas are missing, add them after source check.

Phase 3 result, 2026-06-01:

- Basic matrix kernel audit is complete.
- `MatVec.lean` and `MatMul.lean` are implementation-backed: their rounded
  kernels call `fl_dotProduct` through `fl_matVec`, and their error theorems
  reuse the dot-product bounds.
- Added least-squares bridge theorems in `LSNormalEquations.lean`:
  `gramProductError_from_fl_matMul` and `gramVecError_from_fl_matVec`.
  These prove the normal-equations Gram contracts from the concrete rounded
  matrix multiplication/vector kernels.
- Consequence: in `LSNormalEquations.lean`, the Gram product/vector stage no
  longer needs to remain a permanent assumption.  The remaining major assumed
  stage is Cholesky factorization via `CholeskyBackwardError`.
- Targeted validation passed:
  `lake env lean` on `MatVec.lean`, `MatMul.lean`, and
  `LeastSquares/LSNormalEquations.lean`.

## Phase 4: Triangular Solves

Goal: lock down the main solve kernels before LU/Cholesky/QR solve.

- [x] `TriangularSolve.lean`: audit `fl_backSub_steps`, `fl_backSub`,
  row specs, and backward-error theorem chain.
- [x] `ForwardSub.lean`: audit `fl_forwardSub_steps`, `fl_forwardSub`,
  row specs, and backward-error theorem chain.
- [x] `TriangularSolveCombined.lean`: confirm composition uses proved forward
  and backward substitution results, not hidden solve contracts.
- [x] `TriangularForwardBound.lean`: source-check forward bound statements.
- [x] `TriangularForwardComparison.lean`: source-check comparison/mu bounds.
- [x] `MMatrix.lean`: confirm Corollary 8.10 status and explicitly record any
  non-formalized Big-O simplification.

Likely output:

- documentation/source refinements;
- small bridge lemmas if composition currently unfolds too much.

Phase 4 result, 2026-06-01:

- Triangular solve audit is complete.
- `TriangularSolve.lean` is implementation-backed.  It defines concrete
  `fl_backSub_steps` and `fl_backSub`, proves `fl_backSub_satisfies_spec` from
  the recursive rounded algorithm, then proves `backSub_backward_error` from
  that bridge.  `BackSubRowSpec` is therefore an internal bridge interface, not
  an unsupported high-level assumption.
- `ForwardSub.lean` is implementation-backed in the same sense:
  `fl_forwardSub_satisfies_spec` proves `ForwardSubRowSpec` from
  `fl_forwardSub`, and `forwardSub_backward_error` consumes that proved bridge.
- `TriangularSolveCombined.lean` composes the two proved triangular-solve
  theorems; it does not introduce a hidden solve contract.
- `ForwardError.lean`, `TriangularForwardBound.lean`,
  `TriangularForwardComparison.lean`, and `MMatrix.lean` are derived results.
  They necessarily take exact-side hypotheses such as `IsLeftInverse`,
  `IsInverse`, `Tx = b`, diagonal dominance, M-matrix sign conditions, and
  `gammaValid`.  These are theorem assumptions about the exact problem, not
  missing rounded-algorithm contracts.
- Source-boundary cleanup: `TriangularForwardComparison.lean` now distinguishes
  the backward-error-derived comparison bound from Higham's direct Theorem 8.9,
  which is formalized as `forwardSub_forward_error_mu_bound`.
- `MMatrix.lean` remains honest about Corollary 8.10: it proves the μ-form
  relative-error theorem and does not claim the asymptotic Big-O simplification
  as a separate formal theorem.

## Phase 5: Low-Level Orthogonal Transformations

The user-selected order after triangular solves is the QR low-level layer:
`Norm2`, Householder reflector construction/application, then Givens rotation
application.  Tridiagonal LU remains a later candidate, but this phase now
prioritizes Householder/Givens because they are the next layer in the agreed
bottom-up order.

Deferred candidate: tridiagonal LU recurrence.

- [ ] Source-check Higham §9.5 Algorithm 9.1 and Theorem 9.12 boundaries.
- [ ] Audit `LU/TridiagonalRecurrence.lean`: `tridiag_lu_aux`,
  `tridiag_lu`, `tridiag_L_matrix`, `tridiag_U_matrix`.
- [ ] Identify the exact contract it should satisfy.
- [ ] Prove a bridge from the concrete recurrence to the appropriate LU
  backward/error contract, if mathematically feasible.
- [ ] Then revisit `LU/Tridiagonal.lean` consumers.

Householder low-level kernels.

- [x] Source-check Higham Ch. 18 Lemma 18.1, equation 18.3, Lemma 18.2,
  Lemma 18.3, Theorem 18.4.
- [x] Build concrete rounded Householder vector construction.
- [x] Build concrete rounded Householder application.
- [x] Prove Householder vector construction bound.
- [ ] Prove one-reflector application contract `HouseholderAppError` from the
  concrete implementation.
- [ ] Prove sequence bridge from repeated concrete applications to
  `OrthogonalSequenceBackwardError`.
- [ ] Only then rebuild `householder_qr_backward` as end-to-end.

Phase 5 update, 2026-06-01:

- Added `QR/HouseholderReflector.lean`.
- Concrete rounded construction kernels now exist for
  `fl_householderScale`, `fl_householderVector`, and `fl_householderBeta`.
- Source-alignment correction: Higham Lemma 18.1 computes
  `s = sign(x_0)||x||_2`, `v_0 = fl_add x_0 s_hat`, and
  `beta_hat = fl_div 1 (fl_mul s_hat v_hat_0)`.  The previous dot-product beta
  path is an alternate algorithm and should not be used for the
  `γ_{4n+8}` source bound.
- Source-alignment correction: applying `sign(x_0)` is exact in Higham's
  operation count, so `fl_householderScale` is an exact sign change of
  `fl_norm2`, not a rounded multiplication.
- Added unroll lemmas showing these kernels reduce to the lower-level rounded
  norm, addition, multiplication, and division operations.
- Added `QR/HouseholderApply.lean`.
- Concrete rounded Householder application now exists for the operation
  `b - beta * v * (v^T b)`, with an unroll lemma reducing it to the rounded dot
  product, scalar multiplication, per-component multiplication, and subtraction.
- This is still only the kernel layer.  It does not yet prove Higham
  Lemma 18.1's perturbation bound, and it does not yet prove Lemma 18.2's
  application bound.
- Next action: prove the Householder vector-construction bound and/or the bridge
  from `fl_householderApply` to `HouseholderAppError`.

Phase 5 update, 2026-06-02:

- Source image inspection of Higham Ch. 18 clarified the dependency:
  Lemma 18.2 assumes equation (18.3), namely a normalized exact vector `v` and a
  computed vector `v_hat = v + Δv` with `|Δv| ≤ γ_cm |v|`.
- Added `HouseholderVectorError` to represent equation (18.3) explicitly.
- Added `householder_matMulVec_eq`, the exact target identity
  `P b = b - beta * v * (v^T b)`.
- Added exact Householder construction definitions and normalization bridge
  lemmas:
  `householderBeta_mul_norm_sq`, `householder_normalizedVector_eq`, and
  `householderNormalizedVector_norm_sq`.  These show that the library's
  unnormalized `I - beta v v^T` reflector form is algebraically compatible with
  Higham's normalized `I - v v^T` equation (18.3) form.
- Added `householder_exact_orthogonal`, proving that exact
  `householderVector` and exact `householderBeta` produce an orthogonal
  reflector when `v^T v` is nonzero.
- Added `HouseholderConstructionError`, the explicit Higham Lemma 18.1
  construction contract.
- Added exact beta source-alignment lemmas:
  `householderScale_mul_self`,
  `householderVector_norm_sq_eq_two_scale_mul`, and
  `householderBetaFromScale_eq_householderBeta`.
- Added Householder-facing norm bridges in `Norm2.lean`:
  `weighted_sum_relative_error_nonneg`, `fl_norm2Sq_relative_error`,
  `fl_norm2_relative_error_sqrt_factor`, `sqrt_one_add_sub_one_abs_le_abs`,
  `sqrt_one_add_mul_roundoff_gamma`, and `fl_norm2_relative_error`.  The
  rounded norm now has the source-style implementation-backed form
  `fl_norm2 x = ||x||_2(1+θ_{n+1})`.
- Added `householderVector_zero_abs_eq`, the exact no-cancellation fact
  `|x_0+s| = |x_0| + |s|`, and
  `fl_householderScale_relative_error_sqrt_factor`, which composes the
  `fl_norm2` bridge with exact sign application.
- Added `fl_householderVector_tail_eq_householderVector`, the implementation-
  backed exact-copy part of Lemma 18.1 for all non-first components.
- Added `fl_householderScale_relative_error` and
  `fl_householderVector_zero_relative_error`, proving the scale and
  first-component parts of Higham Lemma 18.1 from concrete rounded kernels.
  The first-component bridge assumes `x ≠ 0`, which is the meaningful
  Householder construction case and is used to form a relative error for
  `x_0+s`.
- Added `gamma_inv_mul_roundoff`, the rounded reciprocal gamma rule needed to
  preserve Higham's beta constant.
- Added `fl_householderBeta_denominator_relative_error`,
  `fl_householderBeta_relative_error`, and `fl_householderConstructionError`.
  Higham Lemma 18.1 is now implementation-backed for nonzero vectors: concrete
  rounded construction proves tail equality, first-component `γ_{n+2}`, and
  beta `γ_{4n+8}`.
- Added `sqrt_one_add_mul_relative_gamma`,
  `householderVectorError_from_construction`, and
  `fl_householderVectorError`.  Higham equation (18.3) is now
  implementation-backed for nonzero vectors after algebraic normalization:
  the computed normalized vector `sqrt(beta_hat) v_hat` is a componentwise
  perturbation of the exact normalized vector `sqrt(beta) v` with explicit
  bound `γ_{5n+10}` under `gammaValid fp (8*n+16)`.
- Do not prove `HouseholderAppError` by choosing an arbitrary perturbation
  matrix after the computation.  That would build a tautological certificate,
  not Higham's stability analysis.
- Added `householderApplyRoundedMatrix` and
  `fl_householderApply_matrix_unroll`, proving the concrete rounded
  Householder application is exactly multiplication by the matrix determined by
  its primitive dot-product/multiplication/subtraction errors.
- Added `householderApplyDeltaMatrix` and
  `fl_householderApply_appError_of_matrix_bound`.  This is a packaging bridge,
  not the missing Lemma 18.2 bound: it converts a Frobenius bound for the
  concrete delta matrix into `HouseholderAppError`.
- Added exact Frobenius infrastructure in `MatrixAlgebra.lean`:
  `frobNorm_le_of_frobNormSq_le_sq`,
  `frobNormSq_le_sum_sq_of_entrywise_abs_le`, and
  `frobNorm_le_of_entrywise_abs_le_sum_sq`.
- Added equation (18.3) consequences in `HouseholderSpec.lean`:
  `householderVectorError_sum_abs_sq`,
  `householderVectorError_vhat_abs_le`,
  `householderVectorError_relative_factors`, and
  `householderVectorError_vhat_abs_sq_sum_le`.
- Added `householderApplyDeltaMatrix_normalized_factorization`,
  `householderApply_error_factor_gamma`, and
  `householderApplyDeltaMatrix_normalized_entry_gamma`.
- Added `householderApply_sub_error_frob_bound`,
  `householderApply_outer_gamma_frob_bound`,
  `householderApplyDeltaMatrix_normalized_frob_bound`, and
  `fl_householderApply_normalized_appError`.
- Result: Higham Lemma 18.2 is now implementation-backed in normalized
  one-vector form, assuming equation (18.3) as its source hypothesis.  The bound
  is kept as the raw expression
  `sqrt(n*u^2) + 2*gamma(2a+n+3)` instead of a single generic `gamma_cm`.
- Added `QR/HouseholderOneStep.lean` with
  `fl_householderConstructApply_appError`, combining
  `fl_householderVectorError` from the concrete Householder construction with
  `fl_householderApply_normalized_appError`.
- Result: construction plus application is now implementation-backed for one
  reflector.  For nonzero input vectors and `gammaValid fp (11*n+23)`, the
  concrete constructed normalized vector applied through
  `fl_householderApply` satisfies `HouseholderAppError`.
- Added `QR/HouseholderMatrixStep.lean` with a concrete matrix-column
  implementation `fl_householderApplyMatrix` and the contract
  `ColumnwiseHouseholderStepError`.
- Result: the concrete Householder construction/application bridge now applies
  to every matrix column.  The perturbation is allowed to depend on the column,
  matching the way Higham Lemma 18.3 uses Lemma 18.2.  This exposes a genuine
  mismatch with the older `orthogonal_sequence_one_step`, which assumes a
  single `ΔP` for an entire matrix step.
- Added exact Frobenius aggregation lemmas:
  `matMulVec_sum_sq_le_frobNormSq_mul_sum_sq`,
  `frobNormSq_columnwise_matMulVec_le`, and
  `frobNorm_columnwise_matMulVec_le`.
- Result: from `ColumnwiseHouseholderStepError` we now derive a single residual
  matrix `E` with `A_hat = P*A + E` and `‖E‖_F ≤ c‖A‖_F`.  This closes the
  first aggregation step needed for Higham Lemma 18.3 without assuming a global
  reflector perturbation matrix.
- Added `orthogonal_sequence_one_step_of_residual` and
  `orthogonal_sequence_one_step_of_columnwise_error` in `QR/HouseholderQR.lean`.
- Result: a columnwise Householder matrix step can now advance the sequence
  invariant `A_hat = Qᵀ(A+ΔA)` by one orthogonal transformation using only a
  residual matrix bound `‖E‖_F ≤ c‖A_hat‖_F`, rather than requiring one global
  matrix perturbation `ΔP` for the entire step.
- Added `residualAccumBound` and
  `residual_orthogonal_sequence_backward_error` in `QR/HouseholderQR.lean`.
- Result: repeated residual accumulation is now proved with a conservative
  recurrence bound:
  `‖ΔA‖_F ≤ residualAccumBound c r ‖A₀‖_F`.  This is sound because it keeps the
  higher-order terms generated by repeated steps, instead of silently replacing
  the result by the first-order approximation `r*c`.
- Added `columnwise_householder_sequence_backward_error` and
  `fl_householder_sequence_backward_error`.
- Result: a repeated sequence of concrete Householder reflector applications is
  now implementation-backed, provided the sequence supplies nonzero construction
  vectors `xseq k` and each matrix update is the concrete
  `fl_householderApplyMatrix` update.
- Remaining distinction: this is still not the full QR factorization loop.  It
  does not yet define the QR trailing-column choice for `xseq`, prove that the
  result is upper triangular, or connect the final matrix to the old
  `HouseholderQRBackwardError` wrapper.
- Added rectangular panel infrastructure:
  `matMulRect`, rectangular Frobenius columnwise residual aggregation,
  `fl_householderApplyMatrixRect`, and
  `ColumnwiseHouseholderStepErrorRect`.
- Result: a square Householder reflector can now be applied to a rectangular
  `m × p` panel with the same implementation-backed columnwise backward-error
  and normwise residual bounds.  This is necessary for the true QR loop because
  Householder QR updates trailing panels, not only full square matrices.
- Added rectangular orthogonal algebra and rectangular sequence theorems:
  `frobNorm_orthogonal_left_rect`,
  `residual_orthogonal_sequence_backward_error_rect`, and
  `fl_householder_panel_sequence_backward_error`.
- Result: repeated concrete Householder updates on rectangular panels now have
  an implementation-backed backward-error sequence theorem.
- Added `panelFirstColumn` and
  `fl_householder_first_column_panel_step_error`.
- Result: the panel update bridge now covers the actual first-column vector
  choice used by a Householder QR panel step, rather than only arbitrary
  supplied construction vectors.
- Added `fl_householder_first_column_panel_sequence_backward_error`.
- Result: repeated first-column Householder updates over a fixed rectangular
  panel are now implementation-backed.  This is still not the full QR loop,
  because the real algorithm shrinks the trailing panel after each step.
- Added exact trailing-panel operations `panelDropFirstRow`,
  `panelDropFirstCol`, and `trailingPanel`, and the concrete rounded one-step
  shrink operation `fl_householderTrailingPanelStep`.
- Result: the QR rebuild now has a concrete definition for one move from an
  `(m+1) × (p+1)` panel to the updated `m × p` trailing panel.  The next gap is
  the dependent induction over shrinking panel dimensions, plus
  triangularization/package theorems.
- Added `frobNormSq_trailingPanel_le`, `frobNorm_trailingPanel_le`, and
  `fl_householderTrailingPanelStep_residual`.
- Result: the concrete shrinking step now has a residual form with a norm bound
  obtained by restricting the full-panel residual.  This is a useful one-step
  bridge for the future dependent QR induction, but it still does not prove
  exact zeroing of the first column or final triangularization.
- Added exact Householder zeroing lemmas:
  `householderVector_dot_original_eq_scale_mul_zero`,
  `householder_constructed_matMulVec_first`, and
  `householder_constructed_matMulVec_tail_zero`.
- Result: one exact constructed Householder reflector now formally maps its
  source column to `-s e_0`, proving the exact tail-zeroing fact needed for QR
  triangularization.  Remaining work is to compose this with the rounded
  shrinking panel loop and package the final QR theorem.
- Added panel-level exact triangularization bridges:
  `householder_first_column_panel_exact_first` and
  `householder_first_column_panel_exact_tail_zero`.
- Result: the exact zeroing fact now applies to the first column of a
  rectangular panel after a constructed Householder reflector.  This is the
  algebraic triangularization side of one QR panel step; it still needs to be
  combined with the rounded residual step in the dependent shrinking-panel loop.
- Added panel decomposition infrastructure:
  `panelTopLeft`, `panelTopRowTail`, `panelFirstColumnTail`, and
  `panelFirstColumnTailZero`, plus exact bridges
  `householder_panel_exact_topLeft` and
  `householder_panel_exact_firstColumnTailZero`.
- Result: one exact Householder panel step now exposes the top-left result and
  first-column tail-zero property in named panel-shape predicates.  This is
  preparation for the full shrinking QR loop, not a final QR theorem.
- Added `fl_householder_first_column_panel_step_residual_and_shape`.
- Result: one concrete rounded first-column Householder panel step now packages
  the residual bound for the computed full-panel update together with the exact
  top-left and first-column-tail-zero facts for the underlying exact reflector.
  This is the one-step implementation-backed panel bridge needed before the
  dependent shrinking-panel induction.
- Added `IsUpperTriangular` and
  `StructuredHouseholderQRBackwardError`.
- Result: the QR target contract now has an explicit shape-aware version.  This
  prevents overclaiming: the existing backward-error theorem proves the
  normwise relation, while the future end-to-end QR theorem must additionally
  prove upper triangularity from the concrete loop.
- Added `HouseholderPanelState`, `householderPanelStateStep`, and
  `householderPanelStateIterate`.
- Result: the rebuild now has a concrete dependent active-panel loop substrate.
  It shrinks nonempty panels by calling `fl_householderTrailingPanelStep`.
  This still is not a full QR factorization algorithm because it does not store
  accumulated orthogonal factors or completed rows of `R`.
- Added `householderPanelStateStep_nonempty_residual_and_shape`.
- Result: a nonempty concrete active-panel state transition now has a proved
  residual representation for the next active panel and exact one-step shape
  facts for the underlying reflector update.  The next gap is induction over
  `householderPanelStateIterate` and a richer state carrying accumulated `Q`
  and completed `R` data.
- Added `HouseholderPanelStepReady` and `HouseholderPanelRunReady`, with head
  and tail lemmas for induction.
- Result: the concrete active-panel iterator now has a named per-step readiness
  hypothesis: nonzero first column plus the required `gammaValid` condition.
  This is preparation for repeated-step proofs; it is not a replacement for the
  actual induction over residual accumulation and triangular structure.
- Added `householderPanelStateStep_nonempty_residual_and_shape_of_ready`.
- Result: future induction proofs can consume `HouseholderPanelStepReady`
  directly when invoking the one-step residual/shape bridge.
- Added `householderPanelRunReady_succ_iff`.
- Result: the readiness predicate now has the standard induction split:
  current step ready plus ready tail after one concrete state transition.
- Added `householderPanelStepReady_nonempty_of_global_gammaValid`.
- Result: future QR loop proofs can carry one global gamma-validity assumption
  for the original row dimension and derive each smaller active-panel
  per-step validity condition by monotonicity.
- Added `embedTrailingOne`.
- Result: the rebuild now has a named exact embedding for viewing an active
  trailing-panel reflector as a full-size matrix with leading identity block.
  The next proof target is orthogonality/composition for this embedding.
- Added embedding algebra:
  `matTranspose_embedTrailingOne`, `matMul_embedTrailingOne`,
  `embedTrailingOne_idMatrix`, and `embedTrailingOne_orthogonal`.
- Result: orthogonal active-panel reflectors can now be lifted to full-size
  orthogonal transformations, which is necessary for composing the final `Q`.
- Updated next action: define/model the actual Householder QR loop that selects
  trailing-column vectors and applies rectangular panel updates; then prove the
  triangularization/package step and add a sourced first-order/gamma-collapse
  lemma if we want Higham's `r*c`/`γ_cm` style final bound.

## Phase 6: QR Rebuild

Do not start this phase until Householder/Givens low-level bridges exist.

- [ ] `QR/HouseholderSpec.lean`: replace permanent assumption status with bridge
  theorem from concrete apply kernel.
- [ ] `QR/HouseholderQR.lean`: add concrete QR loop or an explicitly modeled
  sequence of concrete Householder steps.
- [ ] Prove the concrete sequence satisfies `OrthogonalSequenceBackwardError`.
- [ ] Recast `householder_qr_backward` as either a final theorem using the
  bridge or keep the current wrapper and add a new end-to-end theorem.
- [ ] `QR/GivensSpec.lean`: build concrete Givens rotation/application bridge.
- [ ] `QR/GivensQR.lean`: rebuild after Givens sequence bridge.
- [ ] `QR/QRSolve.lean`: combine QR bridge with triangular solve proofs.

Phase 6 update, 2026-06-02:

- Added the concrete supplied-parameter Givens application bridge
  `fl_givensApply_supplied_app_error`.
- Result: if exact `c,s` satisfy `c^2+s^2=1`, the concrete
  `fl_givensApply` kernel satisfies `GivensAppError` with the conservative
  implementation-backed bound `gamma fp 2 * ‖givensRotation n p q c s‖_F`.
- Boundary: this is not yet the full Higham Lemma 18.7 analysis for constructing
  and applying a Givens rotation.  The rounded rotation-parameter construction
  and the full `fl_givens_qr` loop remain pending.
- Added exact Givens coefficient construction from Higham equation (18.14):
  `givensDenom`, `givensC`, and `givensS`.
- Added exact coefficient facts:
  `givensCoeff_norm_sq`, `givensCoeff_zero_second`,
  `givensCoeff_first_component`, and `givensRotation_constructed_orthogonal`.
- Added rounded coefficient kernels `fl_givensDenom`, `fl_givensC`, and
  `fl_givensS`.  The rounded denominator reuses `fl_norm2`, keeping the
  square-root/domain proof obligations aligned with the existing norm layer.
- Boundary: Higham explicitly omits the proof of Lemma 18.6.  The Lean rebuild
  still needs to prove the bridge from these concrete rounded kernels to
  `c_hat = c(1+theta_4)` and `s_hat = s(1+theta'_4)` before claiming the full
  Givens rotation construction is implementation-backed.
- Added conservative coefficient bridges:
  `fl_givensC_relative_error_conservative` and
  `fl_givensS_relative_error_conservative`.
- Added `GivensCoeffError` and `fl_givensCoeffError_conservative` as the
  reusable interface for later Givens application and sequence proofs.
- Result: the concrete coefficient kernels are now implementation-backed with
  `gamma fp 6` bounds, derived from the existing `fl_norm2` relative-error
  theorem and rounded division via `gamma_inv_mul_roundoff`.
- Boundary: the conservative `gamma 6` bridge is useful for continuing the
  implementation rebuild, but it is not the exact Higham Lemma 18.6 `gamma_4`
  constant.  The next decision is whether to pursue the sharper source constant
  immediately or carry the conservative bridge into the Givens sequence theorem.
- Added `fl_givensApply_coeffError_app_error`, which combines a coefficient
  relative-error contract with the concrete rounded Givens application kernel.
- Added `fl_givensApply_computed_app_error_conservative`, proving the concrete
  path
  `fl_givensC`/`fl_givensS` -> `fl_givensApply`
  satisfies `GivensAppError` for the exact constructed rotation.
- Bound: `gamma fp 8 * frobNorm G`.  This is derived from the current
  conservative `gamma fp 6` coefficient bridge plus the two application
  roundings.  It is implementation-backed but weaker than Higham's Lemma 18.7
  presentation `sqrt(2) * gamma_6`.
- New next step: define the concrete Givens sequence/update kernel and prove
  that a sequence of these implementation-backed applications satisfies the
  sequence contract consumed by `GivensQR.lean`, unless we decide to sharpen
  Lemma 18.6/18.7 first.
- Added `QR/GivensMatrixStep.lean`.
- Added concrete matrix kernels `fl_givensApplyMatrix` and
  `fl_givensApplyMatrixRect`, columnwise Givens step contracts, and residual
  aggregation lemmas.
- Added `fl_givensApply_computed_matrix_step_error` and the rectangular variant,
  lifting the concrete computed-coefficient vector theorem columnwise.
- Added `fl_givens_sequence_backward_error` and
  `fl_givens_panel_sequence_backward_error` in `QR/GivensQR.lean`.
- Result: any supplied concrete sequence of computed Givens matrix/panel
  updates now accumulates through the residual-form orthogonal sequence theorem.
- Boundary: this still is not full Givens QR.  The remaining implementation
  gap is the annihilation schedule: define the actual row-pair/coefficient
  sequence from the evolving matrix, prove each step has the required nonzero
  two-vector and uniform bound, and prove the final matrix has the QR
  triangular shape.
- Added exact Frobenius norm facts for orthogonal matrices:
  `IsOrthogonal.frobNormSq_eq_card` and `IsOrthogonal.frobNorm_eq_sqrt_card`.
- Added uniform sequence corollaries:
  `fl_givens_sequence_backward_error_uniform` and
  `fl_givens_panel_sequence_backward_error_uniform`.
- Result: for supplied concrete Givens update sequences, the per-step bound no
  longer needs to be supplied manually; it is discharged from orthogonality as
  `gamma fp 8 * sqrt(dimension)`.
- Added concrete current-matrix column steps:
  `fl_givensColumnStepMatrix` and `fl_givensColumnStepMatrixRect`.
- Added bridge theorems:
  `fl_givensColumnStep_matrix_step_error` and rectangular variant.
- Added sequence corollaries:
  `fl_givens_column_sequence_backward_error_uniform` and
  `fl_givens_column_panel_sequence_backward_error_uniform`.
- Result: Givens sequence proofs can now use coefficients read from the evolving
  matrix column at each step, instead of separate external `xi`/`xj` streams.
- Remaining full-QR gap: formalize the annihilation schedule itself, prove
  nonzero guards for the selected row pairs or handle zero rotations, and prove
  the final output is upper triangular.

## Phase 7: Cholesky Rebuild

Do not call Cholesky solve end-to-end until the factorization bridge exists.

- [ ] Source-check Cholesky factorization theorem/bounds used in
  `CholeskySpec.lean`.
- [ ] Define concrete rounded Cholesky factorization if absent.
- [ ] Use `fl_sqrt`, `fl_div`, `fl_dotProduct`/update kernels as needed.
- [ ] Prove bridge to `CholeskyBackwardError`.
- [ ] Revisit `CholeskySolve.lean` and mark solve end-to-end only after the
  factorization bridge.
- [ ] Revisit PSD/Demmel/nonsymmetric/indefinite variants after base Cholesky.

## Phase 8: General LU Rebuild

- [ ] Source-check Higham Ch. 9 LU/GE theorem boundaries.
- [ ] Define or locate concrete rounded no-pivot Gaussian elimination.
- [ ] Prove bridge to `LUBackwardError`.
- [ ] Extend to Doolittle if it is the chosen concrete representation.
- [ ] Decide pivoting scope before proving `PermutedLUBackwardError`.
- [ ] Revisit `LUSolve.lean` after LU bridge; triangular solves should already
  be available.
- [ ] Revisit growth-factor and special-matrix modules after the bridge.
- [ ] Defer `BlockLU.lean` until scalar/general LU bridge is stable.

## Phase 9: Least Squares

- [ ] `LSNormalEquations.lean`: prove `GramProductError` from `fl_matMul`.
- [ ] `LSNormalEquations.lean`: prove `GramVecError` from `fl_matVec`.
- [ ] Combine with implementation-backed Cholesky solve once available.
- [ ] `LSQRSolve.lean`: wait for implementation-backed QR solve.
- [ ] `LSPerturbation.lean`: source-check exact perturbation statements.

## Phase 10: Matrix Inversion, Gauss-Jordan, Refinement

- [ ] `MatrixInversion.lean`: classify each method as exact, contract-only, or
  implementation-backed after LU/triangular bridges.
- [ ] `GaussJordan.lean`: determine whether to build concrete GJE or leave as
  specification-transfer with honest documentation.
- [ ] `IterativeRefinement.lean`: prove `ResidualError` from `fl_residual` where
  possible.
- [ ] Keep solver-level `SolverSpec` abstract unless a concrete solver is
  explicitly supplied.

## Phase 11: Remaining Higher-Level Modules

- [ ] `StationaryIteration.lean`: decide whether this is exact iteration theory
  or needs rounded implementation modeling.
- [ ] `MatrixPowers.lean`: source-check exact/Jordan assumptions.
- [ ] `CondEstimation.lean`: decide whether FP estimator modeling is in scope.
- [ ] `Sylvester/*`: classify exact perturbation vs algorithmic stability.
- [ ] `Underdetermined/*`: revisit after Cholesky/QR availability.
- [ ] `FastMatMul.lean`: separate source audit required before implementation
  work; current structures appear contract-level.

## Current Recommended Starting Point

Continue Phase 5 at the Householder sequence boundary.  Householder construction
now has an implementation-backed Lemma 18.1 bridge for nonzero vectors, equation
(18.3) is implementation-backed from that construction bridge, and the concrete
application kernel satisfies the one-vector and columnwise Lemma 18.2 style
contracts.  Column-dependent per-column perturbations now aggregate to a single
matrix residual bound for one reflector step, and that residual bound advances
the orthogonal-sequence invariant for one step.  Repeated residual accumulation
is now proved with a conservative recurrence bound.  Exact embedding lemmas now
show that a trailing-block transformation preserves the top row of a full panel
and transforms the trailing panel by the smaller active-panel multiplication.
Exact panel reconstruction now records the intended QR `R` bookkeeping: keep
the computed top row, set the completed first-column tail to zero by
construction, and recurse on the trailing panel.  This gives the future
`R_hat` algorithm a direct upper-triangularity proof rather than assuming
rounded arithmetic creates exact structural zeros.  The first recursive
rounded `R`-producing loop, `fl_householderQRPanel_R`, is now defined, with
square alias `fl_householderQR_R` and an upper-triangularity theorem for the
square output.  Projection lemmas now state that the loop stores the current
rounded top row, structurally zeroes the completed first-column tail, and
recurses exactly on `fl_householderTrailingPanelStep`.  The next concrete proof
obligation is the backward-error bridge for this recursive loop: relate its
computed trailing-panel recursion to the residual-sequence theorem and the
final `HouseholderQRBackwardError` contract.  The stored first-column residual
bridge is now proved: zeroing the completed first-column tail preserves the
same one-step residual bound because the exact reflector already has zeros in
that tail and the Frobenius norm of the residual cannot increase when that
slice is removed.  Tail perturbation embedding and block-lift algebra are now
proved: a tail backward representation can be lifted to a full panel by using
`embedTrailingOne`, with the embedded tail perturbation preserving Frobenius
norm exactly.  The recursive `HouseholderQRPanelReady` predicate and
`householderQRPanelBackwardCoeff` coefficient are now defined, setting up the
statement shape for the implementation-backed QR backward-error induction.
The rectangular induction target `HouseholderQRPanelBackwardError` is now
defined with empty-row and empty-column base cases; the square final theorem
will specialize this target back to the existing QR contract.  The generic
recursive cons theorem is now proved: a stored one-step residual bound for the
current panel plus a backward-error proof for the trailing panel yields a
full-panel backward-error proof, with the recursive coefficient update
`c + α*(1+c)`.  The concrete recursive panel loop now has its
implementation-backed theorem: `fl_householderQRPanel_R_backward_error` proves
that `fl_householderQRPanel_R` satisfies `HouseholderQRPanelBackwardError`
under `HouseholderQRPanelReady`.  The next QR step is the square wrapper that
turns this rectangular representation into the existing
`HouseholderQRBackwardError` and structured QR contract.  That wrapper is now
also proved: `fl_householderQR_R_backward_error` and
`fl_householderQR_R_structured_backward_error` specialize the rectangular
recursive theorem to square matrices and combine it with the constructive
upper-triangularity proof.  The next QR-solve layer now has its component
packaging theorem, `qr_solve_backward_error_from_components`, which turns QR,
`Qᵀb`, and triangular-solve component hypotheses into `QRSolveBackwardError`.
This is algebraic composition, not yet a concrete `fl_qr_solve` bridge.
Concrete QR-solve objects are now defined: `fl_householderQRPanel_rhs` applies
the same rounded Householder reflector sequence to the right-hand side,
`fl_householderQR_rhs` is the square specialization, and
`fl_householderQR_solve` feeds that result into `fl_backSub` with the computed
`fl_householderQR_R`.  The remaining proof obligation is the RHS-transform
backward error and final solve theorem.  The one-step RHS residual bridge is
now proved: `fl_householder_first_column_rhs_step_residual` exposes the current
computed RHS reflector update as `P*b + e` with `e = ΔP*b` and the same
Householder application bound as the panel step.  Exact vector embedding and
tail-lift lemmas are now available, matching the panel `embedTrailingOne`
algebra for right-hand-side recursion.

Update: exact componentwise matrix-vector bounds were added in
`MatrixAlgebra.lean`, including Frobenius-to-component residual bounds and
crude orthogonal transport bounds.  `QRSolve.lean` now has
`HouseholderAppError.exists_residual_vector_bound` and
`fl_householder_first_column_rhs_step_residual_bound`, so the concrete
one-step RHS reflector update has an explicit componentwise residual bound.
The recursive RHS sequence bridge is also now proved:
`HouseholderQRRhsPanelBackwardError`,
`householderQRRhsPanelBackwardBound`,
`householder_qr_rhs_panel_backward_cons`,
`fl_householderQRPanel_rhs_backward_error`, and
`fl_householderQR_rhs_backward_error`.  The shared-orthogonal-factor gap is now
closed by `HouseholderQRPanelSolveBackwardError`,
`householder_qr_panel_solve_backward_cons`,
`fl_householderQRPanel_solve_components_backward_error`, and
`fl_householderQR_solve_components_backward_error`.  The final concrete solve
bridge `fl_householderQR_solve_backward_error` is proved by combining the
shared-`Q` QR/RHS theorem with `backSub_backward_error`.  This is an
implementation-backed solve theorem, with explicit side assumptions and a
recursive/conservative bound rather than a collapsed asymptotic textbook
constant.

Do not begin full QR, Cholesky, or general LU until their lower-level kernels
and source boundaries are clear.

Givens QR rebuild started after Householder QR solve:

- Added `fl_givensApply` in `QR/GivensSpec.lean` for the concrete
  supplied-parameter application of a Givens rotation.
- Added exact unroll lemmas for the affected `p` and `q` components and for
  unaffected copied components.
- Current status is not yet implementation-backed for Lemma 18.7:
  `GivensAppError` remains a contract until the rounded application bridge and
  rotation-parameter construction are proved.
