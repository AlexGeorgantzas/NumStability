-- Analysis/InstabilityWithoutCancellation.lean
--
-- Exact baselines for Higham Chapter 1, Section 1.12.

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.LU.GaussianElimination

namespace NumStability

open scoped BigOperators

/-!
# Instability Without Cancellation

Higham Chapter 1, Section 1.12 gives examples showing that the absence of
subtractive cancellation does not guarantee floating-point accuracy.  This file
records exact real-arithmetic baselines and selected explicit finite-format
replacement models.  Under-specified historical Fortran/calculator outputs are
ledgered as empirical-source-output in the Chapter 1 audit rather than treated
as required Lean theorem targets.

Some reverse-summation definitions below retain the old D1 route names because
they are useful optional repository-model certificates.  Under the current
Chapter 1 gate they are archived support material, not active obligations to
reconstruct the historical Fortran printout.
-/

/-! ## No-pivot LU example -/

/-- Higham §1.12.1's well-conditioned 2-by-2 matrix for the no-pivot LU
example. -/
noncomputable def noPivotExampleA (ε : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![ε, -1], ![1, 1]]

/-- The inverse of `noPivotExampleA ε` when `1 + ε` is nonzero. -/
noncomputable def noPivotExampleAInv (ε : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![1 / (1 + ε), 1 / (1 + ε)], ![-1 / (1 + ε), ε / (1 + ε)]]

/-- The computed lower triangular factor in the no-pivot example, assuming
`l21 = ε^{-1}` is formed exactly. -/
noncomputable def noPivotRoundedL (ε : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![1, 0], ![ε⁻¹, 1]]

/-- The computed upper triangular factor in the no-pivot example after the
rounded update `fl(1 + ε^{-1}) = ε^{-1}`. -/
noncomputable def noPivotRoundedU (ε : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![ε, -1], ![0, ε⁻¹]]

/-- The exact reproduction error displayed in Higham §1.12.1. -/
noncomputable def noPivotExampleFailureMatrix : Fin 2 → Fin 2 → ℝ :=
  ![![0, 0], ![0, 1]]

/-- The row interchange used by partial pivoting for Higham §1.12.1's
example when the second row supplies the first pivot. -/
noncomputable def noPivotPartialPivotSwap : Fin 2 → Fin 2
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0

/-- The exact unit lower-triangular factor after the partial-pivoting row
interchange in Higham §1.12.1. -/
noncomputable def noPivotPartialPivotL (ε : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![1, 0], ![ε, 1]]

/-- The exact upper-triangular factor after the partial-pivoting row
interchange in Higham §1.12.1. -/
noncomputable def noPivotPartialPivotU (ε : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![1, 1], ![0, -(1 + ε)]]

/-- The concrete IEEE-single rounded `U` produced by the primitive pivoted update
for `ε = 2^{-24}`: the final update `fl((-1)-ε)` rounds to `-1`. -/
noncomputable def noPivotPartialPivotIeeeSingleRoundedU : Fin 2 → Fin 2 → ℝ :=
  ![![1, 1], ![0, -1]]

/-- The rounded pivoted `U` shape obtained whenever the final pivoted update
`fl((-1)-ε)` rounds to `-1`.  This abstracts the concrete IEEE-single
`ε = 2^{-24}` trace. -/
noncomputable def noPivotPartialPivotRoundedU : Fin 2 → Fin 2 → ℝ :=
  ![![1, 1], ![0, -1]]

/-- The pivoted primitive-operation `U` trace with abstract `FPModel`
operations: form `fl(ε/1)`, multiply by `1`, then update `(-1)-...`. -/
noncomputable def noPivotPartialPivotPrimitiveRoundedU
    (fp : FPModel) (ε : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![1, 1], ![0, fp.fl_sub (-1) (fp.fl_mul (fp.fl_div ε 1) 1)]]

/-- If the pivoted primitive operations satisfy the displayed small-`ε`
rounding behavior, then the abstract primitive trace produces the rounded
`U` with `U_22 = -1`. -/
theorem noPivotPartialPivotPrimitiveRoundedU_eq_roundedU_of_rounds
    (fp : FPModel) {ε : ℝ}
    (hdiv : fp.fl_div ε 1 = ε)
    (hmul : fp.fl_mul ε 1 = ε)
    (hsub : fp.fl_sub (-1) ε = -1) :
    noPivotPartialPivotPrimitiveRoundedU fp ε =
      noPivotPartialPivotRoundedU := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [noPivotPartialPivotPrimitiveRoundedU, noPivotPartialPivotRoundedU,
      hdiv, hmul, hsub]

/-- The partial-pivoting row interchange is a permutation of the two rows. -/
theorem noPivotPartialPivotSwap_bijective :
    IsPermutation 2 noPivotPartialPivotSwap := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp [noPivotPartialPivotSwap] at h ⊢
  · intro b
    fin_cases b
    · exact ⟨1, by simp [noPivotPartialPivotSwap]⟩
    · exact ⟨0, by simp [noPivotPartialPivotSwap]⟩

/-- After swapping rows, Higham §1.12.1's matrix has the exact pivoted
factorization `P*A = L*U`. -/
theorem noPivotPartialPivotLUFactSpec (ε : ℝ) :
    PermutedLUFactSpec 2 (noPivotExampleA ε)
      (noPivotPartialPivotL ε) (noPivotPartialPivotU ε)
      noPivotPartialPivotSwap := by
  refine ⟨noPivotPartialPivotSwap_bijective, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [noPivotPartialPivotL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [noPivotPartialPivotL] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [noPivotPartialPivotU] at hij ⊢
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [noPivotPartialPivotL, noPivotPartialPivotU, noPivotExampleA,
        noPivotPartialPivotSwap]

/-- In the source regime `0 <= ε <= 1`, the partial-pivoting multiplier has
magnitude at most one. -/
theorem noPivotPartialPivot_multiplier_abs_le_one {ε : ℝ}
    (hεnonneg : 0 ≤ ε) (hεle : ε ≤ 1) :
    |noPivotPartialPivotL ε 1 0| ≤ 1 := by
  simpa [noPivotPartialPivotL, abs_of_nonneg hεnonneg] using hεle

/-- Under the source regime `0 <= ε`, the exact pivoted `U` has nonzero
diagonal entries. -/
theorem noPivotPartialPivotU_diag_nonzero {ε : ℝ} (hεnonneg : 0 ≤ ε) :
    ∀ i : Fin 2, noPivotPartialPivotU ε i i ≠ 0 := by
  intro i
  fin_cases i
  · simp [noPivotPartialPivotU]
  · have hpos : 0 < 1 + ε := by linarith
    have hne : -(1 + ε) ≠ 0 := neg_ne_zero.mpr hpos.ne'
    simpa [noPivotPartialPivotU, add_comm, add_left_comm, add_assoc] using hne

/-- The exact partial-pivoting branch for Higham §1.12.1 also satisfies the
pivoted LU backward-error surface with zero perturbation.  This is the
backward-error certificate for the exact pivoted factors; a primitive rounded
operation trace remains a separate obligation. -/
theorem noPivotPartialPivotLUBackwardError_zero (ε : ℝ) :
    PermutedLUBackwardError 2 (noPivotExampleA ε)
      (noPivotPartialPivotL ε) (noPivotPartialPivotU ε)
      noPivotPartialPivotSwap 0 := by
  have hspec := noPivotPartialPivotLUFactSpec ε
  refine
    { perm := hspec.perm
      L_diag := hspec.L_diag
      L_upper_zero := hspec.L_upper_zero
      U_lower_zero := hspec.U_lower_zero
      backward_bound := ?_ }
  intro i j
  have hprod := hspec.product_eq i j
  rw [hprod]
  simp

/-- General rounded-pivot bridge for Higham §1.12.1.  If the pivoted primitive
trace has rounded the final update to `U_22 = -1`, then for every `ε >= 0`
the resulting rounded pivoted factors satisfy the componentwise pivoted
LU backward-error certificate with radius `ε`. -/
theorem noPivotPartialPivotRoundedLUBackwardError {ε : ℝ}
    (hεnonneg : 0 ≤ ε) :
    PermutedLUBackwardError 2 (noPivotExampleA ε)
      (noPivotPartialPivotL ε) noPivotPartialPivotRoundedU
      noPivotPartialPivotSwap ε := by
  refine
    { perm := noPivotPartialPivotSwap_bijective
      L_diag := ?_
      L_upper_zero := ?_
      U_lower_zero := ?_
      backward_bound := ?_ }
  · intro i
    fin_cases i <;> simp [noPivotPartialPivotL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [noPivotPartialPivotL] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [noPivotPartialPivotRoundedU] at hij ⊢
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [noPivotExampleA, noPivotPartialPivotL, noPivotPartialPivotRoundedU,
        noPivotPartialPivotSwap, Fin.sum_univ_two]
    all_goals
      first
      | exact hεnonneg
      | exact mul_nonneg hεnonneg (abs_nonneg ε)
      | rw [abs_of_nonneg hεnonneg]
        nlinarith [hεnonneg]

/-- The abstract primitive pivoted trace inherits the same backward-error
certificate once its three primitive rounded-operation facts are supplied. -/
theorem noPivotPartialPivotPrimitiveRoundedLUBackwardError_of_rounds
    (fp : FPModel) {ε : ℝ} (hεnonneg : 0 ≤ ε)
    (hdiv : fp.fl_div ε 1 = ε)
    (hmul : fp.fl_mul ε 1 = ε)
    (hsub : fp.fl_sub (-1) ε = -1) :
    PermutedLUBackwardError 2 (noPivotExampleA ε)
      (noPivotPartialPivotL ε)
      (noPivotPartialPivotPrimitiveRoundedU fp ε)
      noPivotPartialPivotSwap ε := by
  rw [noPivotPartialPivotPrimitiveRoundedU_eq_roundedU_of_rounds fp hdiv hmul hsub]
  exact noPivotPartialPivotRoundedLUBackwardError hεnonneg

/-- The displayed inverse is a two-sided inverse for the no-pivot example. -/
theorem noPivotExampleAInv_isInverse {ε : ℝ} (hden : 1 + ε ≠ 0) :
    IsInverse 2 (noPivotExampleA ε) (noPivotExampleAInv ε) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [noPivotExampleA, noPivotExampleAInv] <;>
      field_simp [hden] <;> ring
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [noPivotExampleA, noPivotExampleAInv] <;>
      field_simp [hden] <;> ring

/-- The matrix in Higham §1.12.1 has infinity norm `2` for `0 <= ε <= 1`. -/
theorem noPivotExampleA_infNorm_eq {ε : ℝ} (hεnonneg : 0 ≤ ε)
    (hεle : ε ≤ 1) :
    infNorm (noPivotExampleA ε) = 2 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;>
        simp [noPivotExampleA, abs_of_nonneg hεnonneg] <;> linarith
    · norm_num
  · have hrow := row_sum_le_infNorm (noPivotExampleA ε) (1 : Fin 2)
    have htwo : (1 : ℝ) + 1 ≤ infNorm (noPivotExampleA ε) := by
      simpa [noPivotExampleA] using hrow
    norm_num at htwo
    exact htwo

/-- The displayed inverse has infinity norm `2/(1+ε)` for `0 <= ε <= 1`. -/
theorem noPivotExampleAInv_infNorm_eq {ε : ℝ} (hεnonneg : 0 ≤ ε)
    (hεle : ε ≤ 1) :
    infNorm (noPivotExampleAInv ε) = 2 / (1 + ε) := by
  have hdenpos : 0 < 1 + ε := by linarith
  have hdenne : 1 + ε ≠ 0 := ne_of_gt hdenpos
  have hdenabs : |1 + ε| = 1 + ε := abs_of_pos hdenpos
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i
      · simp [noPivotExampleAInv, hdenabs]
        rw [show (1 + ε)⁻¹ + (1 + ε)⁻¹ = 2 / (1 + ε) by ring]
      · have hneg_nonpos : -1 / (1 + ε) ≤ 0 := by
          have hpos : 0 < 1 / (1 + ε) := one_div_pos.mpr hdenpos
          rw [show -1 / (1 + ε) = -(1 / (1 + ε)) by ring]
          exact neg_nonpos.mpr (le_of_lt hpos)
        have hfrac_nonneg : 0 ≤ ε / (1 + ε) := by positivity
        simp [noPivotExampleAInv, abs_of_nonpos hneg_nonpos,
          abs_of_nonneg hfrac_nonneg]
        field_simp [hdenne]
        nlinarith
    · positivity
  · have hrow := row_sum_le_infNorm (noPivotExampleAInv ε) (0 : Fin 2)
    have hrow' : (1 + ε)⁻¹ + (1 + ε)⁻¹ ≤
        infNorm (noPivotExampleAInv ε) := by
      simpa [noPivotExampleAInv, hdenabs] using hrow
    rw [show 2 / (1 + ε) = (1 + ε)⁻¹ + (1 + ε)⁻¹ by ring]
    exact hrow'

/-- Higham's displayed conditioning formula
`kappa_infty(A) = ||A||_infty ||A^{-1}||_infty = 4/(1+ε)` for the
no-pivot example. -/
theorem noPivotExample_kappaInf_eq {ε : ℝ} (hεpos : 0 < ε) (hεle : ε ≤ 1) :
    infNorm (noPivotExampleA ε) * infNorm (noPivotExampleAInv ε) =
      4 / (1 + ε) := by
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  rw [noPivotExampleA_infNorm_eq hεnonneg hεle,
    noPivotExampleAInv_infNorm_eq hεnonneg hεle]
  ring

/-- If the no-pivot update rounds `1 + ε^{-1}` to `ε^{-1}`, the computed LU
factors reproduce the wrong matrix and leave the displayed `(2,2)` error. -/
theorem noPivotRoundedLU_error_matrix {ε : ℝ} (hε : ε ≠ 0) :
    (fun i j : Fin 2 =>
        noPivotExampleA ε i j -
          matMul 2 (noPivotRoundedL ε) (noPivotRoundedU ε) i j) =
      noPivotExampleFailureMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [noPivotExampleA, noPivotRoundedL, noPivotRoundedU,
      noPivotExampleFailureMatrix, matMul, hε]

/-- Consequently the rounded no-pivot factors do not reproduce the input
matrix. -/
theorem noPivotRoundedLU_not_reproduce_A (ε : ℝ) :
    matMul 2 (noPivotRoundedL ε) (noPivotRoundedU ε) ≠ noPivotExampleA ε := by
  intro h
  have hentry := congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2)
  simp [noPivotExampleA, noPivotRoundedL, noPivotRoundedU, matMul] at hentry

/-- A concrete IEEE-single value satisfying Higham §1.12.1's "sufficiently
small" condition for the no-pivot update example. -/
noncomputable def noPivotIeeeSingleSmallEpsilon : ℝ :=
  1 / (2 : ℝ) ^ 24

/-- The concrete `ε = 2^{-24}` used for the single-precision §1.12.1 examples
is itself representable in IEEE single precision. -/
theorem noPivotIeeeSingleSmallEpsilon_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      noPivotIeeeSingleSmallEpsilon := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 8388608
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have he : fmt.exponentInRange (-23 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, m, (-23 : ℤ), hm, he, ?_⟩)
  norm_num [noPivotIeeeSingleSmallEpsilon, m, fmt,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- In the concrete partial-pivoting path for `ε = 2^{-24}`, the multiplier
division `fl(ε/1)` is exact in IEEE single nearest/even arithmetic. -/
theorem noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        noPivotIeeeSingleSmallEpsilon 1 =
      noPivotIeeeSingleSmallEpsilon := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfin : fmt.finiteSystem
      (BasicOp.exact BasicOp.div noPivotIeeeSingleSmallEpsilon 1) := by
    simpa [fmt, BasicOp.exact] using noPivotIeeeSingleSmallEpsilon_finiteSystem
  simpa [fmt, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div)
      (x := noPivotIeeeSingleSmallEpsilon) (y := 1) hfin)

/-- In the concrete partial-pivoting path for `ε = 2^{-24}`, the product
`fl(ε*1)` is exact in IEEE single nearest/even arithmetic. -/
theorem noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        noPivotIeeeSingleSmallEpsilon 1 =
      noPivotIeeeSingleSmallEpsilon := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfin : fmt.finiteSystem
      (BasicOp.exact BasicOp.mul noPivotIeeeSingleSmallEpsilon 1) := by
    simpa [fmt, BasicOp.exact] using noPivotIeeeSingleSmallEpsilon_finiteSystem
  simpa [fmt, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul)
      (x := noPivotIeeeSingleSmallEpsilon) (y := 1) hfin)

/-- In IEEE single precision with nearest/even rounding, the concrete
`ε = 2^{-24}` instance of Higham §1.12.1 satisfies
`fl(1 + ε^{-1}) = ε^{-1}`.  The exact sum is the midpoint between `2^24`
and the next binary32 value, and the even mantissa of `2^24` selects the
left endpoint. -/
theorem noPivotIeeeSingle_add_one_inv_epsilon_rounds_to_inv :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 (noPivotIeeeSingleSmallEpsilon⁻¹) =
      noPivotIeeeSingleSmallEpsilon⁻¹ := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 8388608
  let a : ℝ := fmt.normalizedValue false m 25
  let b : ℝ := fmt.normalizedValue false (m + 1) 25
  let x : ℝ := 1 + a
  have heps_inv : noPivotIeeeSingleSmallEpsilon⁻¹ = a := by
    norm_num [noPivotIeeeSingleSmallEpsilon, a, m, fmt,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
    rfl
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (25 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, m, fmt,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, a, m, fmt,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, a, m, fmt,
        FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        x = (16777217 : ℝ) := by
          norm_num [x, a, m, fmt,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue,
            FloatingPointFormat.signValue,
            FloatingPointFormat.betaR,
            zpow_neg]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft :
      a = fmt.normalizedValue false m (25 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    have hxa : x - a = (1 : ℝ) := by
      norm_num [x, a, m, fmt,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
      rfl
    have hxb : x - b = -(1 : ℝ) := by
      norm_num [x, a, b, m, fmt,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    rw [hxa, hxb, abs_neg, abs_one]
  have heven : FloatingPointFormat.evenMantissa m := by
    norm_num [FloatingPointFormat.evenMantissa, m]
  have hround :
      fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 (noPivotIeeeSingleSmallEpsilon⁻¹)
        = fmt.finiteRoundToEven x := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
            heps_inv, x, fmt]
    _ = noPivotIeeeSingleSmallEpsilon⁻¹ := by
      rw [hround, heps_inv]

/-- Non-enumerative no-pivot inverse-update threshold for the next binary32
binade: if `epsilon^{-1}` is a positive IEEE-single normalized value with
exponent `26` and a same-binade successor, then adding `1` rounds back to
`epsilon^{-1}`.  The spacing in this binade is `4`, so the exact sum is
strictly closer to the left endpoint. -/
theorem noPivotIeeeSingle_add_one_normalized_exp26_rounds_to_self
    {m : ℕ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1)) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          (26 : ℤ)) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
        (26 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false m (26 : ℤ)
  let b : ℝ := fmt.normalizedValue false (m + 1) (26 : ℤ)
  let x : ℝ := 1 + a
  have hexp : fmt.exponentInRange (26 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have haSystem : fmt.normalizedSystem a := by
    exact ⟨false, m, (26 : ℤ), hm, hexp, rfl⟩
  have hbSystem : fmt.normalizedSystem b := by
    exact ⟨false, m + 1, (26 : ℤ), hmnext, hexp, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (26 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_eq : a = (m : ℝ) * 4 := by
    norm_num [a, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_eq : b = ((m : ℝ) + 1) * 4 := by
    norm_num [b, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    constructor
    · dsimp [x]
      linarith
    · change 1 + a < b
      rw [ha_eq, hb_eq]
      linarith
  have hapos : 0 < a := by
    simpa [a, fmt] using
      fmt.normalizedValue_false_pos (m := m) (e := (26 : ℤ)) hm
  have hbpos : 0 < b := by
    simpa [b, fmt] using
      fmt.normalizedValue_false_pos (m := m + 1) (e := (26 : ℤ)) hmnext
  have hxrange : fmt.finiteNormalRange x := by
    have haRange := fmt.normalizedSystem_finiteNormalRange haSystem
    have hbRange := fmt.normalizedSystem_finiteNormalRange hbSystem
    have hxnonneg : 0 ≤ x := by
      dsimp [x]
      linarith
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have hmin_le_a : fmt.minNormalMagnitude ≤ a := by
        simpa [abs_of_pos hapos] using haRange.1
      exact le_trans hmin_le_a (le_of_lt hstrict.1)
    · have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
        simpa [abs_of_pos hbpos] using hbRange.2
      exact le_trans (le_of_lt hstrict.2) hb_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    have hxa : x - a = (1 : ℝ) := by
      dsimp [x]
      ring
    have hxb : x - b = -(3 : ℝ) := by
      change 1 + a - b = -(3 : ℝ)
      rw [ha_eq, hb_eq]
      ring
    rw [hxa, hxb, abs_neg]
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          (26 : ℤ))
        = fmt.finiteRoundToEven x := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
            x, a, fmt]
    _ = FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          (26 : ℤ) := by
      rw [hround]

/-- No-pivot inverse-update wrapper for the exponent-26 representable-inverse
slice: if `epsilon^{-1}` is such a binary32 value, then
`fl(1+epsilon^{-1}) = epsilon^{-1}`. -/
theorem noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp26
    {ε : ℝ} {m : ℕ}
    (hεinv :
      ε⁻¹ =
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          (26 : ℤ))
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1)) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 ε⁻¹ = ε⁻¹ := by
  rw [hεinv]
  exact noPivotIeeeSingle_add_one_normalized_exp26_rounds_to_self hm hmnext

/-- General no-pivot inverse-update binade criterion: if `a` is a positive
IEEE-single normalized value with a same-binade successor and the binade ulp is
larger than `2`, then `fl(1+a)=a`.  The exact sum is one unit to the right of
`a`, hence strictly closer to `a` than to the successor. -/
theorem noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_two_lt_ulp
    {m : ℕ} {e : ℤ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hexp : FloatingPointFormat.ieeeSingleFormat.exponentInRange e)
    (hulp :
      2 <
        FloatingPointFormat.ieeeSingleFormat.betaR ^
          (e - (FloatingPointFormat.ieeeSingleFormat.t : ℤ))) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let s : ℝ := fmt.betaR ^ (e - (fmt.t : ℤ))
  let a : ℝ := fmt.normalizedValue false m e
  let b : ℝ := fmt.normalizedValue false (m + 1) e
  let x : ℝ := 1 + a
  have hs : 2 < s := by
    simpa [s, fmt] using hulp
  have hs_pos : 0 < s := by linarith
  have haSystem : fmt.normalizedSystem a := by
    exact ⟨false, m, e, hm, hexp, rfl⟩
  have hbSystem : fmt.normalizedSystem b := by
    exact ⟨false, m + 1, e, hmnext, hexp, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, e, hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_eq : a = (m : ℝ) * s := by
    simp [a, s, fmt, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue]
  have hb_eq : b = ((m + 1 : ℕ) : ℝ) * s := by
    simp [b, s, fmt, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue]
  have hstrict : a < x ∧ x < b := by
    constructor
    · dsimp [x]
      linarith
    · change 1 + a < b
      rw [ha_eq, hb_eq]
      norm_num [Nat.cast_add]
      nlinarith [hs]
  have hapos : 0 < a := by
    simpa [a, fmt] using
      fmt.normalizedValue_false_pos (m := m) (e := e) hm
  have hbpos : 0 < b := by
    simpa [b, fmt] using
      fmt.normalizedValue_false_pos (m := m + 1) (e := e) hmnext
  have hxrange : fmt.finiteNormalRange x := by
    have haRange := fmt.normalizedSystem_finiteNormalRange haSystem
    have hbRange := fmt.normalizedSystem_finiteNormalRange hbSystem
    have hxnonneg : 0 ≤ x := by
      dsimp [x]
      linarith
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have hmin_le_a : fmt.minNormalMagnitude ≤ a := by
        simpa [abs_of_pos hapos] using haRange.1
      exact le_trans hmin_le_a (le_of_lt hstrict.1)
    · have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
        simpa [abs_of_pos hbpos] using hbRange.2
      exact le_trans (le_of_lt hstrict.2) hb_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    have hxa : x - a = (1 : ℝ) := by
      dsimp [x]
      ring
    have hxb : x - b = 1 - s := by
      change 1 + a - b = 1 - s
      rw [ha_eq, hb_eq]
      norm_num [Nat.cast_add]
      ring
    have hxb_neg : x - b < 0 := by
      rw [hxb]
      linarith
    rw [hxa, abs_one, abs_of_neg hxb_neg, hxb]
    linarith
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e)
        = fmt.finiteRoundToEven x := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
            x, a, fmt]
    _ = FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e := by
      rw [hround]

/-- Every positive IEEE-single normalized value in exponent binade at least
`26`, with a same-binade successor, satisfies the no-pivot inverse-update
rounding `fl(1+a)=a`. -/
theorem noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_exp_ge_26
    {m : ℕ} {e : ℤ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hexp : FloatingPointFormat.ieeeSingleFormat.exponentInRange e)
    (he : (26 : ℤ) ≤ e) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e := by
  apply noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_two_lt_ulp
      hm hmnext hexp
  have hexp_le : (2 : ℤ) ≤ e - 24 := by
    linarith
  have hp :
      (2 : ℝ) ^ (2 : ℤ) ≤ (2 : ℝ) ^ (e - 24) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp_le
  norm_num [FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.betaR] at hp ⊢
  linarith

/-- Source-facing wrapper for the exponent-`>=26` representable-inverse
threshold: if `epsilon^{-1}` is such a binary32 value, then
`fl(1+epsilon^{-1}) = epsilon^{-1}`. -/
theorem noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp_ge_26
    {ε : ℝ} {m : ℕ} {e : ℤ}
    (hεinv :
      ε⁻¹ =
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e)
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hexp : FloatingPointFormat.ieeeSingleFormat.exponentInRange e)
    (he : (26 : ℤ) ≤ e) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 ε⁻¹ = ε⁻¹ := by
  rw [hεinv]
  exact
    noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_exp_ge_26
      hm hmnext hexp he

/-- General no-pivot inverse-update midpoint criterion for IEEE single:
if the binade ulp is exactly `2`, then `1+a` is the exact midpoint between
`a` and its same-binade successor.  Round-to-nearest/even returns `a` when
the left mantissa is even. -/
theorem noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_ulp_eq_two_even
    {m : ℕ} {e : ℤ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hexp : FloatingPointFormat.ieeeSingleFormat.exponentInRange e)
    (hulp :
      FloatingPointFormat.ieeeSingleFormat.betaR ^
          (e - (FloatingPointFormat.ieeeSingleFormat.t : ℤ)) =
        (2 : ℝ))
    (heven : FloatingPointFormat.evenMantissa m) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let s : ℝ := fmt.betaR ^ (e - (fmt.t : ℤ))
  let a : ℝ := fmt.normalizedValue false m e
  let b : ℝ := fmt.normalizedValue false (m + 1) e
  let x : ℝ := 1 + a
  have hs : s = (2 : ℝ) := by
    simpa [s, fmt] using hulp
  have haSystem : fmt.normalizedSystem a := by
    exact ⟨false, m, e, hm, hexp, rfl⟩
  have hbSystem : fmt.normalizedSystem b := by
    exact ⟨false, m + 1, e, hmnext, hexp, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, e, hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_eq : a = (m : ℝ) * s := by
    simp [a, s, fmt, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue]
  have hb_eq : b = ((m + 1 : ℕ) : ℝ) * s := by
    simp [b, s, fmt, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue]
  have hstrict : a < x ∧ x < b := by
    constructor
    · dsimp [x]
      linarith
    · change 1 + a < b
      rw [ha_eq, hb_eq, hs]
      norm_num [Nat.cast_add]
      linarith
  have hapos : 0 < a := by
    simpa [a, fmt] using
      fmt.normalizedValue_false_pos (m := m) (e := e) hm
  have hbpos : 0 < b := by
    simpa [b, fmt] using
      fmt.normalizedValue_false_pos (m := m + 1) (e := e) hmnext
  have hxrange : fmt.finiteNormalRange x := by
    have haRange := fmt.normalizedSystem_finiteNormalRange haSystem
    have hbRange := fmt.normalizedSystem_finiteNormalRange hbSystem
    have hxnonneg : 0 ≤ x := by
      dsimp [x]
      linarith
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have hmin_le_a : fmt.minNormalMagnitude ≤ a := by
        simpa [abs_of_pos hapos] using haRange.1
      exact le_trans hmin_le_a (le_of_lt hstrict.1)
    · have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
        simpa [abs_of_pos hbpos] using hbRange.2
      exact le_trans (le_of_lt hstrict.2) hb_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft :
      a = fmt.normalizedValue false m e := rfl
  have htie : |x - a| = |x - b| := by
    have hxa : x - a = (1 : ℝ) := by
      dsimp [x]
      ring
    have hxb : x - b = -(1 : ℝ) := by
      change 1 + a - b = -(1 : ℝ)
      rw [ha_eq, hb_eq, hs]
      norm_num [Nat.cast_add]
      ring_nf
    rw [hxa, hxb, abs_neg, abs_one]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e)
        = fmt.finiteRoundToEven x := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
            x, a, fmt]
    _ = FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e := by
      rw [hround]

/-- General no-pivot inverse-update midpoint criterion for IEEE single:
if the binade ulp is exactly `2`, then `1+a` is the exact midpoint between
`a` and its same-binade successor.  Round-to-nearest/even returns the successor
when the left mantissa is odd. -/
theorem noPivotIeeeSingle_add_one_normalized_rounds_to_succ_of_ulp_eq_two_odd
    {m : ℕ} {e : ℤ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hexp : FloatingPointFormat.ieeeSingleFormat.exponentInRange e)
    (hulp :
      FloatingPointFormat.ieeeSingleFormat.betaR ^
          (e - (FloatingPointFormat.ieeeSingleFormat.t : ℤ)) =
        (2 : ℝ))
    (hodd : ¬ FloatingPointFormat.evenMantissa m) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + 1) e := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let s : ℝ := fmt.betaR ^ (e - (fmt.t : ℤ))
  let a : ℝ := fmt.normalizedValue false m e
  let b : ℝ := fmt.normalizedValue false (m + 1) e
  let x : ℝ := 1 + a
  have hs : s = (2 : ℝ) := by
    simpa [s, fmt] using hulp
  have haSystem : fmt.normalizedSystem a := by
    exact ⟨false, m, e, hm, hexp, rfl⟩
  have hbSystem : fmt.normalizedSystem b := by
    exact ⟨false, m + 1, e, hmnext, hexp, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, e, hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_eq : a = (m : ℝ) * s := by
    simp [a, s, fmt, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue]
  have hb_eq : b = ((m + 1 : ℕ) : ℝ) * s := by
    simp [b, s, fmt, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue]
  have hstrict : a < x ∧ x < b := by
    constructor
    · dsimp [x]
      linarith
    · change 1 + a < b
      rw [ha_eq, hb_eq, hs]
      norm_num [Nat.cast_add]
      linarith
  have hapos : 0 < a := by
    simpa [a, fmt] using
      fmt.normalizedValue_false_pos (m := m) (e := e) hm
  have hbpos : 0 < b := by
    simpa [b, fmt] using
      fmt.normalizedValue_false_pos (m := m + 1) (e := e) hmnext
  have hxrange : fmt.finiteNormalRange x := by
    have haRange := fmt.normalizedSystem_finiteNormalRange haSystem
    have hbRange := fmt.normalizedSystem_finiteNormalRange hbSystem
    have hxnonneg : 0 ≤ x := by
      dsimp [x]
      linarith
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have hmin_le_a : fmt.minNormalMagnitude ≤ a := by
        simpa [abs_of_pos hapos] using haRange.1
      exact le_trans hmin_le_a (le_of_lt hstrict.1)
    · have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
        simpa [abs_of_pos hbpos] using hbRange.2
      exact le_trans (le_of_lt hstrict.2) hb_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft :
      a = fmt.normalizedValue false m e := rfl
  have htie : |x - a| = |x - b| := by
    have hxa : x - a = (1 : ℝ) := by
      dsimp [x]
      ring
    have hxb : x - b = -(1 : ℝ) := by
      change 1 + a - b = -(1 : ℝ)
      rw [ha_eq, hb_eq, hs]
      norm_num [Nat.cast_add]
      ring_nf
    rw [hxa, hxb, abs_neg, abs_one]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e)
        = fmt.finiteRoundToEven x := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
            x, a, fmt]
    _ = FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + 1) e := by
      rw [hround]

/-- Exponent-25 same-binade midpoint case for no-pivot inverse updates:
an even left mantissa rounds back to the left endpoint. -/
theorem noPivotIeeeSingle_add_one_normalized_exp25_even_rounds_to_self
    {m : ℕ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (heven : FloatingPointFormat.evenMantissa m) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          (25 : ℤ)) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
        (25 : ℤ) := by
  apply
    noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_ulp_eq_two_even
      hm hmnext
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.betaR]
  · exact heven

/-- Exponent-25 same-binade midpoint case for no-pivot inverse updates:
an odd left mantissa rounds to the successor, so the source equality
`fl(1+a)=a` is false for this boundary parity. -/
theorem noPivotIeeeSingle_add_one_normalized_exp25_odd_rounds_to_succ
    {m : ℕ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hodd : ¬ FloatingPointFormat.evenMantissa m) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          (25 : ℤ)) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + 1)
        (25 : ℤ) := by
  apply
    noPivotIeeeSingle_add_one_normalized_rounds_to_succ_of_ulp_eq_two_odd
      hm hmnext
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.betaR]
  · exact hodd

/-- Source-facing wrapper for the exponent-25 even midpoint case: if
`epsilon^{-1}` is a same-binade IEEE-single normalized value in exponent `25`
with even mantissa, then `fl(1+epsilon^{-1}) = epsilon^{-1}`. -/
theorem noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp25_even
    {ε : ℝ} {m : ℕ}
    (hεinv :
      ε⁻¹ =
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          (25 : ℤ))
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (heven : FloatingPointFormat.evenMantissa m) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 ε⁻¹ = ε⁻¹ := by
  rw [hεinv]
  exact noPivotIeeeSingle_add_one_normalized_exp25_even_rounds_to_self
    hm hmnext heven

/-- Source-facing wrapper for the exponent-25 odd midpoint case: if
`epsilon^{-1}` is a same-binade IEEE-single normalized value in exponent `25`
with odd mantissa, then `fl(1+epsilon^{-1})` rounds to the successor instead
of back to `epsilon^{-1}`. -/
theorem noPivotIeeeSingle_add_one_inv_rounds_to_succ_of_inv_normalized_exp25_odd
    {ε : ℝ} {m : ℕ}
    (hεinv :
      ε⁻¹ =
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          (25 : ℤ))
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hodd : ¬ FloatingPointFormat.evenMantissa m) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 ε⁻¹ =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + 1)
        (25 : ℤ) := by
  rw [hεinv]
  exact noPivotIeeeSingle_add_one_normalized_exp25_odd_rounds_to_succ
    hm hmnext hodd

/-- The remaining exponent-25 carry endpoint: adding `1` to the largest
positive binary32 normalized value in exponent binade `25` is the exact
midpoint between that value and the smallest normalized value in binade `26`.
The left mantissa is odd, so nearest/even rounds to the exponent-26 endpoint. -/
theorem noPivotIeeeSingle_add_one_normalized_exp25_max_rounds_to_exp26_min :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
          FloatingPointFormat.ieeeSingleFormat.maxNormalMantissa (25 : ℤ)) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        FloatingPointFormat.ieeeSingleFormat.minNormalMantissa (26 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a : ℝ :=
    fmt.normalizedValue false fmt.maxNormalMantissa (25 : ℤ)
  let b : ℝ :=
    fmt.normalizedValue false fmt.minNormalMantissa (26 : ℤ)
  let x : ℝ := 1 + a
  have hmax : fmt.normalizedMantissa fmt.maxNormalMantissa :=
    fmt.maxNormalMantissa_normalized
  have hmin : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have hexp25 : fmt.exponentInRange (25 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hexp26 : fmt.exponentInRange (26 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have haSystem : fmt.normalizedSystem a := by
    exact ⟨false, fmt.maxNormalMantissa, (25 : ℤ), hmax, hexp25, rfl⟩
  have hbSystem : fmt.normalizedSystem b := by
    exact ⟨false, fmt.minNormalMantissa, (26 : ℤ), hmin, hexp26, rfl⟩
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, (25 : ℤ), Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, fmt,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hapos : 0 < a := by
    simpa [a, fmt] using
      fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := (25 : ℤ)) hmax
  have hbpos : 0 < b := by
    simpa [b, fmt] using
      fmt.normalizedValue_false_pos
        (m := fmt.minNormalMantissa) (e := (26 : ℤ)) hmin
  have hxrange : fmt.finiteNormalRange x := by
    have haRange := fmt.normalizedSystem_finiteNormalRange haSystem
    have hbRange := fmt.normalizedSystem_finiteNormalRange hbSystem
    have hxnonneg : 0 ≤ x := by
      dsimp [x]
      linarith
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have hmin_le_a : fmt.minNormalMagnitude ≤ a := by
        simpa [abs_of_pos hapos] using haRange.1
      exact le_trans hmin_le_a (le_of_lt hstrict.1)
    · have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
        simpa [abs_of_pos hbpos] using hbRange.2
      exact le_trans (le_of_lt hstrict.2) hb_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft :
      a = fmt.normalizedValue false fmt.maxNormalMantissa (25 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    have hxa : x - a = (1 : ℝ) := by
      dsimp [x]
      ring
    have hxb : x - b = -(1 : ℝ) := by
      norm_num [x, a, b, fmt,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    rw [hxa, hxb, abs_neg, abs_one]
  have hodd : ¬ FloatingPointFormat.evenMantissa fmt.maxNormalMantissa := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hmax hleft htie hodd
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
          FloatingPointFormat.ieeeSingleFormat.maxNormalMantissa (25 : ℤ))
        = fmt.finiteRoundToEven x := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
            x, a, fmt]
    _ = FloatingPointFormat.ieeeSingleFormat.normalizedValue false
          FloatingPointFormat.ieeeSingleFormat.minNormalMantissa
          (26 : ℤ) := by
      rw [hround]

/-- Source-facing wrapper for the exponent-25 carry endpoint: if
`epsilon^{-1}` is the largest positive binary32 normalized value in exponent
binade `25`, then `fl(1+epsilon^{-1})` rounds to the first value in binade
`26`, not back to `epsilon^{-1}`. -/
theorem noPivotIeeeSingle_add_one_inv_rounds_to_exp26_min_of_inv_normalized_exp25_max
    {ε : ℝ}
    (hεinv :
      ε⁻¹ =
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false
          FloatingPointFormat.ieeeSingleFormat.maxNormalMantissa (25 : ℤ)) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 ε⁻¹ =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        FloatingPointFormat.ieeeSingleFormat.minNormalMantissa (26 : ℤ) := by
  rw [hεinv]
  exact noPivotIeeeSingle_add_one_normalized_exp25_max_rounds_to_exp26_min

/-- Source-facing classifier for the representable-inverse left-rounding cases
of the no-pivot update.  A positive IEEE-single normalized inverse rounds back
to itself when either its exponent binade is at least `26`, or it is an
exponent-25 same-binade midpoint with even left mantissa. -/
theorem noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_left_rounding_cases
    {m : ℕ} {e : ℤ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hexp : FloatingPointFormat.ieeeSingleFormat.exponentInRange e)
    (hcase :
      ((26 : ℤ) ≤ e ∧
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1)) ∨
        (e = (25 : ℤ) ∧
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1) ∧
          FloatingPointFormat.evenMantissa m)) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e := by
  rcases hcase with hge | hmid
  · rcases hge with ⟨he, hmnext⟩
    exact
      noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_exp_ge_26
        hm hmnext hexp he
  · rcases hmid with ⟨heq, hmnext, heven⟩
    subst e
    exact
      noPivotIeeeSingle_add_one_normalized_exp25_even_rounds_to_self
        hm hmnext heven

/-- Source-facing `epsilon` wrapper for
`noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_left_rounding_cases`:
once `epsilon^{-1}` is explicitly represented as a positive IEEE-single
normalized value in one of the left-rounding cases, the no-pivot update
satisfies `fl(1+epsilon^{-1}) = epsilon^{-1}`. -/
theorem noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_left_rounding_cases
    {ε : ℝ} {m : ℕ} {e : ℤ}
    (hεinv :
      ε⁻¹ =
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m e)
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hexp : FloatingPointFormat.ieeeSingleFormat.exponentInRange e)
    (hcase :
      ((26 : ℤ) ≤ e ∧
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1)) ∨
        (e = (25 : ℤ) ∧
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1) ∧
          FloatingPointFormat.evenMantissa m)) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 ε⁻¹ = ε⁻¹ := by
  rw [hεinv]
  exact
    noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_left_rounding_cases
      hm hexp hcase

/-- Source-facing representability guard for the no-pivot inverse update:
if the rounded update is claimed to equal `epsilon^{-1}`, then
`epsilon^{-1}` must itself be a finite IEEE-single value, because the total
finite round-to-even operation always returns a finite-format value. -/
theorem noPivotIeeeSingle_add_one_inv_rounds_to_inv_requires_inv_finiteSystem
    {ε : ℝ}
    (hround :
      FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
          1 ε⁻¹ = ε⁻¹) :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem ε⁻¹ := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  rw [← hround]
  exact fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add 1 ε⁻¹

/-- Contrapositive form of the source-facing representability guard: an
arbitrary real `epsilon` whose inverse is not finite-format cannot satisfy the
source equality `fl(1+epsilon^{-1}) = epsilon^{-1}` in this finite selector. -/
theorem noPivotIeeeSingle_add_one_inv_not_rounds_to_inv_of_inv_not_finiteSystem
    {ε : ℝ}
    (hnot :
      ¬ FloatingPointFormat.ieeeSingleFormat.finiteSystem ε⁻¹) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 ε⁻¹ ≠ ε⁻¹ := by
  intro hround
  exact hnot
    (noPivotIeeeSingle_add_one_inv_rounds_to_inv_requires_inv_finiteSystem
      hround)

/-- In IEEE single precision with nearest/even rounding, the pivoted-path
midpoint `1 + 2^{-24}` rounds back to `1`. -/
theorem noPivotIeeeSingle_add_one_epsilon_rounds_to_one :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 noPivotIeeeSingleSmallEpsilon = 1 := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 8388608
  let a : ℝ := fmt.normalizedValue false m 1
  let b : ℝ := fmt.normalizedValue false (m + 1) 1
  let x : ℝ := 1 + noPivotIeeeSingleSmallEpsilon
  have hone : (1 : ℝ) = a := by
    norm_num [a, m, fmt,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
    rfl
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    constructor
    · rw [← hone]
      norm_num [x, noPivotIeeeSingleSmallEpsilon]
    · norm_num [x, noPivotIeeeSingleSmallEpsilon, a, b, m, fmt,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, noPivotIeeeSingleSmallEpsilon]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, noPivotIeeeSingleSmallEpsilon, fmt,
        FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        x = (16777217 : ℝ) / 16777216 := by
          norm_num [x, noPivotIeeeSingleSmallEpsilon]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false m (1 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    have hxa : x - a = (1 : ℝ) / (2 : ℝ)^24 := by
      have h :
          1 + ((2 : ℝ) ^ 24)⁻¹ -
              8388608 * ((2 : ℝ) ^ 23)⁻¹ =
            ((2 : ℝ) ^ 24)⁻¹ := by
        norm_num
      simpa [x, noPivotIeeeSingleSmallEpsilon, a, m, fmt,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg] using h
    have hxb : x - b = -((1 : ℝ) / (2 : ℝ)^24) := by
      norm_num [x, noPivotIeeeSingleSmallEpsilon, a, b, m, fmt,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    rw [hxa, hxb, abs_neg]
  have heven : FloatingPointFormat.evenMantissa m := by
    norm_num [FloatingPointFormat.evenMantissa, m]
  have hround :
      fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 noPivotIeeeSingleSmallEpsilon
        = fmt.finiteRoundToEven x := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
            x, fmt]
    _ = 1 := by
      rw [hround, ← hone]

/-- In IEEE single precision with nearest/even rounding, the signed pivoted
update `fl((-1) - 2^{-24})` rounds back to `-1`. -/
theorem noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1) noPivotIeeeSingleSmallEpsilon = -1 := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 8388608
  let a : ℝ := fmt.normalizedValue true (m + 1) 1
  let b : ℝ := fmt.normalizedValue true m 1
  let x : ℝ := (-1) - noPivotIeeeSingleSmallEpsilon
  have hneg_one : (-1 : ℝ) = b := by
    norm_num [b, m, fmt,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨true, m, (1 : ℤ), hm, hmnext, Or.inr ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, noPivotIeeeSingleSmallEpsilon, a, b, m, fmt,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonpos : x ≤ 0 := by
      norm_num [x, noPivotIeeeSingleSmallEpsilon]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonpos hxnonpos]
    constructor
    · norm_num [x, noPivotIeeeSingleSmallEpsilon, fmt,
        FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        -x = (16777217 : ℝ) / 16777216 := by
          norm_num [x, noPivotIeeeSingleSmallEpsilon]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue true (m + 1) (1 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    have hxa : x - a = (1 : ℝ) / (2 : ℝ)^24 := by
      norm_num [x, noPivotIeeeSingleSmallEpsilon, a, b, m, fmt,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hxb : x - b = -((1 : ℝ) / (2 : ℝ)^24) := by
      norm_num [x, noPivotIeeeSingleSmallEpsilon, b, m, fmt,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    rw [hxa, hxb, abs_neg]
  have hodd : ¬ FloatingPointFormat.evenMantissa (m + 1) := by
    norm_num [FloatingPointFormat.evenMantissa, m]
  have hround :
      fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hmnext hleft htie hodd
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1) noPivotIeeeSingleSmallEpsilon
        = fmt.finiteRoundToEven x := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
            x, fmt]
    _ = -1 := by
      rw [hround, ← hneg_one]

/-- For any IEEE-single finite `ε`, the pivoted-path multiplier division
`fl(ε/1)` is exact in nearest/even arithmetic. -/
theorem noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon_of_finiteSystem
    {ε : ℝ}
    (hεfinite : FloatingPointFormat.ieeeSingleFormat.finiteSystem ε) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        ε 1 = ε := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfin : fmt.finiteSystem (BasicOp.exact BasicOp.div ε 1) := by
    simpa [fmt, BasicOp.exact] using hεfinite
  simpa [fmt, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := ε) (y := 1) hfin)

/-- For any IEEE-single finite `ε`, the pivoted-path product `fl(ε*1)` is
exact in nearest/even arithmetic. -/
theorem noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon_of_finiteSystem
    {ε : ℝ}
    (hεfinite : FloatingPointFormat.ieeeSingleFormat.finiteSystem ε) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        ε 1 = ε := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfin : fmt.finiteSystem (BasicOp.exact BasicOp.mul ε 1) := by
    simpa [fmt, BasicOp.exact] using hεfinite
  simpa [fmt, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := ε) (y := 1) hfin)

/-- IEEE-single nearest/even threshold form of the pivoted-path update:
for every `0 <= ε <= 2^-24`, `fl(1+ε)=1`.  This is the non-enumerative
"sufficiently small ε" version of the concrete `ε=2^-24` theorem above. -/
theorem noPivotIeeeSingle_add_one_epsilon_rounds_to_one_of_nonneg_le_small
    {ε : ℝ}
    (hεnonneg : 0 ≤ ε)
    (hεle : ε ≤ noPivotIeeeSingleSmallEpsilon) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 ε = 1 := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 8388608
  let a : ℝ := fmt.normalizedValue false m 1
  let b : ℝ := fmt.normalizedValue false (m + 1) 1
  let x : ℝ := 1 + ε
  have hsmall :
      noPivotIeeeSingleSmallEpsilon = (1 : ℝ) / (2 : ℝ)^24 := by
    rfl
  have hspacing :
      b = 1 + (1 : ℝ) / (2 : ℝ)^23 := by
    norm_num [b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hone : (1 : ℝ) = a := by
    norm_num [a, m, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
    rfl
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      dsimp [x]
      linarith
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have hmin_le_one :
          fmt.minNormalMagnitude ≤ (1 : ℝ) := by
        norm_num [fmt, FloatingPointFormat.minNormalMagnitude,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.betaR, zpow_neg]
      dsimp [x]
      linarith
    · have hx_le :
          x ≤ 1 + noPivotIeeeSingleSmallEpsilon := by
        dsimp [x]
        linarith
      have hcap :
          1 + noPivotIeeeSingleSmallEpsilon ≤ fmt.maxFiniteMagnitude := by
        calc
          1 + noPivotIeeeSingleSmallEpsilon =
              (16777217 : ℝ) / 16777216 := by
            norm_num [noPivotIeeeSingleSmallEpsilon]
          _ ≤ 340282346638528859811704183484516925440 := by
            norm_num
          _ = fmt.maxFiniteMagnitude := by
            norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.betaR, zpow_neg]
            rfl
      exact le_trans hx_le hcap
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have ha_le_x : a ≤ x := by
    rw [← hone]
    dsimp [x]
    linarith
  have hx_le_b : x ≤ b := by
    rw [hspacing]
    have hsmall_le_spacing :
        noPivotIeeeSingleSmallEpsilon ≤ (1 : ℝ) / (2 : ℝ)^23 := by
      norm_num [noPivotIeeeSingleSmallEpsilon]
    dsimp [x]
    linarith
  have hnearest :
      fmt.finiteRoundToEven x =
        FloatingPointFormat.nearestAdjacentRoundToEven x a b m :=
    fmt.sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between
      hpolicy hadj ⟨false, (1 : ℤ), hm, rfl⟩ ⟨ha_le_x, hx_le_b⟩
  have hxa : |x - a| = ε := by
    have hxsub : x - a = ε := by
      rw [← hone]
      dsimp [x]
      ring
    rw [hxsub, abs_of_nonneg hεnonneg]
  have hxb : |x - b| = (1 : ℝ) / (2 : ℝ)^23 - ε := by
    have hxsub : x - b = ε - (1 : ℝ) / (2 : ℝ)^23 := by
      rw [hspacing]
      dsimp [x]
      ring
    have hnonpos : x - b ≤ 0 := by
      rw [hxsub]
      have hsmall_le_spacing :
          noPivotIeeeSingleSmallEpsilon ≤ (1 : ℝ) / (2 : ℝ)^23 := by
        norm_num [noPivotIeeeSingleSmallEpsilon]
      linarith
    rw [abs_of_nonpos hnonpos, hxsub]
    ring
  have hnearest_left :
      FloatingPointFormat.nearestAdjacentRoundToEven x a b m = a := by
    by_cases hlt : ε < noPivotIeeeSingleSmallEpsilon
    · apply FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_left_closer
      rw [hxa, hxb]
      have htwice :
          (1 : ℝ) / (2 : ℝ)^23 =
            2 * noPivotIeeeSingleSmallEpsilon := by
        norm_num [noPivotIeeeSingleSmallEpsilon]
      linarith
    · have heq : ε = noPivotIeeeSingleSmallEpsilon :=
        le_antisymm hεle (le_of_not_gt hlt)
      apply FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_tie_even
      · rw [hxa, hxb, heq]
        norm_num [noPivotIeeeSingleSmallEpsilon]
      · norm_num [FloatingPointFormat.evenMantissa, m]
  have hround : fmt.finiteRoundToEven x = a := by
    rw [hnearest, hnearest_left]
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        1 ε
        = fmt.finiteRoundToEven x := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact, x, fmt]
    _ = 1 := by
      rw [hround, ← hone]

/-- Signed companion of
`noPivotIeeeSingle_add_one_epsilon_rounds_to_one_of_nonneg_le_small`: for
every `0 <= ε <= 2^-24`, IEEE-single nearest/even gives
`fl((-1)-ε)=-1`. -/
theorem noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one_of_nonneg_le_small
    {ε : ℝ}
    (hεnonneg : 0 ≤ ε)
    (hεle : ε ≤ noPivotIeeeSingleSmallEpsilon) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1) ε = -1 := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hbeta : FloatingPointFormat.evenMantissa fmt.beta := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.evenMantissa]
  have ht : 1 < fmt.t := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat]
  have hadd :=
    noPivotIeeeSingle_add_one_epsilon_rounds_to_one_of_nonneg_le_small
      hεnonneg hεle
  have hadd_round : fmt.finiteRoundToEven (1 + ε) = 1 := by
    simpa [fmt, FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact]
      using hadd
  have harg : (-1 : ℝ) - ε = -(1 + ε) := by ring
  calc
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1) ε
        = fmt.finiteRoundToEven (-(1 + ε)) := by
          simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
            fmt, harg]
    _ = -fmt.finiteRoundToEven (1 + ε) := by
      exact fmt.finiteRoundToEven_neg hbeta ht (1 + ε)
    _ = -1 := by
      rw [hadd_round]

/-- The concrete `ε = 2^{-24}` no-pivot example is in the nonzero branch
needed by the factor-reproduction error theorem. -/
theorem noPivotIeeeSingleSmallEpsilon_ne_zero :
    noPivotIeeeSingleSmallEpsilon ≠ 0 := by
  norm_num [noPivotIeeeSingleSmallEpsilon]

/-- Specializing the no-pivot reproduction error to the concrete IEEE-single
`ε = 2^{-24}` instance. -/
theorem noPivotIeeeSingleSmallEpsilon_error_matrix :
    (fun i j : Fin 2 =>
        noPivotExampleA noPivotIeeeSingleSmallEpsilon i j -
          matMul 2 (noPivotRoundedL noPivotIeeeSingleSmallEpsilon)
            (noPivotRoundedU noPivotIeeeSingleSmallEpsilon) i j) =
      noPivotExampleFailureMatrix :=
  noPivotRoundedLU_error_matrix noPivotIeeeSingleSmallEpsilon_ne_zero

/-- The actual concrete IEEE-single pivoted factors produced by the primitive
rounded trace for `ε = 2^{-24}` satisfy the pivoted LU backward-error surface
with componentwise radius `ε`.  Unlike the exact pivoted factors, these rounded
factors use `U_22 = -1`, because `fl((-1)-ε) = -1`. -/
theorem noPivotIeeeSinglePartialPivotRoundedLUBackwardError :
    PermutedLUBackwardError 2
      (noPivotExampleA noPivotIeeeSingleSmallEpsilon)
      (noPivotPartialPivotL noPivotIeeeSingleSmallEpsilon)
      noPivotPartialPivotIeeeSingleRoundedU
      noPivotPartialPivotSwap
      noPivotIeeeSingleSmallEpsilon := by
  refine
    { perm := noPivotPartialPivotSwap_bijective
      L_diag := ?_
      L_upper_zero := ?_
      U_lower_zero := ?_
      backward_bound := ?_ }
  · intro i
    fin_cases i <;> simp [noPivotPartialPivotL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [noPivotPartialPivotL] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [noPivotPartialPivotIeeeSingleRoundedU] at hij ⊢
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [noPivotExampleA, noPivotPartialPivotL,
        noPivotPartialPivotIeeeSingleRoundedU, noPivotPartialPivotSwap,
        noPivotIeeeSingleSmallEpsilon]
    all_goals
      exact (by norm_num : |(0 : ℝ)| ≤ (1 : ℝ) / 16777216)

/-- Apply the real square-root map `k` times. -/
noncomputable def repeatedSqrt : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.sqrt (repeatedSqrt k x)

/-- Apply the squaring map `k` times. -/
noncomputable def repeatedSquare : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => repeatedSquare k (x ^ 2)

/-- Repeated square roots of a nonnegative real remain nonnegative. -/
theorem repeatedSqrt_nonneg (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ repeatedSqrt k x := by
  induction k with
  | zero =>
      simpa [repeatedSqrt] using hx
  | succ _ _ =>
      simp [repeatedSqrt, Real.sqrt_nonneg]

/-- In exact real arithmetic, applying `k` square roots and then `k` squarings
returns the original nonnegative value. -/
theorem repeatedSquare_repeatedSqrt_eq_self (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    repeatedSquare k (repeatedSqrt k x) = x := by
  induction k with
  | zero =>
      simp [repeatedSquare, repeatedSqrt]
  | succ k ih =>
      simp [repeatedSquare, repeatedSqrt]
      rw [Real.sq_sqrt (repeatedSqrt_nonneg k hx)]
      exact ih

/-- Higham §1.12.2's exact baseline for the displayed 60 square-root steps
followed by 60 squaring steps. -/
theorem repeatedSquare_repeatedSqrt_sixty_eq_self {x : ℝ} (hx : 0 ≤ x) :
    repeatedSquare 60 (repeatedSqrt 60 x) = x :=
  repeatedSquare_repeatedSqrt_eq_self 60 hx

/-! ## HP 48G surrogate from the text -/

/-- The piecewise function that Higham reports the HP 48G calculation computes
in place of the identity in §1.12.2.  The compact phase-law derivation is
formalized below; instantiating those laws from a concrete HP 48G decimal/range
model is a separate floating-point/range theorem. -/
noncomputable def hp48gSqrtSquareSurrogate (x : ℝ) : ℝ :=
  if x < 1 then 0 else 1

/-- The 12-significant-decimal value just below `1` used in Higham's HP 48G
discussion: `0.999999999999`. -/
noncomputable def hp48gTwelveDigitBelowOne : ℝ :=
  1 - (1 / (10 : ℝ) ^ 12)

/-- Abstract HP 48G laws sufficient to derive Higham's §1.12.2 step surrogate
from the 60-square-root phase and the following 60-squaring phase.  These laws
package the source's finite-range/rounding-to-one/underflow explanation without
unfolding 120 primitive operations. -/
structure Hp48gSqrtSquareSurrogateLaws
    (sqrtPhase squarePhase : ℝ → ℝ) : Prop where
  sqrt_ge_one_rounds_to_one :
    ∀ {x : ℝ}, 1 ≤ x → sqrtPhase x = 1
  sqrt_nonneg_lt_one_le_twelveDigitBelowOne :
    ∀ {x : ℝ}, 0 ≤ x → x < 1 →
      0 ≤ sqrtPhase x ∧ sqrtPhase x ≤ hp48gTwelveDigitBelowOne
  square_one_eq_one :
    squarePhase 1 = 1
  square_underflows_of_le_twelveDigitBelowOne :
    ∀ {y : ℝ}, 0 ≤ y → y ≤ hp48gTwelveDigitBelowOne →
      squarePhase y = 0

/-- The machine-level two-phase trace described in §1.12.2: first perform the
60 rounded square roots, then perform the 60 rounded squarings. -/
noncomputable def hp48gSqrtSquareTrace
    (sqrtPhase squarePhase : ℝ → ℝ) (x : ℝ) : ℝ :=
  squarePhase (sqrtPhase x)

/-- If the HP 48G root and square phases satisfy the source's
rounding-to-one and underflow laws, then the full two-phase trace computes
Higham's displayed step surrogate on every nonnegative input. -/
theorem hp48gSqrtSquareTrace_eq_surrogate_of_laws
    {sqrtPhase squarePhase : ℝ → ℝ}
    (hlaws : Hp48gSqrtSquareSurrogateLaws sqrtPhase squarePhase)
    {x : ℝ} (hx : 0 ≤ x) :
    hp48gSqrtSquareTrace sqrtPhase squarePhase x =
      hp48gSqrtSquareSurrogate x := by
  by_cases hlt : x < 1
  · rcases hlaws.sqrt_nonneg_lt_one_le_twelveDigitBelowOne hx hlt with
      ⟨hroot_nonneg, hroot_le⟩
    rw [hp48gSqrtSquareTrace,
      hlaws.square_underflows_of_le_twelveDigitBelowOne
        hroot_nonneg hroot_le,
      hp48gSqrtSquareSurrogate]
    simp [hlt]
  · have hge : 1 ≤ x := le_of_not_gt hlt
    rw [hp48gSqrtSquareTrace, hlaws.sqrt_ge_one_rounds_to_one hge,
      hlaws.square_one_eq_one, hp48gSqrtSquareSurrogate]
    simp [not_lt.mpr hge]

/-- On the source domain `0 <= x < 1`, the displayed HP 48G surrogate returns
zero. -/
theorem hp48gSqrtSquareSurrogate_of_nonneg_lt_one {x : ℝ} (_h0 : 0 ≤ x)
    (hx : x < 1) :
    hp48gSqrtSquareSurrogate x = 0 := by
  simp [hp48gSqrtSquareSurrogate, hx]

/-- For `x >= 1`, the displayed HP 48G surrogate returns one. -/
theorem hp48gSqrtSquareSurrogate_of_ge_one {x : ℝ} (hx : 1 ≤ x) :
    hp48gSqrtSquareSurrogate x = 1 := by
  simp [hp48gSqrtSquareSurrogate, not_lt.mpr hx]

/-- The reported HP 48G surrogate sends `x = 100` to `1`. -/
theorem hp48gSqrtSquareSurrogate_100_eq_one :
    hp48gSqrtSquareSurrogate 100 = 1 := by
  norm_num [hp48gSqrtSquareSurrogate]

/-- The absolute error of the displayed HP 48G surrogate at `x = 100` is `99`. -/
theorem hp48gSqrtSquareSurrogate_absError_100 :
    absError (hp48gSqrtSquareSurrogate 100) 100 = 99 := by
  norm_num [absError, hp48gSqrtSquareSurrogate]

/-- The relative error of the displayed HP 48G surrogate at `x = 100` is
`99/100`. -/
theorem hp48gSqrtSquareSurrogate_relError_100 :
    relError (hp48gSqrtSquareSurrogate 100) 100 = 99 / 100 := by
  norm_num [relError, hp48gSqrtSquareSurrogate]

/-- On the source interval `x >= 1`, the displayed HP 48G surrogate has
absolute error `x - 1`. -/
theorem hp48gSqrtSquareSurrogate_absError_of_ge_one {x : ℝ} (hx : 1 ≤ x) :
    absError (hp48gSqrtSquareSurrogate x) x = x - 1 := by
  have hsur := hp48gSqrtSquareSurrogate_of_ge_one hx
  have hnonpos : 1 - x ≤ 0 := by linarith
  rw [hsur]
  simp [absError, abs_of_nonpos hnonpos]

/-- On the source interval `x >= 1`, the displayed HP 48G surrogate has
relative error `(x - 1) / x`. -/
theorem hp48gSqrtSquareSurrogate_relError_of_ge_one {x : ℝ} (hx : 1 ≤ x) :
    relError (hp48gSqrtSquareSurrogate x) x = (x - 1) / x := by
  have hsur := hp48gSqrtSquareSurrogate_of_ge_one hx
  have hnonpos : 1 - x ≤ 0 := by linarith
  have hnonneg : 0 ≤ x := by linarith
  rw [hsur]
  simp [relError, abs_of_nonpos hnonpos, abs_of_nonneg hnonneg]

/-- On the source interval `0 <= x < 1`, the displayed HP 48G surrogate has
absolute error `x`. -/
theorem hp48gSqrtSquareSurrogate_absError_of_nonneg_lt_one {x : ℝ}
    (h0 : 0 ≤ x) (hx : x < 1) :
    absError (hp48gSqrtSquareSurrogate x) x = x := by
  have hsur := hp48gSqrtSquareSurrogate_of_nonneg_lt_one h0 hx
  rw [hsur]
  simpa [absError] using abs_of_nonneg h0

/-- On the source interval `0 < x < 1`, the displayed HP 48G surrogate has
relative error `1`. -/
theorem hp48gSqrtSquareSurrogate_relError_of_pos_lt_one {x : ℝ}
    (hpos : 0 < x) (hx : x < 1) :
    relError (hp48gSqrtSquareSurrogate x) x = 1 := by
  have h0 : 0 ≤ x := le_of_lt hpos
  have hsur := hp48gSqrtSquareSurrogate_of_nonneg_lt_one h0 hx
  have hnonneg : 0 ≤ x := le_of_lt hpos
  rw [hsur]
  calc
    relError 0 x = x / x := by
      simp [relError, abs_of_nonneg hnonneg]
    _ = 1 := div_self (ne_of_gt hpos)

/-! ## Exact infinite-sum term size -/

/-- The inverse-square term `1/k^2` from Higham §1.12.3's summation example. -/
noncomputable def inverseSquareTerm (k : ℕ) : ℝ :=
  1 / (k : ℝ) ^ 2

/-- The term identified in Higham §1.12.3 is exactly
`4096^{-2} = 2^{-24}`. -/
theorem inverseSquareTerm_4096_eq_two_pow_neg_24 :
    inverseSquareTerm 4096 = 1 / (2 : ℝ) ^ 24 := by
  norm_num [inverseSquareTerm]

/-- Every positive inverse-square term is positive. -/
theorem inverseSquareTerm_pos_of_pos {k : ℕ} (hk : 0 < k) :
    0 < inverseSquareTerm k := by
  unfold inverseSquareTerm
  have hk_real : (0 : ℝ) < k := by
    exact_mod_cast hk
  exact div_pos zero_lt_one (pow_pos hk_real 2)

/-- The `10^9` inverse-square term is the smallest positive term encountered
in Higham §1.12.3's `10^9`-term experiment. -/
theorem inverseSquareTerm_ten_pow_nine_le_of_pos_le
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ 10 ^ 9) :
    inverseSquareTerm (10 ^ 9) ≤ inverseSquareTerm k := by
  unfold inverseSquareTerm
  have hk_real_pos : (0 : ℝ) < k := by
    exact_mod_cast hkpos
  have hk_real_le : (k : ℝ) ≤ ((10 ^ 9 : ℕ) : ℝ) := by
    exact_mod_cast hk
  have hsquare_le : (k : ℝ) ^ 2 ≤ (((10 ^ 9 : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  exact one_div_le_one_div_of_le (pow_pos hk_real_pos 2) hsquare_le

/-- Even the smallest positive term in the `10^9` experiment is normal-sized
for binary32.  This prevents the high-index prefix additions from entering the
underflow range. -/
theorem inverseSquareTerm_ten_pow_nine_ge_ieeeSingle_minNormal :
    FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤
      inverseSquareTerm (10 ^ 9) := by
  norm_num [inverseSquareTerm, FloatingPointFormat.minNormalMagnitude,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR, zpow_neg]

/-- Every positive inverse-square term up to index `10^9` is normal-sized for
binary32. -/
theorem inverseSquareTerm_ge_ieeeSingle_minNormal_of_pos_le_ten_pow_nine
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ 10 ^ 9) :
    FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤
      inverseSquareTerm k :=
  le_trans inverseSquareTerm_ten_pow_nine_ge_ieeeSingle_minNormal
    (inverseSquareTerm_ten_pow_nine_le_of_pos_le hkpos hk)

/-- After `k = 4096`, the inverse-square terms are no larger than the
`4096^{-2}` term that Higham identifies as being too small to affect the
single-precision running sum. -/
theorem inverseSquareTerm_le_4096_of_ge {k : ℕ} (hk : 4096 ≤ k) :
    inverseSquareTerm k ≤ inverseSquareTerm 4096 := by
  unfold inverseSquareTerm
  have h4096_pos : (0 : ℝ) < 4096 := by
    norm_num
  have hk_ge : (4096 : ℝ) ≤ k := by
    exact_mod_cast hk
  have hsquare_ge : (4096 : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
    nlinarith
  exact div_le_div_of_nonneg_left
    (by norm_num : (0 : ℝ) ≤ 1) (pow_pos h4096_pos 2) hsquare_ge

/-- Therefore every inverse-square term from `k = 4096` onward is at most
`2^{-24}`.  The floating-point claim that such terms drop off the end of a
single-precision accumulator remains a separate machine-rounding theorem. -/
theorem inverseSquareTerm_le_two_pow_neg_24_of_ge {k : ℕ} (hk : 4096 ≤ k) :
    inverseSquareTerm k ≤ 1 / (2 : ℝ) ^ 24 := by
  rw [← inverseSquareTerm_4096_eq_two_pow_neg_24]
  exact inverseSquareTerm_le_4096_of_ge hk

/-- The first binary block above Higham's `4096` cutoff has term size at most
`8192^{-2} = 2^{-26}`.  This is a binade-scale foothold for the remaining
reverse high-prefix interval proof. -/
theorem inverseSquareTerm_le_two_pow_neg_26_of_ge_8192
    {k : ℕ} (hk : 8192 ≤ k) :
    inverseSquareTerm k ≤ 1 / (2 : ℝ) ^ 26 := by
  unfold inverseSquareTerm
  have h8192_pos : (0 : ℝ) < 8192 := by norm_num
  have hk_ge : (8192 : ℝ) ≤ k := by exact_mod_cast hk
  have hsquare_ge : (8192 : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
    nlinarith
  have hden_pos : 0 < (8192 : ℝ) ^ 2 := pow_pos h8192_pos 2
  have hstep :
      1 / ((k : ℝ) ^ 2) ≤ 1 / ((8192 : ℝ) ^ 2) := by
    exact one_div_le_one_div_of_le hden_pos hsquare_ge
  calc
    1 / ((k : ℝ) ^ 2) ≤ 1 / ((8192 : ℝ) ^ 2) := hstep
    _ = 1 / (2 : ℝ) ^ 26 := by norm_num

/-- For the whole strict-pre-plateau range that matters in Higham §1.12.3,
`1/k^2` lies between one half-ulp and one ulp at binary32 exponent `1`.
This is the range fact used to avoid proving the predecessor trace one
numeral at a time. -/
theorem inverseSquareTerm_between_half_ulp_and_one_ulp_of_ge_2897_lt_4096
    {k : ℕ} (hklo : 2897 ≤ k) (hkhi : k < 4096) :
    1 / (2 : ℝ) ^ 24 < inverseSquareTerm k ∧
      inverseSquareTerm k < 1 / (2 : ℝ) ^ 23 := by
  have hk_nonneg : (0 : ℝ) ≤ k := by exact_mod_cast Nat.zero_le k
  have hk_pos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2897) hklo)
  have hklo_real : (2897 : ℝ) ≤ k := by exact_mod_cast hklo
  have hkhi_real : (k : ℝ) < 4096 := by exact_mod_cast hkhi
  have hk_sq_pos : 0 < (k : ℝ) ^ 2 := pow_pos hk_pos 2
  have hk_sq_lt_two_pow_24 : (k : ℝ) ^ 2 < (2 : ℝ) ^ 24 := by
    have hk_sq_lt_4096_sq : (k : ℝ) ^ 2 < (4096 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hkhi_real hk_nonneg (by norm_num : 2 ≠ 0)
    norm_num at hk_sq_lt_4096_sq ⊢
    exact hk_sq_lt_4096_sq
  have htwo_pow_23_lt_hk_sq : (2 : ℝ) ^ 23 < (k : ℝ) ^ 2 := by
    have h2897_sq_le_hk_sq : (2897 : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2897) hklo_real 2
    norm_num at h2897_sq_le_hk_sq ⊢
    linarith
  constructor
  · simpa [inverseSquareTerm] using
      one_div_lt_one_div_of_lt hk_sq_pos hk_sq_lt_two_pow_24
  · have htwo_pow_23_pos : (0 : ℝ) < (2 : ℝ) ^ 23 := by norm_num
    simpa [inverseSquareTerm] using
      one_div_lt_one_div_of_lt htwo_pow_23_pos htwo_pow_23_lt_hk_sq

/-! ## Single-precision local stagnation mechanism -/

/-- The IEEE-single value six ulps below the plateau printed in Higham
§1.12.3, with mantissa `13796950` and exponent `1`. -/
noncomputable def inverseSquareSingleSixBeforePlateauAccumulator : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13796950 1

/-- The binary32 accumulator value from which the proved range theorem carries
the forward summation through `k = 2897, ..., 4090` to the six-before-plateau
accumulator.  In the explicit repository model, the early-prefix question is
whether the modeled accumulator reaches this value after the `k = 2896` step;
the historical Fortran run itself is an empirical ledger row. -/
noncomputable def inverseSquareSinglePrePlateauWindowStartAccumulator : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13795756 1

/-- The IEEE-single value five ulps below the plateau printed in Higham
§1.12.3, with mantissa `13796951` and exponent `1`. -/
noncomputable def inverseSquareSingleFiveBeforePlateauAccumulator : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13796951 1

/-- The IEEE-single value four ulps below the plateau printed in Higham
§1.12.3, with mantissa `13796952` and exponent `1`. -/
noncomputable def inverseSquareSingleFourBeforePlateauAccumulator : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13796952 1

/-- The IEEE-single value three ulps below the plateau printed in Higham
§1.12.3, with mantissa `13796953` and exponent `1`. -/
noncomputable def inverseSquareSingleThreeBeforePlateauAccumulator : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13796953 1

/-- The IEEE-single value two ulps below the plateau printed in Higham §1.12.3,
with mantissa `13796954` and exponent `1`. -/
noncomputable def inverseSquareSingleTwoBeforePlateauAccumulator : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13796954 1

/-- The IEEE-single value immediately below the plateau printed in Higham
§1.12.3, with mantissa `13796955` and exponent `1`. -/
noncomputable def inverseSquareSinglePrePlateauAccumulator : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13796955 1

/-- The six-before-plateau accumulator is strictly below the
five-before-plateau accumulator. -/
theorem inverseSquareSingleSixBeforePlateauAccumulator_lt_fiveBeforePlateau :
    inverseSquareSingleSixBeforePlateauAccumulator <
      inverseSquareSingleFiveBeforePlateauAccumulator := by
  norm_num [inverseSquareSingleSixBeforePlateauAccumulator,
    inverseSquareSingleFiveBeforePlateauAccumulator,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- The five-before-plateau accumulator is strictly below the
four-before-plateau accumulator. -/
theorem inverseSquareSingleFiveBeforePlateauAccumulator_lt_fourBeforePlateau :
    inverseSquareSingleFiveBeforePlateauAccumulator <
      inverseSquareSingleFourBeforePlateauAccumulator := by
  norm_num [inverseSquareSingleFiveBeforePlateauAccumulator,
    inverseSquareSingleFourBeforePlateauAccumulator,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- The four-before-plateau accumulator is strictly below the
three-before-plateau accumulator. -/
theorem inverseSquareSingleFourBeforePlateauAccumulator_lt_threeBeforePlateau :
    inverseSquareSingleFourBeforePlateauAccumulator <
      inverseSquareSingleThreeBeforePlateauAccumulator := by
  norm_num [inverseSquareSingleFourBeforePlateauAccumulator,
    inverseSquareSingleThreeBeforePlateauAccumulator,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- The three-before-plateau accumulator is strictly below the two-before-plateau
accumulator. -/
theorem inverseSquareSingleThreeBeforePlateauAccumulator_lt_twoBeforePlateau :
    inverseSquareSingleThreeBeforePlateauAccumulator <
      inverseSquareSingleTwoBeforePlateauAccumulator := by
  norm_num [inverseSquareSingleThreeBeforePlateauAccumulator,
    inverseSquareSingleTwoBeforePlateauAccumulator,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- The two-before-plateau accumulator is strictly below the pre-plateau
accumulator. -/
theorem inverseSquareSingleTwoBeforePlateauAccumulator_lt_prePlateau :
    inverseSquareSingleTwoBeforePlateauAccumulator <
      inverseSquareSinglePrePlateauAccumulator := by
  norm_num [inverseSquareSingleTwoBeforePlateauAccumulator,
    inverseSquareSinglePrePlateauAccumulator,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- A concrete IEEE-single value near the plateau printed in Higham §1.12.3:
it is the normalized finite number with even mantissa `13796956` and exponent
`1`, i.e. the binary32 value printed by common tools as approximately
`1.64472532`. -/
noncomputable def inverseSquareSinglePlateauAccumulator : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13796956 1

/-- The pre-plateau accumulator is strictly below the displayed plateau value. -/
theorem inverseSquareSinglePrePlateauAccumulator_lt_plateau :
    inverseSquareSinglePrePlateauAccumulator <
      inverseSquareSinglePlateauAccumulator := by
  norm_num [inverseSquareSinglePrePlateauAccumulator,
    inverseSquareSinglePlateauAccumulator,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- The §1.12.3 local stagnation mechanism: at this concrete single-precision
accumulator, adding the displayed term `4096^{-2} = 2^{-24}` is an exact
midpoint tie between two adjacent binary32 values, and nearest/even returns the
same accumulator because its mantissa is even.  This closes the book's local
"drops off the end" explanation; deriving a whole explicit repository-model
loop is optional model strengthening, while the historical run remains
empirical-source-output. -/
theorem inverseSquareSinglePlateau_add_4096_term_rounds_to_self :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        inverseSquareSinglePlateauAccumulator (inverseSquareTerm 4096) =
      inverseSquareSinglePlateauAccumulator := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 13796956
  let a : ℝ := fmt.normalizedValue false m 1
  let b : ℝ := fmt.normalizedValue false (m + 1) 1
  let x : ℝ := a + inverseSquareTerm 4096
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, m, fmt, inverseSquareTerm,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, a, m, fmt, inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, a, m, fmt, inverseSquareTerm,
        FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        x = (27593913 : ℝ) / 16777216 := by
          norm_num [x, a, m, fmt, inverseSquareTerm,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue,
            FloatingPointFormat.signValue,
            FloatingPointFormat.betaR,
            zpow_neg]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft :
      a = fmt.normalizedValue false m (1 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    norm_num [x, a, b, m, fmt, inverseSquareTerm,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have heven : FloatingPointFormat.evenMantissa m := by
    norm_num [FloatingPointFormat.evenMantissa, m]
  have hround :
      fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
    inverseSquareSinglePlateauAccumulator, inverseSquareTerm, x, a, fmt, m]
    using hround

/-- The boundary step into Higham §1.12.3's displayed single-precision plateau:
adding the `4096^{-2} = 2^{-24}` term to the immediately preceding binary32
accumulator is an exact midpoint tie between mantissas `13796955` and
`13796956`. Since the left mantissa is odd, nearest/even returns the right
endpoint, namely the plateau accumulator printed approximately as
`1.64472532`. This is the local `k = 4096` entry step; the proof that the full
forward loop reaches the pre-plateau accumulator at `k = 4095` remains a
separate operation-trace obligation. -/
theorem inverseSquareSinglePrePlateau_add_4096_term_rounds_to_plateau :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        inverseSquareSinglePrePlateauAccumulator (inverseSquareTerm 4096) =
      inverseSquareSinglePlateauAccumulator := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 13796955
  let a : ℝ := fmt.normalizedValue false m 1
  let b : ℝ := fmt.normalizedValue false (m + 1) 1
  let x : ℝ := a + inverseSquareTerm 4096
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, m, fmt, inverseSquareTerm,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, a, m, fmt, inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, a, m, fmt, inverseSquareTerm,
        FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        x = (27593911 : ℝ) / 16777216 := by
          norm_num [x, a, m, fmt, inverseSquareTerm,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue,
            FloatingPointFormat.signValue,
            FloatingPointFormat.betaR,
            zpow_neg]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft :
      a = fmt.normalizedValue false m (1 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    norm_num [x, a, b, m, fmt, inverseSquareTerm,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hodd : ¬ FloatingPointFormat.evenMantissa m := by
    norm_num [FloatingPointFormat.evenMantissa, m]
  have hround :
      fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd
  simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
    inverseSquareSinglePrePlateauAccumulator,
    inverseSquareSinglePlateauAccumulator, inverseSquareTerm, x, a, b, fmt, m]
    using hround

/-- Reusable one-ulp successor lemma for the local Higham §1.12.3 binary32
inverse-square chain.  If the positive term is between one half-ulp and one ulp
at exponent `1`, adding it to a positive IEEE-single value with adjacent
mantissa `m+1` rounds to that adjacent value under nearest/even.  The explicit
finite-range hypotheses keep this lemma local to the machine-range facts needed
by the concrete Chapter 1 wrappers. -/
theorem inverseSquareSingle_add_term_rounds_to_next_of_half_ulp_lt
    {m k : ℕ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hmin_le_left :
      FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ))
    (hnext_le_max :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + 1) (1 : ℤ) ≤
        FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude)
    (hterm_pos : 0 < inverseSquareTerm k)
    (hterm_lt_spacing : inverseSquareTerm k < 1 / (2 : ℝ) ^ 23)
    (hhalf_lt_term : 1 / (2 : ℝ) ^ 24 < inverseSquareTerm k) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ))
        (inverseSquareTerm k) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + 1) (1 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false m 1
  let b : ℝ := fmt.normalizedValue false (m + 1) 1
  let term : ℝ := inverseSquareTerm k
  let x : ℝ := a + term
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hb_sub : b - a = 1 / (2 : ℝ) ^ 23 := by
    norm_num [a, b, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
    ring
  have hstrict : a < x ∧ x < b := by
    constructor
    · simp [x, term]
      exact hterm_pos
    · have : a + term < b := by
        nlinarith [hb_sub, hterm_lt_spacing]
      simpa [x] using this
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      have ha_pos : 0 < a := by
        exact fmt.normalizedValue_false_pos (m := m) (e := (1 : ℤ)) hm
      positivity
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have ha_le_x : a ≤ x := le_of_lt hstrict.1
      exact le_trans hmin_le_left ha_le_x
    · exact le_trans (le_of_lt hstrict.2) hnext_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    have hxa : x - a = term := by
      simp [x]
    have hxb : x - b = term - (1 / (2 : ℝ) ^ 23) := by
      calc
        x - b = a + term - b := by simp [x]
        _ = term - (b - a) := by ring
        _ = term - (1 / (2 : ℝ) ^ 23) := by rw [hb_sub]
    have hspacing_twice : 1 / (2 : ℝ) ^ 23 = 2 * (1 / (2 : ℝ) ^ 24) := by
      norm_num
    have hright : (1 / (2 : ℝ) ^ 23) - term < term := by
      nlinarith
    have hneg : term - (1 / (2 : ℝ) ^ 23) < 0 := by
      nlinarith [hterm_lt_spacing]
    calc
      |x - b| = (1 / (2 : ℝ) ^ 23) - term := by
        rw [hxb, abs_of_neg hneg]
        ring
      _ < term := hright
      _ = |x - a| := by rw [hxa, abs_of_pos hterm_pos]
  have hround :
      fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
    inverseSquareTerm, term, x, a, b, fmt]
    using hround

/-- Range-index version of
`inverseSquareSingle_add_term_rounds_to_next_of_half_ulp_lt`: throughout the
whole `2897 <= k < 4096` pre-plateau range, the inverse-square term is
automatically between one half-ulp and one ulp, so a normalized adjacent
binary32 pair at exponent `1` rounds to its successor. -/
theorem inverseSquareSingle_add_term_rounds_to_next_of_index_range
    {m k : ℕ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hmin_le_left :
      FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ))
    (hnext_le_max :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + 1) (1 : ℤ) ≤
        FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude)
    (hklo : 2897 ≤ k) (hkhi : k < 4096) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ))
        (inverseSquareTerm k) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + 1) (1 : ℤ) := by
  have hbounds :=
    inverseSquareTerm_between_half_ulp_and_one_ulp_of_ge_2897_lt_4096 hklo hkhi
  exact
    inverseSquareSingle_add_term_rounds_to_next_of_half_ulp_lt
      hm hmnext hmin_le_left hnext_le_max
      (inverseSquareTerm_pos_of_pos
        (lt_of_lt_of_le (by norm_num : 0 < 2897) hklo))
      hbounds.2 hbounds.1

/-- One forward rounded-addition step in Higham §1.12.3's single-precision
left-to-right inverse-square summation.  The index `k` is the mathematical
term index in `1/k^2`. -/
noncomputable def inverseSquareSingleForwardStep (s : ℝ) (k : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
    s (inverseSquareTerm k)

/-- Generic positive binary32 adjacent-bracket certificate for a rounded
inverse-square addition.  If the exact sum is strictly between a target state
and its successor and is closer to the target, the IEEE-single rounded add
returns the target state. -/
theorem inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer
    {s y succ : ℝ} {k : ℕ}
    (hySystem :
      FloatingPointFormat.ieeeSingleFormat.normalizedSystem y)
    (hsuccSystem :
      FloatingPointFormat.ieeeSingleFormat.normalizedSystem succ)
    (hadj :
      FloatingPointFormat.ieeeSingleFormat.realOrderAdjacentNormalized y succ)
    (hy_pos : 0 < y) (hsucc_pos : 0 < succ)
    (hstrict : y < s + inverseSquareTerm k ∧
      s + inverseSquareTerm k < succ)
    (hleftCloser :
      |s + inverseSquareTerm k - y| <
        |s + inverseSquareTerm k - succ|) :
    inverseSquareSingleForwardStep s k = y := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let x : ℝ := s + inverseSquareTerm k
  have hxpos : 0 < x := lt_trans hy_pos (by simpa [x] using hstrict.1)
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg (le_of_lt hxpos)]
    constructor
    · have hy_min : fmt.minNormalMagnitude ≤ y := by
        simpa [FloatingPointFormat.minNormalMagnitude, abs_of_pos hy_pos] using
          fmt.normalizedSystem_abs_lower_bound hySystem
      exact le_trans hy_min (le_of_lt (by simpa [x] using hstrict.1))
    · have hsucc_max : succ ≤ fmt.maxFiniteMagnitude := by
        simpa [FloatingPointFormat.maxFiniteMagnitude, abs_of_pos hsucc_pos] using
          fmt.normalizedSystem_abs_le_maxFinite_bound hsuccSystem
      exact le_trans (le_of_lt (by simpa [x] using hstrict.2)) hsucc_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hround : fmt.finiteRoundToEven x = y :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj (by simpa [x] using hstrict)
      (by simpa [x] using hleftCloser)
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, x, fmt] using hround

/-- Right-endpoint version of
`inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer`.
This is the companion certificate used when the exact sum lies between the
predecessor and the target state and is closer to the target. -/
theorem inverseSquareSingleForwardStep_eq_right_of_adjacent_strict_between_right_closer
    {s pred y : ℝ} {k : ℕ}
    (hpredSystem :
      FloatingPointFormat.ieeeSingleFormat.normalizedSystem pred)
    (hySystem :
      FloatingPointFormat.ieeeSingleFormat.normalizedSystem y)
    (hadj :
      FloatingPointFormat.ieeeSingleFormat.realOrderAdjacentNormalized pred y)
    (hpred_pos : 0 < pred) (hy_pos : 0 < y)
    (hstrict : pred < s + inverseSquareTerm k ∧
      s + inverseSquareTerm k < y)
    (hrightCloser :
      |s + inverseSquareTerm k - y| <
        |s + inverseSquareTerm k - pred|) :
    inverseSquareSingleForwardStep s k = y := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let x : ℝ := s + inverseSquareTerm k
  have hxpos : 0 < x := lt_trans hpred_pos (by simpa [x] using hstrict.1)
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg (le_of_lt hxpos)]
    constructor
    · have hpred_min : fmt.minNormalMagnitude ≤ pred := by
        simpa [FloatingPointFormat.minNormalMagnitude, abs_of_pos hpred_pos] using
          fmt.normalizedSystem_abs_lower_bound hpredSystem
      exact le_trans hpred_min (le_of_lt (by simpa [x] using hstrict.1))
    · have hy_max : y ≤ fmt.maxFiniteMagnitude := by
        simpa [FloatingPointFormat.maxFiniteMagnitude, abs_of_pos hy_pos] using
          fmt.normalizedSystem_abs_le_maxFinite_bound hySystem
      exact le_trans (le_of_lt (by simpa [x] using hstrict.2)) hy_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hround : fmt.finiteRoundToEven x = y :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj (by simpa [x] using hstrict)
      (by simpa [x] using hrightCloser)
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, x, fmt] using hround

/-- Scale identity for the binary32 exponent band whose half-ulp arithmetic is
encoded by the natural power `2^q`. -/
theorem inverseSquareSingle_scaleAtExponent_mul_two_pow (q : ℕ) :
    (2 : ℝ) ^ (((25 : ℤ) - (q : ℤ)) - (24 : ℤ)) *
      (2 : ℝ) ^ q = 2 := by
  rw [← zpow_natCast]
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hexp : ((25 : ℤ) - (q : ℤ)) - (24 : ℤ) + (q : ℤ) = 1 := by
    omega
  rw [hexp]
  norm_num

/-- Division form of `inverseSquareSingle_scaleAtExponent_mul_two_pow`. -/
theorem inverseSquareSingle_scaleAtExponent_eq_two_div_two_pow (q : ℕ) :
    (2 : ℝ) ^ (((25 : ℤ) - (q : ℤ)) - (24 : ℤ)) =
      2 / (2 : ℝ) ^ q := by
  have hmul := inverseSquareSingle_scaleAtExponent_mul_two_pow q
  have hp : (2 : ℝ) ^ q ≠ 0 := by positivity
  exact (eq_div_iff hp).2 hmul

/-- Generic left bracket arithmetic for nearest-mantissa rounding in any
positive IEEE-single exponent band represented by `e = 25 - q`. -/
theorem inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
    {m d k q : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hleft : (2 * d - 1) * k ^ 2 < 2 ^ q) :
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d - 1)
        ((25 : ℤ) - (q : ℤ)) <
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          ((25 : ℤ) - (q : ℤ)) +
        inverseSquareTerm k := by
  let scale : ℝ := (2 : ℝ) ^ (((25 : ℤ) - (q : ℤ)) - (24 : ℤ))
  have hscale_eq : scale = 2 / (2 : ℝ) ^ q := by
    simpa [scale] using inverseSquareSingle_scaleAtExponent_eq_two_div_two_pow q
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hPpos : 0 < (2 : ℝ) ^ q := by positivity
  have hkRpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hcertR : (((2 * d - 1) * k ^ 2 : ℕ) : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast hleft
  have hdcast : ((2 * d - 1 : ℕ) : ℝ) = 2 * (d : ℝ) - 1 := by
    have hsub : 1 ≤ 2 * d := by omega
    rw [Nat.cast_sub hsub]
    norm_num
  have hmdcast : ((m + d - 1 : ℕ) : ℝ) = (m : ℝ) + (d : ℝ) - 1 := by
    have hsub : 1 ≤ m + d := by omega
    rw [Nat.cast_sub hsub]
    norm_num
  have hcertR2 : (2 * (d : ℝ) - 1) * (k : ℝ) ^ 2 < (2 : ℝ) ^ q := by
    simpa [Nat.cast_mul, Nat.cast_pow, hdcast] using hcertR
  have hgoalR :
      ((m : ℝ) + (d : ℝ) - 1) * (2 / (2 : ℝ) ^ q) <
        (m : ℝ) * (2 / (2 : ℝ) ^ q) + 1 / (k : ℝ) ^ 2 := by
    field_simp [hkR, ne_of_gt hPpos]
    nlinarith [hcertR2, hkRpos]
  simpa [FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, inverseSquareTerm, scale, hscale_eq, hmdcast]
    using hgoalR

/-- Generic right bracket arithmetic for nearest-mantissa rounding in any
positive IEEE-single exponent band represented by `e = 25 - q`. -/
theorem inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
    {m d k q : ℕ} (hk : 0 < k)
    (hright : 2 ^ q < (2 * d + 1) * k ^ 2) :
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          ((25 : ℤ) - (q : ℤ)) +
        inverseSquareTerm k <
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d + 1)
        ((25 : ℤ) - (q : ℤ)) := by
  let scale : ℝ := (2 : ℝ) ^ (((25 : ℤ) - (q : ℤ)) - (24 : ℤ))
  have hscale_eq : scale = 2 / (2 : ℝ) ^ q := by
    simpa [scale] using inverseSquareSingle_scaleAtExponent_eq_two_div_two_pow q
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hPpos : 0 < (2 : ℝ) ^ q := by positivity
  have hkRpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hcertR : (((2 ^ q : ℕ) : ℝ) < (((2 * d + 1) * k ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hright
  have hcertR2 : (2 : ℝ) ^ q < (2 * (d : ℝ) + 1) * (k : ℝ) ^ 2 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hcertR
  have hgoalR :
      (m : ℝ) * (2 / (2 : ℝ) ^ q) + 1 / (k : ℝ) ^ 2 <
        ((m : ℝ) + (d : ℝ) + 1) * (2 / (2 : ℝ) ^ q) := by
    field_simp [hkR, ne_of_gt hPpos]
    nlinarith [hcertR2, hkRpos]
  simpa [FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, inverseSquareTerm, scale, hscale_eq,
    add_assoc, add_comm, add_left_comm] using hgoalR

/-- In the left bracket at arbitrary exponent scale, the exact sum is strictly
closer to the certified target mantissa than to its predecessor. -/
theorem inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
    {m d k q : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hleft : (2 * d - 1) * k ^ 2 < 2 ^ q)
    (hx_lt_target :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k <
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
          ((25 : ℤ) - (q : ℤ))) :
    |(FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
          ((25 : ℤ) - (q : ℤ))| <
      |(FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d - 1)
          ((25 : ℤ) - (q : ℤ))| := by
  let scale : ℝ := (2 : ℝ) ^ (((25 : ℤ) - (q : ℤ)) - (24 : ℤ))
  have hscale_eq : scale = 2 / (2 : ℝ) ^ q := by
    simpa [scale] using inverseSquareSingle_scaleAtExponent_eq_two_div_two_pow q
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hPpos : 0 < (2 : ℝ) ^ q := by positivity
  have hkRpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hcertR : (((2 * d - 1) * k ^ 2 : ℕ) : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast hleft
  have hdcast : ((2 * d - 1 : ℕ) : ℝ) = 2 * (d : ℝ) - 1 := by
    have hsub : 1 ≤ 2 * d := by omega
    rw [Nat.cast_sub hsub]
    norm_num
  have hmdcast : ((m + d - 1 : ℕ) : ℝ) = (m : ℝ) + (d : ℝ) - 1 := by
    have hsub : 1 ≤ m + d := by omega
    rw [Nat.cast_sub hsub]
    norm_num
  have hcertR2 : (2 * (d : ℝ) - 1) * (k : ℝ) ^ 2 < (2 : ℝ) ^ q := by
    simpa [Nat.cast_mul, Nat.cast_pow, hdcast] using hcertR
  have hpred_lt_x :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d - 1)
          ((25 : ℤ) - (q : ℤ)) <
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k :=
    inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
      (m := m) (d := d) (k := k) (q := q) hd hk hleft
  have hxb_nonpos :
      (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
          ((25 : ℤ) - (q : ℤ)) ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hx_lt_target)
  have hxa_nonneg :
      0 ≤ (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d - 1)
          ((25 : ℤ) - (q : ℤ)) :=
    sub_nonneg.mpr (le_of_lt hpred_lt_x)
  rw [abs_of_nonpos hxb_nonpos, abs_of_nonneg hxa_nonneg]
  have hgoalR :
      ((m : ℝ) + (d : ℝ)) * (2 / (2 : ℝ) ^ q) -
          ((m : ℝ) * (2 / (2 : ℝ) ^ q) + 1 / (k : ℝ) ^ 2) <
        ((m : ℝ) * (2 / (2 : ℝ) ^ q) + 1 / (k : ℝ) ^ 2) -
          ((m : ℝ) + (d : ℝ) - 1) * (2 / (2 : ℝ) ^ q) := by
    field_simp [hkR, ne_of_gt hPpos]
    nlinarith [hcertR2, hkRpos]
  simpa [FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, inverseSquareTerm, scale, hscale_eq, hmdcast,
    add_assoc, add_comm, add_left_comm] using hgoalR

/-- In the right bracket at arbitrary exponent scale, the exact sum is strictly
closer to the certified target mantissa than to its successor. -/
theorem inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
    {m d k q : ℕ} (hk : 0 < k)
    (hright : 2 ^ q < (2 * d + 1) * k ^ 2)
    (htarget_lt_x :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
          ((25 : ℤ) - (q : ℤ)) <
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k) :
    |(FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
          ((25 : ℤ) - (q : ℤ))| <
      |(FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d + 1)
          ((25 : ℤ) - (q : ℤ))| := by
  let scale : ℝ := (2 : ℝ) ^ (((25 : ℤ) - (q : ℤ)) - (24 : ℤ))
  have hscale_eq : scale = 2 / (2 : ℝ) ^ q := by
    simpa [scale] using inverseSquareSingle_scaleAtExponent_eq_two_div_two_pow q
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hPpos : 0 < (2 : ℝ) ^ q := by positivity
  have hkRpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hcertR : (((2 ^ q : ℕ) : ℝ) < (((2 * d + 1) * k ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hright
  have hcertR2 : (2 : ℝ) ^ q < (2 * (d : ℝ) + 1) * (k : ℝ) ^ 2 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hcertR
  have hx_lt_succ :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k <
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d + 1)
          ((25 : ℤ) - (q : ℤ)) :=
    inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
      (m := m) (d := d) (k := k) (q := q) hk hright
  have hxb_nonneg :
      0 ≤ (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
          ((25 : ℤ) - (q : ℤ)) :=
    sub_nonneg.mpr (le_of_lt htarget_lt_x)
  have hxc_nonpos :
      (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
            ((25 : ℤ) - (q : ℤ)) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d + 1)
          ((25 : ℤ) - (q : ℤ)) ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hx_lt_succ)
  rw [abs_of_nonneg hxb_nonneg, abs_of_nonpos hxc_nonpos]
  have hgoalR :
      (m : ℝ) * (2 / (2 : ℝ) ^ q) + 1 / (k : ℝ) ^ 2 -
          ((m : ℝ) + (d : ℝ)) * (2 / (2 : ℝ) ^ q) <
        ((m : ℝ) + (d : ℝ) + 1) * (2 / (2 : ℝ) ^ q) -
          ((m : ℝ) * (2 / (2 : ℝ) ^ q) + 1 / (k : ℝ) ^ 2) := by
    field_simp [hkR, ne_of_gt hPpos]
    nlinarith [hcertR2, hkRpos]
  simpa [FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, inverseSquareTerm, scale, hscale_eq,
    add_assoc, add_comm, add_left_comm] using hgoalR

/-- Arbitrary-exponent binary32 nearest-mantissa certificate.  The natural
power `2^q` represents twice the term-to-ulp scale for exponent `e = 25 - q`;
strict integer half-cell inequalities then certify the rounded addition. -/
theorem inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale
    {m d k q : ℕ}
    (hd : 0 < d) (hk : 0 < k)
    (hleft : (2 * d - 1) * k ^ 2 < 2 ^ q)
    (hright : 2 ^ q < (2 * d + 1) * k ^ 2)
    (hmpred :
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d - 1))
    (hmtarget :
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d))
    (hmsucc :
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d + 1))
    (hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (q : ℤ))) :
    inverseSquareSingleForwardStep
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          ((25 : ℤ) - (q : ℤ))) k =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
        ((25 : ℤ) - (q : ℤ)) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let e : ℤ := (25 : ℤ) - (q : ℤ)
  let x : ℝ := fmt.normalizedValue false m e + inverseSquareTerm k
  let y : ℝ := fmt.normalizedValue false (m + d) e
  let pred : ℝ := fmt.normalizedValue false (m + d - 1) e
  let succ : ℝ := fmt.normalizedValue false (m + d + 1) e
  have hpredSystem : fmt.normalizedSystem pred := by
    exact ⟨false, m + d - 1, e, hmpred, hexp, rfl⟩
  have hySystem : fmt.normalizedSystem y := by
    exact ⟨false, m + d, e, hmtarget, hexp, rfl⟩
  have hsuccSystem : fmt.normalizedSystem succ := by
    exact ⟨false, m + d + 1, e, hmsucc, hexp, rfl⟩
  have hpred_lt_x : pred < x := by
    simpa [pred, x, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := m) (d := d) (k := k) (q := q) hd hk hleft
  have hx_lt_succ : x < succ := by
    simpa [succ, x, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := m) (d := d) (k := k) (q := q) hk hright
  have hpred_pos : 0 < pred := by
    simpa [pred, e, fmt] using
      fmt.normalizedValue_false_pos (m := m + d - 1) (e := e) hmpred
  have hy_pos : 0 < y := by
    simpa [y, e, fmt] using
      fmt.normalizedValue_false_pos (m := m + d) (e := e) hmtarget
  have hsucc_pos : 0 < succ := by
    simpa [succ, e, fmt] using
      fmt.normalizedValue_false_pos (m := m + d + 1) (e := e) hmsucc
  by_cases hxy : x = y
  · have hyfinite : fmt.finiteSystem y := Or.inr (Or.inl hySystem)
    have hround : fmt.finiteRoundToEven x = y := by
      rw [hxy]
      exact fmt.finiteRoundToEven_eq_self_of_finiteSystem hyfinite
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact, x, y, e, fmt]
      using hround
  · rcases lt_or_gt_of_ne hxy with hx_lt_y | hy_lt_x
    · have hadj : fmt.realOrderAdjacentNormalized pred y := by
        refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
        refine ⟨false, m + d - 1, e, hmpred, ?_, Or.inl ⟨rfl, ?_⟩⟩
        · simpa [Nat.sub_add_cancel (by omega : 1 ≤ m + d)] using hmtarget
        · simp [y, Nat.sub_add_cancel (by omega : 1 ≤ m + d)]
      have hrightCloser : |x - y| < |x - pred| := by
        simpa [x, y, pred, e, fmt] using
          inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
            (m := m) (d := d) (k := k) (q := q) hd hk hleft
            (by simpa [x, y, e, fmt] using hx_lt_y)
      have hstep :
          inverseSquareSingleForwardStep
              (fmt.normalizedValue false m e) k = y :=
        inverseSquareSingleForwardStep_eq_right_of_adjacent_strict_between_right_closer
          (s := fmt.normalizedValue false m e) (k := k)
          (pred := pred) (y := y) hpredSystem hySystem hadj hpred_pos
          hy_pos (by simpa [x] using ⟨hpred_lt_x, hx_lt_y⟩)
          (by simpa [x] using hrightCloser)
      simpa [y, e, fmt] using hstep
    · have hadj : fmt.realOrderAdjacentNormalized y succ := by
        refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
        exact ⟨false, m + d, e, hmtarget, hmsucc, Or.inl ⟨rfl, rfl⟩⟩
      have hleftCloser : |x - y| < |x - succ| := by
        simpa [x, y, succ, e, fmt] using
          inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
            (m := m) (d := d) (k := k) (q := q) hk hright
            (by simpa [x, y, e, fmt] using hy_lt_x)
      have hstep :
          inverseSquareSingleForwardStep
              (fmt.normalizedValue false m e) k = y :=
        inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer
          (s := fmt.normalizedValue false m e) (k := k)
          (y := y) (succ := succ) hySystem hsuccSystem hadj hy_pos
          hsucc_pos (by simpa [x] using ⟨hy_lt_x, hx_lt_succ⟩)
          (by simpa [x] using hleftCloser)
      simpa [y, e, fmt] using hstep

/-- Arbitrary-exponent binary32 no-change certificate for inverse-square
addition.  If `1/k^2` is strictly below half an ulp at the exponent band
encoded by `q`, then adding it to the positive normalized state rounds back to
the same state.  This is the no-change companion to
`inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale`
and is intended for compressed high-prefix bands where many terms are too small
to move the accumulator. -/
theorem inverseSquareSingleForwardStep_normalizedValue_eq_self_of_scaled_half_ulp_at_scale
    {m k q : ℕ}
    (hk : 0 < k)
    (hsmall : 2 ^ q < k ^ 2)
    (hm :
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmsucc :
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (q : ℤ))) :
    inverseSquareSingleForwardStep
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
          ((25 : ℤ) - (q : ℤ))) k =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
        ((25 : ℤ) - (q : ℤ)) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let e : ℤ := (25 : ℤ) - (q : ℤ)
  let y : ℝ := fmt.normalizedValue false m e
  let succ : ℝ := fmt.normalizedValue false (m + 1) e
  let x : ℝ := y + inverseSquareTerm k
  have hySystem : fmt.normalizedSystem y := by
    exact ⟨false, m, e, hm, hexp, rfl⟩
  have hsuccSystem : fmt.normalizedSystem succ := by
    exact ⟨false, m + 1, e, hmsucc, hexp, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized y succ := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, m, e, hm, hmsucc, Or.inl ⟨rfl, rfl⟩⟩
  have hy_pos : 0 < y := by
    simpa [y, e, fmt] using
      fmt.normalizedValue_false_pos (m := m) (e := e) hm
  have hsucc_pos : 0 < succ := by
    simpa [succ, e, fmt] using
      fmt.normalizedValue_false_pos (m := m + 1) (e := e) hmsucc
  have hy_lt_x : y < x := by
    simp [x]
    exact inverseSquareTerm_pos_of_pos hk
  have hx_lt_succ : x < succ := by
    simpa [x, y, succ, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := m) (d := 0) (k := k) (q := q) hk
        (by simpa using hsmall)
  have hleftCloser : |x - y| < |x - succ| := by
    simpa [x, y, succ, e, fmt] using
      inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
        (m := m) (d := 0) (k := k) (q := q) hk
        (by simpa using hsmall)
        (by simpa [x, y] using hy_lt_x)
  exact
    inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer
      (s := fmt.normalizedValue false m e) (k := k)
      (y := y) (succ := succ) hySystem hsuccSystem hadj hy_pos
      hsucc_pos (by simpa [x] using ⟨hy_lt_x, hx_lt_succ⟩)
      (by simpa [x, y, e, fmt] using hleftCloser)

/-- Nearest mantissa increment for an inverse-square term in the binary32
exponent band encoded by the scale `2^q`. -/
def inverseSquareSingleScaledMantissaIncrement (q k : ℕ) : ℕ :=
  (2 ^ q + k ^ 2) / (2 * k ^ 2)

/-- Reverse-order prefix sum of scaled mantissa increments.  Starting from
`kTop`, this sums the certified increments for `kTop, kTop-1, ...`. -/
def inverseSquareSingleReverseScaledMantissaPrefix (q kTop : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      inverseSquareSingleReverseScaledMantissaPrefix q kTop n +
        inverseSquareSingleScaledMantissaIncrement q (kTop - n)

@[simp] theorem inverseSquareSingleReverseScaledMantissaPrefix_zero
    (q kTop : ℕ) :
    inverseSquareSingleReverseScaledMantissaPrefix q kTop 0 = 0 := rfl

@[simp] theorem inverseSquareSingleReverseScaledMantissaPrefix_succ
    (q kTop n : ℕ) :
    inverseSquareSingleReverseScaledMantissaPrefix q kTop (n + 1) =
      inverseSquareSingleReverseScaledMantissaPrefix q kTop n +
        inverseSquareSingleScaledMantissaIncrement q (kTop - n) := rfl

/-- The forward single-precision accumulator obtained by starting from `start`
and adding `1/k0^2`, `1/(k0+1)^2`, ..., left-to-right.  The third argument is
the number of rounded additions performed. -/
noncomputable def inverseSquareSingleForwardAccumulatorFrom
    (start : ℝ) (k0 : ℕ) : ℕ → ℝ
  | 0 => start
  | n + 1 =>
      inverseSquareSingleForwardStep
        (inverseSquareSingleForwardAccumulatorFrom start k0 n) (k0 + n)

/-- The actual left-to-right single-precision accumulator for Higham §1.12.3's
forward summation, starting at `0` and adding `1/1^2`, `1/2^2`, ... .  The
argument is the number of rounded additions performed. -/
noncomputable def inverseSquareSingleForwardAccumulator (n : ℕ) : ℝ :=
  inverseSquareSingleForwardAccumulatorFrom 0 1 n

@[simp] theorem inverseSquareSingleForwardAccumulatorFrom_zero
    (start : ℝ) (k0 : ℕ) :
    inverseSquareSingleForwardAccumulatorFrom start k0 0 = start := rfl

@[simp] theorem inverseSquareSingleForwardAccumulatorFrom_succ
    (start : ℝ) (k0 n : ℕ) :
    inverseSquareSingleForwardAccumulatorFrom start k0 (n + 1) =
      inverseSquareSingleForwardStep
        (inverseSquareSingleForwardAccumulatorFrom start k0 n) (k0 + n) := rfl

/-- Split a forward accumulator trace after `n` rounded additions. -/
theorem inverseSquareSingleForwardAccumulatorFrom_add
    (start : ℝ) (k0 n r : ℕ) :
    inverseSquareSingleForwardAccumulatorFrom start k0 (n + r) =
      inverseSquareSingleForwardAccumulatorFrom
        (inverseSquareSingleForwardAccumulatorFrom start k0 n) (k0 + n) r := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      calc
        inverseSquareSingleForwardAccumulatorFrom start k0 (n + (r + 1)) =
            inverseSquareSingleForwardStep
              (inverseSquareSingleForwardAccumulatorFrom start k0 (n + r))
              (k0 + (n + r)) := by
          rw [show n + (r + 1) = (n + r) + 1 by omega]
          rfl
        _ =
            inverseSquareSingleForwardStep
              (inverseSquareSingleForwardAccumulatorFrom
                (inverseSquareSingleForwardAccumulatorFrom start k0 n)
                (k0 + n) r) ((k0 + n) + r) := by
          rw [ih]
          congr 1
          omega
        _ =
            inverseSquareSingleForwardAccumulatorFrom
              (inverseSquareSingleForwardAccumulatorFrom start k0 n)
              (k0 + n) (r + 1) := by
          rfl

/-- Split the actual forward accumulator after `n` rounded additions. -/
theorem inverseSquareSingleForwardAccumulator_add (n r : ℕ) :
    inverseSquareSingleForwardAccumulator (n + r) =
      inverseSquareSingleForwardAccumulatorFrom
        (inverseSquareSingleForwardAccumulator n) (1 + n) r := by
  simpa [inverseSquareSingleForwardAccumulator, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using
    inverseSquareSingleForwardAccumulatorFrom_add (start := 0) (k0 := 1) n r

/-- Reverse-order single-precision accumulator for Higham §1.12.3.  Starting
from `start`, this adds `1/kTop^2`, then `1/(kTop-1)^2`, and so on for the
specified number of rounded additions.  Statements that use this definition
should keep the number of additions at most `kTop`; beyond that point natural
subtraction saturates the term index at zero. -/
noncomputable def inverseSquareSingleReverseAccumulatorFrom
    (start : ℝ) (kTop : ℕ) : ℕ → ℝ
  | 0 => start
  | n + 1 =>
      inverseSquareSingleForwardStep
        (inverseSquareSingleReverseAccumulatorFrom start kTop n) (kTop - n)

/-- The reverse-order single-precision accumulator that takes exactly `N`
terms, from `1/N^2` down to `1/1^2`.  This is the operation order used for
the `10^9`-term cure in Higham §1.12.3. -/
noncomputable def inverseSquareSingleReverseAccumulator (N : ℕ) : ℝ :=
  inverseSquareSingleReverseAccumulatorFrom 0 N N

@[simp] theorem inverseSquareSingleReverseAccumulatorFrom_zero
    (start : ℝ) (kTop : ℕ) :
    inverseSquareSingleReverseAccumulatorFrom start kTop 0 = start := rfl

@[simp] theorem inverseSquareSingleReverseAccumulatorFrom_succ
    (start : ℝ) (kTop n : ℕ) :
    inverseSquareSingleReverseAccumulatorFrom start kTop (n + 1) =
      inverseSquareSingleForwardStep
        (inverseSquareSingleReverseAccumulatorFrom start kTop n) (kTop - n) := rfl

/-- Split a reverse-order accumulator trace after `n` rounded additions. -/
theorem inverseSquareSingleReverseAccumulatorFrom_add
    (start : ℝ) (kTop n r : ℕ) :
    inverseSquareSingleReverseAccumulatorFrom start kTop (n + r) =
      inverseSquareSingleReverseAccumulatorFrom
        (inverseSquareSingleReverseAccumulatorFrom start kTop n) (kTop - n) r := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      calc
        inverseSquareSingleReverseAccumulatorFrom start kTop (n + (r + 1)) =
            inverseSquareSingleForwardStep
              (inverseSquareSingleReverseAccumulatorFrom start kTop (n + r))
              (kTop - (n + r)) := by
          rw [show n + (r + 1) = (n + r) + 1 by omega]
          rfl
        _ =
            inverseSquareSingleForwardStep
              (inverseSquareSingleReverseAccumulatorFrom
                (inverseSquareSingleReverseAccumulatorFrom start kTop n)
                (kTop - n) r) ((kTop - n) - r) := by
          rw [ih]
          congr 1
          omega
        _ =
            inverseSquareSingleReverseAccumulatorFrom
              (inverseSquareSingleReverseAccumulatorFrom start kTop n)
              (kTop - n) (r + 1) := by
          rfl

/-- Every concrete IEEE-single reverse accumulator state is finite, provided
the start state is finite.  This is the finite-format foothold for later
high-prefix nearest-cell/window certificates. -/
theorem inverseSquareSingleReverseAccumulatorFrom_finiteSystem_of_start
    {start : ℝ}
    (hstart : FloatingPointFormat.ieeeSingleFormat.finiteSystem start)
    (kTop n : ℕ) :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (inverseSquareSingleReverseAccumulatorFrom start kTop n) := by
  induction n with
  | zero =>
      simpa [inverseSquareSingleReverseAccumulatorFrom] using hstart
  | succ n _ih =>
      simpa [inverseSquareSingleReverseAccumulatorFrom, inverseSquareSingleForwardStep] using
        (FloatingPointFormat.finiteRoundToEvenOp_finiteSystem
          FloatingPointFormat.ieeeSingleFormat BasicOp.add
          (inverseSquareSingleReverseAccumulatorFrom start kTop n)
          (inverseSquareTerm (kTop - n)))

/-- Generic same-exponent reverse-suffix band certificate.  If each reverse
term in a band has a checked nearest-mantissa increment at the fixed binary32
scale `q`, then the rounded reverse accumulator follows the certified mantissa
prefix for the whole band. -/
theorem inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
    {base q kTop count : ℕ}
    (hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (q : ℤ)))
    (hcert :
      ∀ {n : ℕ}, n < count →
        let m := base + inverseSquareSingleReverseScaledMantissaPrefix q kTop n
        let k := kTop - n
        let d := inverseSquareSingleScaledMantissaIncrement q k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ q ∧
          2 ^ q < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216)
    (n : ℕ) (hn : n ≤ count) :
    inverseSquareSingleReverseAccumulatorFrom
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false base
          ((25 : ℤ) - (q : ℤ))) kTop n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (base + inverseSquareSingleReverseScaledMantissaPrefix q kTop n)
        ((25 : ℤ) - (q : ℤ)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hnle : n ≤ count := by omega
      have hnlt : n < count := by omega
      have hstepCert := hcert hnlt
      let m := base + inverseSquareSingleReverseScaledMantissaPrefix q kTop n
      let k := kTop - n
      let d := inverseSquareSingleScaledMantissaIncrement q k
      rcases hstepCert with
        ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
      have hmin' : 8388608 ≤ m + d - 1 := by
        simpa [m, d, k] using hmin
      have hmax' : m + d + 1 < 16777216 := by
        simpa [m, d, k] using hmax
      have hmpred :
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d - 1) := by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa,
          FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
        omega
      have hmtarget :
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d) := by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa,
          FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
        omega
      have hmsucc :
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d + 1) := by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa,
          FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
        omega
      have hstep :
          inverseSquareSingleForwardStep
              (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
                ((25 : ℤ) - (q : ℤ))) k =
            FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
              ((25 : ℤ) - (q : ℤ)) :=
        inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale
          (m := m) (d := d) (k := k) (q := q)
          hdpos hkpos hleft hright hmpred hmtarget hmsucc hexp
      calc
        inverseSquareSingleReverseAccumulatorFrom
            (FloatingPointFormat.ieeeSingleFormat.normalizedValue false base
              ((25 : ℤ) - (q : ℤ))) kTop (n + 1) =
          inverseSquareSingleForwardStep
            (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
              ((25 : ℤ) - (q : ℤ))) k := by
            simp [inverseSquareSingleReverseAccumulatorFrom, ih hnle, m, k]
        _ =
          FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
            ((25 : ℤ) - (q : ℤ)) := hstep
        _ =
          FloatingPointFormat.ieeeSingleFormat.normalizedValue false
            (base +
              inverseSquareSingleReverseScaledMantissaPrefix q kTop (n + 1))
            ((25 : ℤ) - (q : ℤ)) := by
            simp [m, d, k, inverseSquareSingleReverseScaledMantissaPrefix,
              add_assoc]

/-- Source-named unfolding of the `10^9`-term reverse-order accumulator from
Higham §1.12.3. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9) := rfl

/-- Split the actual reverse-order accumulator after an initial high-index
block.  If `n + r` terms are requested, the first `n` rounded additions consume
indices `n+r, ..., r+1`; the remaining `r` additions consume `r, ..., 1`. -/
theorem inverseSquareSingleReverseAccumulator_split (n r : ℕ) :
    inverseSquareSingleReverseAccumulator (n + r) =
      inverseSquareSingleReverseAccumulatorFrom
        (inverseSquareSingleReverseAccumulatorFrom 0 (n + r) n) r r := by
  unfold inverseSquareSingleReverseAccumulator
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show (n + r) - n = r by omega]

/-- Source-shaped split for Higham §1.12.3's `10^9`-term reverse-order run:
first sum the terms with indices above `4096`, then continue with the final
`4096` low-index terms. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096 :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReverseAccumulatorFrom
        (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096))
        4096 4096 := by
  have hN : (10 ^ 9 - 4096) + 4096 = (10 ^ 9 : ℕ) := by norm_num
  rw [← hN]
  exact inverseSquareSingleReverseAccumulator_split (10 ^ 9 - 4096) 4096

/-- Every index consumed in the high-index prefix of the source's `10^9`-term
reverse-order run is still above the forward stagnation index. -/
theorem inverseSquareReverseTenPowNineHighPrefix_index_ge_4097
    {j : ℕ} (hj : j < 10 ^ 9 - 4096) :
    4097 ≤ (10 ^ 9 : ℕ) - j := by
  norm_num at hj ⊢
  omega

/-- Every index consumed before the final high-prefix binade split is at least
`8192`.  This isolates the `10^9, ..., 8193` block from the later
`8192, ..., 4097` binade. -/
theorem inverseSquareReverseTenPowNineHighPrefix_index_ge_8192
    {j : ℕ} (hj : j < 10 ^ 9 - 8192) :
    8192 ≤ (10 ^ 9 : ℕ) - j := by
  norm_num at hj ⊢
  omega

/-- Consequently, every inverse-square term in that high-index reverse prefix
is bounded by the same `2^-24` threshold used in the forward stagnation
analysis. -/
theorem inverseSquareTerm_le_two_pow_neg_24_of_reverse_ten_pow_nine_high_prefix
    {j : ℕ} (hj : j < 10 ^ 9 - 4096) :
    inverseSquareTerm ((10 ^ 9 : ℕ) - j) ≤ 1 / (2 : ℝ) ^ 24 := by
  apply inverseSquareTerm_le_two_pow_neg_24_of_ge
  have hge :=
    inverseSquareReverseTenPowNineHighPrefix_index_ge_4097 (j := j) hj
  omega

/-- Terms in the earlier `10^9, ..., 8193` high-prefix block are already below
the sharper `2^-26` binade threshold. -/
theorem inverseSquareTerm_le_two_pow_neg_26_of_reverse_ten_pow_nine_high_binade
    {j : ℕ} (hj : j < 10 ^ 9 - 8192) :
    inverseSquareTerm ((10 ^ 9 : ℕ) - j) ≤ 1 / (2 : ℝ) ^ 26 := by
  apply inverseSquareTerm_le_two_pow_neg_26_of_ge_8192
  exact inverseSquareReverseTenPowNineHighPrefix_index_ge_8192 (j := j) hj

/-- Exact real reverse-order accumulator matching the term order of the
single-precision reverse accumulator, but without rounding.  This is used for
non-enumerative mass bounds on the large high-index prefix. -/
noncomputable def inverseSquareExactReverseAccumulatorFrom
    (start : ℝ) (kTop : ℕ) : ℕ → ℝ
  | 0 => start
  | n + 1 =>
      inverseSquareExactReverseAccumulatorFrom start kTop n + inverseSquareTerm (kTop - n)

@[simp] theorem inverseSquareExactReverseAccumulatorFrom_zero
    (start : ℝ) (kTop : ℕ) :
    inverseSquareExactReverseAccumulatorFrom start kTop 0 = start := rfl

@[simp] theorem inverseSquareExactReverseAccumulatorFrom_succ
    (start : ℝ) (kTop n : ℕ) :
    inverseSquareExactReverseAccumulatorFrom start kTop (n + 1) =
      inverseSquareExactReverseAccumulatorFrom start kTop n + inverseSquareTerm (kTop - n) := rfl

/-- Exact real reverse-order accumulator that takes exactly `N` terms, from
`1/N^2` down to `1/1^2`, with no rounding. -/
noncomputable def inverseSquareExactReverseAccumulator (N : ℕ) : ℝ :=
  inverseSquareExactReverseAccumulatorFrom 0 N N

/-- Exact reverse accumulation is affine in its starting accumulator. -/
theorem inverseSquareExactReverseAccumulatorFrom_add_start
    (start : ℝ) (kTop n : ℕ) :
    inverseSquareExactReverseAccumulatorFrom start kTop n =
      start + inverseSquareExactReverseAccumulatorFrom 0 kTop n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        inverseSquareExactReverseAccumulatorFrom start kTop (n + 1) =
            inverseSquareExactReverseAccumulatorFrom start kTop n +
              inverseSquareTerm (kTop - n) := rfl
        _ =
            (start + inverseSquareExactReverseAccumulatorFrom 0 kTop n) +
              inverseSquareTerm (kTop - n) := by
          rw [ih]
        _ = start + inverseSquareExactReverseAccumulatorFrom 0 kTop (n + 1) := by
          simp [add_assoc]

/-- Split an exact reverse-order accumulator trace after `n` additions. -/
theorem inverseSquareExactReverseAccumulatorFrom_add
    (start : ℝ) (kTop n r : ℕ) :
    inverseSquareExactReverseAccumulatorFrom start kTop (n + r) =
      inverseSquareExactReverseAccumulatorFrom
        (inverseSquareExactReverseAccumulatorFrom start kTop n) (kTop - n) r := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      calc
        inverseSquareExactReverseAccumulatorFrom start kTop (n + (r + 1)) =
            inverseSquareExactReverseAccumulatorFrom start kTop (n + r) +
              inverseSquareTerm (kTop - (n + r)) := by
          rw [show n + (r + 1) = (n + r) + 1 by omega]
          rfl
        _ =
            inverseSquareExactReverseAccumulatorFrom
                (inverseSquareExactReverseAccumulatorFrom start kTop n)
                (kTop - n) r +
              inverseSquareTerm ((kTop - n) - r) := by
          rw [ih]
          rw [Nat.sub_sub]
        _ =
            inverseSquareExactReverseAccumulatorFrom
              (inverseSquareExactReverseAccumulatorFrom start kTop n)
              (kTop - n) (r + 1) := by
          rfl

/-- Split the exact `n+r`-term reverse sum into the high-index prefix followed
by the final `r` low-index terms. -/
theorem inverseSquareExactReverseAccumulator_split (n r : ℕ) :
    inverseSquareExactReverseAccumulator (n + r) =
      inverseSquareExactReverseAccumulatorFrom
        (inverseSquareExactReverseAccumulatorFrom 0 (n + r) n) r r := by
  unfold inverseSquareExactReverseAccumulator
  rw [inverseSquareExactReverseAccumulatorFrom_add]
  rw [show (n + r) - n = r by omega]

/-- Exact-real counterpart of the source-shaped `10^9`/`4096` reverse split. -/
theorem inverseSquareExactReverseAccumulator_ten_pow_nine_split_4096 :
    inverseSquareExactReverseAccumulator (10 ^ 9) =
      inverseSquareExactReverseAccumulatorFrom
        (inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096))
        4096 4096 := by
  have hN : (10 ^ 9 - 4096) + 4096 = (10 ^ 9 : ℕ) := by norm_num
  rw [← hN]
  exact inverseSquareExactReverseAccumulator_split (10 ^ 9 - 4096) 4096

/-- The exact `10^9`-term reverse sum is the exact high-index prefix plus the
exact final `4096` low-index reverse sum. -/
theorem inverseSquareExactReverseAccumulator_ten_pow_nine_eq_highPrefix_add_low4096 :
    inverseSquareExactReverseAccumulator (10 ^ 9) =
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) +
        inverseSquareExactReverseAccumulator 4096 := by
  rw [inverseSquareExactReverseAccumulator_ten_pow_nine_split_4096]
  rw [inverseSquareExactReverseAccumulatorFrom_add_start]
  rfl

/-- Every inverse-square term is nonnegative, with the `k = 0` case handled by
Lean's totalized real division. -/
theorem inverseSquareTerm_nonneg (k : ℕ) : 0 ≤ inverseSquareTerm k := by
  by_cases hk : k = 0
  · simp [inverseSquareTerm, hk]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    exact le_of_lt (inverseSquareTerm_pos_of_pos hkpos)

/-- One rounded inverse-square addition cannot decrease a finite IEEE-single
state. -/
theorem inverseSquareSingleForwardStep_ge_self_of_finiteSystem
    {s : ℝ} (hs : FloatingPointFormat.ieeeSingleFormat.finiteSystem s)
    (k : ℕ) :
    s ≤ inverseSquareSingleForwardStep s k := by
  simpa [inverseSquareSingleForwardStep] using
    (FloatingPointFormat.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
      (fmt := FloatingPointFormat.ieeeSingleFormat) hs
      (inverseSquareTerm_nonneg k))

/-- One rounded inverse-square addition has absolute rounding error bounded by
the inverse-square term, using the previous finite accumulator as a comparison
point. -/
theorem inverseSquareSingleForwardStep_abs_error_le_term_of_finiteSystem
    {s : ℝ} (hs : FloatingPointFormat.ieeeSingleFormat.finiteSystem s)
    (k : ℕ) :
    |inverseSquareSingleForwardStep s k - (s + inverseSquareTerm k)| ≤
      inverseSquareTerm k := by
  simpa [inverseSquareSingleForwardStep] using
    (FloatingPointFormat.finiteRoundToEvenOp_add_abs_error_le_right_of_finiteSystem_of_nonneg
      (fmt := FloatingPointFormat.ieeeSingleFormat) hs
      (inverseSquareTerm_nonneg k))

/-- One rounded inverse-square addition increases a finite IEEE-single state by
at most twice the term being added. -/
theorem inverseSquareSingleForwardStep_le_self_add_two_mul_term_of_finiteSystem
    {s : ℝ} (hs : FloatingPointFormat.ieeeSingleFormat.finiteSystem s)
    (k : ℕ) :
    inverseSquareSingleForwardStep s k ≤ s + 2 * inverseSquareTerm k := by
  simpa [inverseSquareSingleForwardStep] using
    (FloatingPointFormat.finiteRoundToEvenOp_add_le_left_add_two_mul_right_of_finiteSystem_of_nonneg
      (fmt := FloatingPointFormat.ieeeSingleFormat) hs
      (inverseSquareTerm_nonneg k))

/-- Reverse-order rounded accumulation is monotone above its finite starting
state, because every term added is nonnegative and every rounded addition keeps
the previous finite accumulator as a lower bound. -/
theorem inverseSquareSingleReverseAccumulatorFrom_start_le_of_finiteSystem
    {start : ℝ}
    (hstart : FloatingPointFormat.ieeeSingleFormat.finiteSystem start)
    (kTop n : ℕ) :
    start ≤ inverseSquareSingleReverseAccumulatorFrom start kTop n := by
  induction n with
  | zero =>
      simp [inverseSquareSingleReverseAccumulatorFrom]
  | succ n ih =>
      calc
        start ≤ inverseSquareSingleReverseAccumulatorFrom start kTop n := ih
        _ ≤ inverseSquareSingleForwardStep
              (inverseSquareSingleReverseAccumulatorFrom start kTop n)
              (kTop - n) :=
            inverseSquareSingleForwardStep_ge_self_of_finiteSystem
              (inverseSquareSingleReverseAccumulatorFrom_finiteSystem_of_start
                hstart kTop n)
              (kTop - n)
        _ = inverseSquareSingleReverseAccumulatorFrom start kTop (n + 1) := rfl

/-- Reverse-order rounded accumulation is monotone in the number of steps,
provided the initial state is a binary32 finite-system value. -/
theorem inverseSquareSingleReverseAccumulatorFrom_le_of_le_steps
    {start : ℝ}
    (hstart : FloatingPointFormat.ieeeSingleFormat.finiteSystem start)
    {kTop n m : ℕ} (hnm : n ≤ m) :
    inverseSquareSingleReverseAccumulatorFrom start kTop n ≤
      inverseSquareSingleReverseAccumulatorFrom start kTop m := by
  rw [show m = n + (m - n) by omega]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  exact inverseSquareSingleReverseAccumulatorFrom_start_le_of_finiteSystem
    (inverseSquareSingleReverseAccumulatorFrom_finiteSystem_of_start
      hstart kTop n)
    (kTop - n) (m - n)

/-- Nonnegativity specialization of the reverse-order monotonicity theorem. -/
theorem inverseSquareSingleReverseAccumulatorFrom_nonneg_of_start_nonneg
    {start : ℝ}
    (hstart : FloatingPointFormat.ieeeSingleFormat.finiteSystem start)
    (hstart_nonneg : 0 ≤ start) (kTop n : ℕ) :
    0 ≤ inverseSquareSingleReverseAccumulatorFrom start kTop n :=
  le_trans hstart_nonneg
    (inverseSquareSingleReverseAccumulatorFrom_start_le_of_finiteSystem
      hstart kTop n)

/-- Crude but reusable upper envelope for reverse-order rounded accumulation:
starting from a finite value, the rounded trace is bounded by the start plus
twice the corresponding exact nonnegative term mass. -/
theorem inverseSquareSingleReverseAccumulatorFrom_le_start_add_two_mul_exact_zero_start
    {start : ℝ}
    (hstart : FloatingPointFormat.ieeeSingleFormat.finiteSystem start)
    (kTop n : ℕ) :
    inverseSquareSingleReverseAccumulatorFrom start kTop n ≤
      start + 2 * inverseSquareExactReverseAccumulatorFrom 0 kTop n := by
  induction n with
  | zero =>
      simp [inverseSquareSingleReverseAccumulatorFrom,
        inverseSquareExactReverseAccumulatorFrom]
  | succ n ih =>
      have hfin :
          FloatingPointFormat.ieeeSingleFormat.finiteSystem
            (inverseSquareSingleReverseAccumulatorFrom start kTop n) :=
        inverseSquareSingleReverseAccumulatorFrom_finiteSystem_of_start
          hstart kTop n
      have hstep :=
        inverseSquareSingleForwardStep_le_self_add_two_mul_term_of_finiteSystem
          hfin (kTop - n)
      calc
        inverseSquareSingleReverseAccumulatorFrom start kTop (n + 1) =
            inverseSquareSingleForwardStep
              (inverseSquareSingleReverseAccumulatorFrom start kTop n)
              (kTop - n) := rfl
        _ ≤ inverseSquareSingleReverseAccumulatorFrom start kTop n +
              2 * inverseSquareTerm (kTop - n) := hstep
        _ ≤ start + 2 * inverseSquareExactReverseAccumulatorFrom 0 kTop n +
              2 * inverseSquareTerm (kTop - n) := by linarith
        _ = start + 2 * inverseSquareExactReverseAccumulatorFrom 0 kTop (n + 1) := by
              rw [inverseSquareExactReverseAccumulatorFrom_succ]
              ring

/-- Telescoping majorant for the inverse-square tail:
`1/k^2 <= 1/(k-1) - 1/k` for `k >= 2`. -/
theorem inverseSquareTerm_le_telescope {k : ℕ} (hk : 2 ≤ k) :
    inverseSquareTerm k ≤ 1 / (((k - 1 : ℕ) : ℝ)) - 1 / (k : ℝ) := by
  have hkRpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hk)
  have hkRgt1 : (1 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hk)
  have hk1posNat : 0 < k - 1 := by omega
  have hk1Rpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast hk1posNat
  have hk1R : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    have h1 : 1 ≤ k := by omega
    rw [Nat.cast_sub h1]
    norm_num
  have hprod_pos : 0 < (((k - 1 : ℕ) : ℝ) * (k : ℝ)) := mul_pos hk1Rpos hkRpos
  have hden_le : (((k - 1 : ℕ) : ℝ) * (k : ℝ)) ≤ (k : ℝ) ^ 2 := by
    rw [hk1R]
    nlinarith [hkRpos]
  have hfrac : 1 / ((k : ℝ) ^ 2) ≤ 1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ)) := by
    exact one_div_le_one_div_of_le hprod_pos hden_le
  have htel : 1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ)) =
      1 / (((k - 1 : ℕ) : ℝ)) - 1 / (k : ℝ) := by
    field_simp [ne_of_gt hk1Rpos, ne_of_gt hkRpos]
    rw [hk1R]
    ring
  calc
    inverseSquareTerm k = 1 / ((k : ℝ) ^ 2) := by rfl
    _ ≤ 1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ)) := hfrac
    _ = 1 / (((k - 1 : ℕ) : ℝ)) - 1 / (k : ℝ) := htel

/-- Non-enumerative bound for a reverse exact prefix: the exact mass of the
terms `kTop, kTop-1, ..., kTop-n+1` is bounded by the telescoping tail
`1/(kTop-n) - 1/kTop`. -/
theorem inverseSquareExactReverseAccumulatorFrom_le_telescope
    {kTop n : ℕ} (hn : n ≤ kTop - 1) :
    inverseSquareExactReverseAccumulatorFrom 0 kTop n ≤
      1 / (((kTop - n : ℕ) : ℝ)) - 1 / (kTop : ℝ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hn' : n ≤ kTop - 1 := by omega
      have hidx : 2 ≤ kTop - n := by omega
      have hstep := inverseSquareTerm_le_telescope (k := kTop - n) hidx
      have hstep' :
          inverseSquareTerm (kTop - n) ≤
            1 / (((kTop - (n + 1) : ℕ) : ℝ)) -
              1 / (((kTop - n : ℕ) : ℝ)) := by
        rw [show (kTop - n) - 1 = kTop - (n + 1) by omega] at hstep
        exact hstep
      calc
        inverseSquareExactReverseAccumulatorFrom 0 kTop (n + 1) =
            inverseSquareExactReverseAccumulatorFrom 0 kTop n +
                inverseSquareTerm (kTop - n) := rfl
        _ ≤ (1 / (((kTop - n : ℕ) : ℝ)) - 1 / (kTop : ℝ)) +
              (1 / (((kTop - (n + 1) : ℕ) : ℝ)) -
                1 / (((kTop - n : ℕ) : ℝ))) := by
            exact add_le_add (ih hn') hstep'
        _ = 1 / (((kTop - (n + 1) : ℕ) : ℝ)) - 1 / (kTop : ℝ) := by ring

/-- The exact real mass of the source's reverse-order high-index prefix
`10^9, 10^9-1, ..., 4097` is at most `1/4096`.  This is the chunk-level
foundation for the remaining reverse-order floating-point trace, avoiding any
enumeration of the billion-step prefix. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096 :
    inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
      1 / (4096 : ℝ) := by
  have hn : (10 ^ 9 - 4096 : ℕ) ≤ (10 ^ 9 : ℕ) - 1 := by norm_num
  have htel := inverseSquareExactReverseAccumulatorFrom_le_telescope
    (kTop := 10 ^ 9) (n := 10 ^ 9 - 4096) hn
  have hden : ((10 ^ 9 : ℕ) - (10 ^ 9 - 4096 : ℕ) : ℕ) = 4096 := by norm_num
  rw [hden] at htel
  have hnonneg : 0 ≤ 1 / ((10 ^ 9 : ℕ) : ℝ) := by norm_num
  nlinarith

/-- Consequently, the exact real contribution of all terms above `4096` in the
source's `10^9`-term reverse sum is at most `1/4096`. -/
theorem inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_le_inv_4096 :
    inverseSquareExactReverseAccumulator (10 ^ 9) -
        inverseSquareExactReverseAccumulator 4096 ≤
      1 / (4096 : ℝ) := by
  rw [inverseSquareExactReverseAccumulator_ten_pow_nine_eq_highPrefix_add_low4096]
  ring_nf
  exact inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096

/-- The binary32 value printed in Higham §1.12.3 for the reverse-order
`10^9`-term summation, represented as the exact IEEE-single grid point whose
usual decimal rendering is `1.64493406`. -/
noncomputable def inverseSquareSingleReversePrintedAccumulator : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13798707 (1 : ℤ)

/-- Lower endpoint of the binary32 start window for the final `4096` reverse
additions in the archived optional repository model. -/
noncomputable def inverseSquareSingleReverseSuffixStartLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16773049 (-12 : ℤ)

/-- Upper endpoint of the binary32 start window for the final `4096` reverse
additions in the archived optional repository model. -/
noncomputable def inverseSquareSingleReverseSuffixStartUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8389596 (-11 : ℤ)

/-- Tighter upper endpoint of the binary32 start window for the final `4096`
reverse additions in the archived optional repository model.  This refines
`inverseSquareSingleReverseSuffixStartUpper` by staying in the exponent-`-12`
bin. -/
noncomputable def inverseSquareSingleReverseSuffixStartUpperTight : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16777650 (-12 : ℤ)

/-- Lower telescoping minorant for inverse-square terms:
`1/k - 1/(k+1) <= 1/k^2` for `k >= 1`. -/
theorem inverseSquareTerm_ge_telescope_succ {k : ℕ} (hk : 1 ≤ k) :
    1 / (k : ℝ) - 1 / (((k + 1 : ℕ) : ℝ)) ≤ inverseSquareTerm k := by
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1Rpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k + 1)
  have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkRpos
  have hk1R_ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hk1Rpos
  have hk1R : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
  have hden_le : (k : ℝ) ^ 2 ≤ (k : ℝ) * (((k + 1 : ℕ) : ℝ)) := by
    rw [hk1R]
    nlinarith [hkRpos]
  have hfrac :
      1 / ((k : ℝ) * (((k + 1 : ℕ) : ℝ))) ≤ 1 / ((k : ℝ) ^ 2) := by
    exact one_div_le_one_div_of_le (pow_pos hkRpos 2) hden_le
  have htel :
      1 / (k : ℝ) - 1 / (((k + 1 : ℕ) : ℝ)) =
        1 / ((k : ℝ) * (((k + 1 : ℕ) : ℝ))) := by
    field_simp [hkR_ne, hk1R_ne]
    rw [hk1R]
    ring
  calc
    1 / (k : ℝ) - 1 / (((k + 1 : ℕ) : ℝ)) =
        1 / ((k : ℝ) * (((k + 1 : ℕ) : ℝ))) := htel
    _ ≤ 1 / ((k : ℝ) ^ 2) := hfrac
    _ = inverseSquareTerm k := by rfl

/-- Non-enumerative lower bound for a reverse exact prefix: the exact mass of
the terms `kTop, kTop-1, ..., kTop-n+1` dominates the telescoping tail
`1/(kTop-n+1) - 1/(kTop+1)`. -/
theorem inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ
    {kTop n : ℕ} (hn : n ≤ kTop) :
    1 / (((kTop - n + 1 : ℕ) : ℝ)) -
        1 / (((kTop + 1 : ℕ) : ℝ)) ≤
      inverseSquareExactReverseAccumulatorFrom 0 kTop n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hn' : n ≤ kTop := by omega
      have hidx : 1 ≤ kTop - n := by omega
      have hstep := inverseSquareTerm_ge_telescope_succ (k := kTop - n) hidx
      calc
        1 / (((kTop - (n + 1) + 1 : ℕ) : ℝ)) -
            1 / (((kTop + 1 : ℕ) : ℝ)) =
          (1 / (((kTop - n : ℕ) : ℝ)) -
              1 / (((kTop - n + 1 : ℕ) : ℝ))) +
            (1 / (((kTop - n + 1 : ℕ) : ℝ)) -
              1 / (((kTop + 1 : ℕ) : ℝ))) := by
            have hsub : kTop - (n + 1) + 1 = kTop - n := by omega
            rw [hsub]
            ring
        _ ≤ inverseSquareTerm (kTop - n) +
              inverseSquareExactReverseAccumulatorFrom 0 kTop n := by
            exact add_le_add hstep (ih hn')
        _ = inverseSquareExactReverseAccumulatorFrom 0 kTop (n + 1) := by
            rw [inverseSquareExactReverseAccumulatorFrom_succ]
            ring

/-- Sharper shifted lower telescoping minorant for inverse-square terms in the
high-prefix range.  The shift `4096/8193` is just below one half, so the
telescoping difference is much tighter than the coarse `1/k - 1/(k+1)` bound
while still lying below `1/k^2` for every `k >= 4097`. -/
theorem inverseSquareTerm_ge_shifted_telescope_4096_8193
    {k : ℕ} (hk : 4097 ≤ k) :
    1 / ((k : ℝ) - (4096 : ℝ) / 8193) -
        1 / (((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193) ≤
      inverseSquareTerm k := by
  have hkRpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4097) hk)
  have hkR_ge : (4097 : ℝ) ≤ k := by exact_mod_cast hk
  have hleft_pos : (0 : ℝ) < (k : ℝ) - (4096 : ℝ) / 8193 := by
    nlinarith [hkR_ge, (by norm_num : (4096 : ℝ) / 8193 < 4097)]
  have hright_pos :
      (0 : ℝ) < (((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193) := by
    have hk1 : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
    rw [hk1]
    nlinarith [hleft_pos]
  have hden_le :
      (k : ℝ) ^ 2 ≤
        ((k : ℝ) - (4096 : ℝ) / 8193) *
          ((((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)) := by
    have hk1 : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
    rw [hk1]
    nlinarith [hkR_ge]
  have hfrac :
      1 / (((k : ℝ) - (4096 : ℝ) / 8193) *
          ((((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193))) ≤
        1 / ((k : ℝ) ^ 2) := by
    exact one_div_le_one_div_of_le (pow_pos hkRpos 2) hden_le
  have htel :
      1 / ((k : ℝ) - (4096 : ℝ) / 8193) -
          1 / (((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193) =
        1 / (((k : ℝ) - (4096 : ℝ) / 8193) *
          ((((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193))) := by
    let a : ℝ := (k : ℝ) - (4096 : ℝ) / 8193
    let b : ℝ := (((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)
    have ha : a ≠ 0 := ne_of_gt (by simpa [a] using hleft_pos)
    have hb : b ≠ 0 := ne_of_gt (by simpa [b] using hright_pos)
    have hdiff : b - a = 1 := by simp [a, b]
    calc
      1 / ((k : ℝ) - (4096 : ℝ) / 8193) -
          1 / (((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193) =
        1 / a - 1 / b := by simp [a, b]
      _ = 1 / a * (b - a) * (1 / b) := by
        rw [one_div_mul_sub_mul_one_div_eq_one_div_add_one_div ha hb]
      _ = 1 / (a * b) := by
        rw [hdiff]
        field_simp [ha, hb]
      _ = 1 / (((k : ℝ) - (4096 : ℝ) / 8193) *
          ((((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193))) := by
        simp [a, b]
  calc
    1 / ((k : ℝ) - (4096 : ℝ) / 8193) -
        1 / (((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193) =
      1 / (((k : ℝ) - (4096 : ℝ) / 8193) *
          ((((k + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193))) := htel
    _ ≤ 1 / ((k : ℝ) ^ 2) := hfrac
    _ = inverseSquareTerm k := by rfl

/-- Shifted telescoping lower bound for a reverse exact prefix whose lowest
term index is at least `4097`. -/
theorem inverseSquareExactReverseAccumulatorFrom_ge_shifted_telescope_4096_8193
    {kTop n : ℕ} (hn : n ≤ kTop)
    (hlo : 4097 ≤ kTop - n + 1) :
    1 / (((kTop - n + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193) -
        1 / (((kTop + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193) ≤
      inverseSquareExactReverseAccumulatorFrom 0 kTop n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hn' : n ≤ kTop := by omega
      have hidx : 4097 ≤ kTop - n := by omega
      have hlo_tail : 4097 ≤ kTop - n + 1 := by omega
      have hstep :=
        inverseSquareTerm_ge_shifted_telescope_4096_8193
          (k := kTop - n) hidx
      calc
        1 / (((kTop - (n + 1) + 1 : ℕ) : ℝ) -
              (4096 : ℝ) / 8193) -
            1 / (((kTop + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193) =
          (1 / (((kTop - n : ℕ) : ℝ) - (4096 : ℝ) / 8193) -
              1 / (((kTop - n + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)) +
            (1 / (((kTop - n + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193) -
              1 / (((kTop + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)) := by
            have hsub : kTop - (n + 1) + 1 = kTop - n := by omega
            rw [hsub]
            ring
        _ ≤ inverseSquareTerm (kTop - n) +
              inverseSquareExactReverseAccumulatorFrom 0 kTop n := by
            exact add_le_add hstep (ih hn' hlo_tail)
        _ = inverseSquareExactReverseAccumulatorFrom 0 kTop (n + 1) := by
            rw [inverseSquareExactReverseAccumulatorFrom_succ]
            ring

/-- Sharp lower squeeze for the exact high-index prefix in the source's
`10^9` reverse summation. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193 :
    1 / ((4097 : ℝ) - (4096 : ℝ) / 8193) -
        1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)) ≤
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
  have hn : (10 ^ 9 - 4096 : ℕ) ≤ (10 ^ 9 : ℕ) := by norm_num
  have hlo : 4097 ≤ (10 ^ 9 : ℕ) - (10 ^ 9 - 4096 : ℕ) + 1 := by norm_num
  have htel :=
    inverseSquareExactReverseAccumulatorFrom_ge_shifted_telescope_4096_8193
      (kTop := 10 ^ 9) (n := 10 ^ 9 - 4096) hn hlo
  have hden : (10 ^ 9 - (10 ^ 9 - 4096) + 1 : ℕ) = 4097 := by norm_num
  rw [hden] at htel
  exact htel

/-- Half-shifted upper telescoping majorant for inverse-square terms. -/
theorem inverseSquareTerm_le_half_telescope {k : ℕ} (hk : 1 ≤ k) :
    inverseSquareTerm k ≤
      1 / ((k : ℝ) - (1 : ℝ) / 2) -
        1 / (((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) := by
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkR_ge : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hleft_pos : (0 : ℝ) < (k : ℝ) - (1 : ℝ) / 2 := by
    nlinarith [hkR_ge]
  have hright_pos : (0 : ℝ) < (((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) := by
    have hk1 : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
    rw [hk1]
    nlinarith [hleft_pos]
  have hden_le :
      ((k : ℝ) - (1 : ℝ) / 2) *
          ((((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2)) ≤
        (k : ℝ) ^ 2 := by
    have hk1 : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
    rw [hk1]
    nlinarith
  have hprod_pos :
      0 < ((k : ℝ) - (1 : ℝ) / 2) *
          ((((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2)) :=
    mul_pos hleft_pos hright_pos
  have hfrac :
      1 / ((k : ℝ) ^ 2) ≤
        1 / (((k : ℝ) - (1 : ℝ) / 2) *
          ((((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))) := by
    exact one_div_le_one_div_of_le hprod_pos hden_le
  have htel :
      1 / ((k : ℝ) - (1 : ℝ) / 2) -
          1 / (((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) =
        1 / (((k : ℝ) - (1 : ℝ) / 2) *
          ((((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))) := by
    let a : ℝ := (k : ℝ) - (1 : ℝ) / 2
    let b : ℝ := (((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2)
    have ha : a ≠ 0 := ne_of_gt (by simpa [a] using hleft_pos)
    have hb : b ≠ 0 := ne_of_gt (by simpa [b] using hright_pos)
    have hdiff : b - a = 1 := by simp [a, b]
    calc
      1 / ((k : ℝ) - (1 : ℝ) / 2) -
          1 / (((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) =
        1 / a - 1 / b := by simp [a, b]
      _ = 1 / a * (b - a) * (1 / b) := by
        rw [one_div_mul_sub_mul_one_div_eq_one_div_add_one_div ha hb]
      _ = 1 / (a * b) := by
        rw [hdiff]
        field_simp [ha, hb]
      _ = 1 / (((k : ℝ) - (1 : ℝ) / 2) *
          ((((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))) := by
        simp [a, b]
  calc
    inverseSquareTerm k = 1 / ((k : ℝ) ^ 2) := by rfl
    _ ≤ 1 / (((k : ℝ) - (1 : ℝ) / 2) *
          ((((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))) := hfrac
    _ = 1 / ((k : ℝ) - (1 : ℝ) / 2) -
        1 / (((k + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) := htel.symm

/-- Half-shifted telescoping upper bound for a reverse exact prefix. -/
theorem inverseSquareExactReverseAccumulatorFrom_le_half_telescope
    {kTop n : ℕ} (hn : n ≤ kTop) :
    inverseSquareExactReverseAccumulatorFrom 0 kTop n ≤
      1 / (((kTop - n + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) -
        1 / (((kTop + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hn' : n ≤ kTop := by omega
      have hidx : 1 ≤ kTop - n := by omega
      have hstep := inverseSquareTerm_le_half_telescope (k := kTop - n) hidx
      calc
        inverseSquareExactReverseAccumulatorFrom 0 kTop (n + 1) =
          inverseSquareTerm (kTop - n) +
            inverseSquareExactReverseAccumulatorFrom 0 kTop n := by
            rw [inverseSquareExactReverseAccumulatorFrom_succ]
            ring
        _ ≤ (1 / (((kTop - n : ℕ) : ℝ) - (1 : ℝ) / 2) -
              1 / (((kTop - n + 1 : ℕ) : ℝ) - (1 : ℝ) / 2)) +
            (1 / (((kTop - n + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) -
              1 / (((kTop + 1 : ℕ) : ℝ) - (1 : ℝ) / 2)) := by
            exact add_le_add hstep (ih hn')
        _ = 1 / (((kTop - (n + 1) + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) -
            1 / (((kTop + 1 : ℕ) : ℝ) - (1 : ℝ) / 2) := by
            have hsub : kTop - (n + 1) + 1 = kTop - n := by omega
            rw [hsub]
            ring

/-- Sharp upper squeeze for the exact high-index prefix in the source's
`10^9` reverse summation. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope :
    inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
      1 / ((4097 : ℝ) - (1 : ℝ) / 2) -
        1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (1 : ℝ) / 2)) := by
  have hn : (10 ^ 9 - 4096 : ℕ) ≤ (10 ^ 9 : ℕ) := by norm_num
  have htel :=
    inverseSquareExactReverseAccumulatorFrom_le_half_telescope
      (kTop := 10 ^ 9) (n := 10 ^ 9 - 4096) hn
  have hden : (10 ^ 9 - (10 ^ 9 - 4096) + 1 : ℕ) = 4097 := by norm_num
  rw [hden] at htel
  exact htel

/-- The exact real mass of the source's high-index reverse prefix is above
the lower endpoint of the final-suffix start window for the archived optional
repository model. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_ge_printedSuffixStartLower :
    inverseSquareSingleReverseSuffixStartLower ≤
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
  have hn : (10 ^ 9 - 4096 : ℕ) ≤ (10 ^ 9 : ℕ) := by norm_num
  have htel := inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ
    (kTop := 10 ^ 9) (n := 10 ^ 9 - 4096) hn
  have hden : (10 ^ 9 - (10 ^ 9 - 4096) + 1 : ℕ) = 4097 := by norm_num
  rw [hden] at htel
  have hwindow :
      inverseSquareSingleReverseSuffixStartLower ≤
        1 / (4097 : ℝ) - 1 / (((10 ^ 9 + 1 : ℕ) : ℝ)) := by
    norm_num [inverseSquareSingleReverseSuffixStartLower,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  exact le_trans hwindow htel

/-- The exact real mass of the source's high-index reverse prefix is below
the upper endpoint of the final-suffix start window for the archived optional
repository model. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpper :
    inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
      inverseSquareSingleReverseSuffixStartUpper := by
  have hwindow :
      1 / (4096 : ℝ) ≤ inverseSquareSingleReverseSuffixStartUpper := by
    norm_num [inverseSquareSingleReverseSuffixStartUpper,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  exact le_trans inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096 hwindow

/-- The exact real mass of the source's high-index reverse prefix is below the
tighter upper endpoint of the final-suffix start window. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpperTight :
    inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
      inverseSquareSingleReverseSuffixStartUpperTight := by
  have hwindow :
      1 / (4096 : ℝ) ≤ inverseSquareSingleReverseSuffixStartUpperTight := by
    norm_num [inverseSquareSingleReverseSuffixStartUpperTight,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  exact le_trans inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096 hwindow

/-- Exact high-prefix start-window squeeze for the archived optional
repository-model trace: the symbolic mass of the `10^9, ..., 4097` block lies
inside the binary32 start window whose final 4096-term suffix reaches the
displayed model accumulator.  The corresponding rounded high-prefix state is
only optional explicit-model replay work. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow :
    inverseSquareSingleReverseSuffixStartLower ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ∧
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        inverseSquareSingleReverseSuffixStartUpper :=
  ⟨inverseSquareExactReverseTenPowNineHighPrefix_ge_printedSuffixStartLower,
    inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpper⟩

/-- Exact high-prefix squeeze for the tighter final-suffix start window in the
archived optional repository model.  This is the non-enumerative interval target
that replaces the earlier, deliberately looser upper endpoint for a
whole-window suffix certificate. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow :
    inverseSquareSingleReverseSuffixStartLower ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ∧
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        inverseSquareSingleReverseSuffixStartUpperTight :=
  ⟨inverseSquareExactReverseTenPowNineHighPrefix_ge_printedSuffixStartLower,
    inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpperTight⟩

/-- Start-window squeeze restated through the exact decomposition of the full
`10^9` reverse sum into its high-index prefix plus the final `4096` terms. -/
theorem inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_mem_printedSuffixStartWindow :
    inverseSquareSingleReverseSuffixStartLower ≤
        inverseSquareExactReverseAccumulator (10 ^ 9) -
          inverseSquareExactReverseAccumulator 4096 ∧
      inverseSquareExactReverseAccumulator (10 ^ 9) -
          inverseSquareExactReverseAccumulator 4096 ≤
        inverseSquareSingleReverseSuffixStartUpper := by
  rw [inverseSquareExactReverseAccumulator_ten_pow_nine_eq_highPrefix_add_low4096]
  ring_nf
  exact inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow

/-- The rounded high-index prefix state in the source's reverse-order run,
before the final `4096` low-index additions are applied. -/
noncomputable def inverseSquareSingleReverseTenPowNineHighPrefixState : ℝ :=
  inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)

/-- Split the rounded high-index prefix into the earlier block
`10^9, ..., 8193` followed by the final high-prefix binade
`8192, ..., 4097`.  This is a structural D1 foothold, not a replay of the
closed low-index suffix. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixState_split_8192 :
    inverseSquareSingleReverseTenPowNineHighPrefixState =
      inverseSquareSingleReverseAccumulatorFrom
        (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192))
        8192 (8192 - 4096) := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixState
  rw [show (10 ^ 9 - 4096 : ℕ) =
    (10 ^ 9 - 8192) + (8192 - 4096) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  congr

/-- Lower endpoint of a concrete binary32 candidate window for the rounded
high-prefix state: 1024 ulps below the observed high-prefix candidate. -/
noncomputable def inverseSquareSingleReverseHighPrefixCandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16774836 - 1024) (-12 : ℤ)

/-- Upper endpoint of the concrete binary32 candidate window for the rounded
high-prefix state: 1024 ulps above the observed high-prefix candidate. -/
noncomputable def inverseSquareSingleReverseHighPrefixCandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16774836 + 1024) (-12 : ℤ)

/-- If `pred` and `target` are adjacent positive normalized values, no finite
value strictly below `target` can lie above `pred`.  This turns the normalized
adjacency fact into a finite-system exclusion lemma, covering zero and
subnormal values explicitly. -/
theorem FloatingPointFormat.finiteSystem_lt_right_adjacent_le_left
    {fmt : FloatingPointFormat} {z pred target : ℝ}
    (hz : fmt.finiteSystem z)
    (hpredSystem : fmt.normalizedSystem pred)
    (hadj : fmt.realOrderAdjacentNormalized pred target)
    (hpred_pos : 0 < pred)
    (hzlt : z < target) :
    z ≤ pred := by
  rcases hz with rfl | hznorm | hzsub
  · exact le_of_lt hpred_pos
  · by_cases hzle : z ≤ pred
    · exact hzle
    · have hpred_lt_z : pred < z := lt_of_not_ge hzle
      exfalso
      exact hadj.2.2.2 z
        (fmt.normalizedSystem_unboundedNormalizedSystem hznorm)
        (Or.inl ⟨hpred_lt_z, hzlt⟩)
  · have hsub_le_min := fmt.subnormalSystem_le_minNormalMagnitude hzsub
    have hmin_le_pred : fmt.minNormalMagnitude ≤ pred := by
      have hpred_abs :=
        fmt.normalizedSystem_abs_lower_bound hpredSystem
      simpa [abs_of_pos hpred_pos] using hpred_abs
    exact le_trans hsub_le_min hmin_le_pred

/-- If `target` and `succ` are adjacent positive normalized values, no finite
value strictly above `target` can lie below `succ`. -/
theorem FloatingPointFormat.right_adjacent_le_finiteSystem_of_left_lt
    {fmt : FloatingPointFormat} {z target succ : ℝ}
    (hz : fmt.finiteSystem z)
    (htargetSystem : fmt.normalizedSystem target)
    (hadj : fmt.realOrderAdjacentNormalized target succ)
    (htarget_pos : 0 < target)
    (hltz : target < z) :
    succ ≤ z := by
  rcases hz with rfl | hznorm | hzsub
  · exfalso
    linarith
  · by_cases hsuccle : succ ≤ z
    · exact hsuccle
    · have hz_lt_succ : z < succ := lt_of_not_ge hsuccle
      exfalso
      exact hadj.2.2.2 z
        (fmt.normalizedSystem_unboundedNormalizedSystem hznorm)
        (Or.inl ⟨hltz, hz_lt_succ⟩)
  · exfalso
    have hsub_le_min := fmt.subnormalSystem_le_minNormalMagnitude hzsub
    have hmin_le_target : fmt.minNormalMagnitude ≤ target := by
      have htarget_abs :=
        fmt.normalizedSystem_abs_lower_bound htargetSystem
      simpa [abs_of_pos htarget_pos] using htarget_abs
    linarith

/-- Nearest finite rounding cannot leave an interval whose endpoints are
finite representable values and which contains the exact input. -/
theorem FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hax : a ≤ x) (hxb : x ≤ b) :
    a ≤ y ∧ y ≤ b := by
  constructor
  · by_contra hnot
    have hya : y < a := lt_of_not_ge hnot
    have hyx : y ≤ x := le_trans (le_of_lt hya) hax
    have hnear := nearestRoundingIn_minimal hround ha
    rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr hax)] at hnear
    linarith
  · by_contra hnot
    have hby : b < y := lt_of_not_ge hnot
    have hxy : x ≤ y := le_trans hxb (le_of_lt hby)
    have hnear := nearestRoundingIn_minimal hround hb
    rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr hxb)] at hnear
    linarith

/-- Nearest finite rounding cannot round below a positive adjacent target once
the exact input is either already at/above the target, or lies to the right of
the predecessor-target midpoint. -/
theorem FloatingPointFormat.nearestRoundingToFinite_ge_of_adjacent_midpoint
    {fmt : FloatingPointFormat} {x y pred target : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (hpredSystem : fmt.normalizedSystem pred)
    (htargetSystem : fmt.normalizedSystem target)
    (hadj : fmt.realOrderAdjacentNormalized pred target)
    (hpred_pos : 0 < pred)
    (hxpred : pred < x)
    (hcase : target ≤ x ∨ |x - target| < |x - pred|) :
    target ≤ y := by
  by_contra hnot
  have hylt : y < target := lt_of_not_ge hnot
  have hyfin := nearestRoundingIn_mem hround
  have hyle :
      y ≤ pred :=
    fmt.finiteSystem_lt_right_adjacent_le_left
      hyfin hpredSystem hadj hpred_pos hylt
  have hnear :=
    nearestRoundingIn_minimal hround (Or.inr (Or.inl htargetSystem))
  rcases hcase with htarget_le_x | hcloser
  · have hxy_nonneg : 0 ≤ x - y := by linarith
    have hxt_nonneg : 0 ≤ x - target := by linarith
    rw [abs_of_nonneg hxy_nonneg, abs_of_nonneg hxt_nonneg] at hnear
    linarith
  · have hxp_nonneg : 0 ≤ x - pred := by linarith
    have hxy_nonneg : 0 ≤ x - y := by linarith
    have hxp_le_hxy : x - pred ≤ x - y := by linarith
    rw [abs_of_nonneg hxy_nonneg] at hnear
    rw [abs_of_nonneg hxp_nonneg] at hcloser
    linarith

/-- Upper-endpoint companion to
`nearestRoundingToFinite_ge_of_adjacent_midpoint`. -/
theorem FloatingPointFormat.nearestRoundingToFinite_le_of_adjacent_midpoint
    {fmt : FloatingPointFormat} {x y target succ : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (htargetSystem : fmt.normalizedSystem target)
    (hadj : fmt.realOrderAdjacentNormalized target succ)
    (htarget_pos : 0 < target)
    (hxsucc : x < succ)
    (hcase : x ≤ target ∨ |x - target| < |x - succ|) :
    y ≤ target := by
  by_contra hnot
  have hlty : target < y := lt_of_not_ge hnot
  have hyfin := nearestRoundingIn_mem hround
  have hsuccle :
      succ ≤ y :=
    fmt.right_adjacent_le_finiteSystem_of_left_lt
      hyfin htargetSystem hadj htarget_pos hlty
  have hnear :=
    nearestRoundingIn_minimal hround (Or.inr (Or.inl htargetSystem))
  rcases hcase with hx_le_target | hcloser
  · have hxy_nonpos : x - y ≤ 0 := by linarith
    have hxt_nonpos : x - target ≤ 0 := by linarith
    rw [abs_of_nonpos hxy_nonpos, abs_of_nonpos hxt_nonpos] at hnear
    linarith
  · have hsx_nonneg : 0 ≤ succ - x := by linarith
    have hxs_nonpos : x - succ ≤ 0 := by linarith
    have hxy_nonpos : x - y ≤ 0 := by linarith
    have hsx_le_hyx : succ - x ≤ y - x := by linarith
    rw [abs_of_nonpos hxy_nonpos] at hnear
    rw [abs_of_nonpos hxs_nonpos] at hcloser
    linarith

/-- If a point is to the right of another point that is already closer to the
right endpoint of an adjacent cell, then it remains closer to the right
endpoint until it reaches that endpoint. -/
theorem abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
    {left x0 x right : ℝ}
    (hleft_lt_x0 : left < x0)
    (hx0le : x0 ≤ x)
    (hx_lt_right : x < right)
    (hcloser0 : |x0 - right| < |x0 - left|) :
    |x - right| < |x - left| := by
  have hx0_right_nonpos : x0 - right ≤ 0 := by linarith
  have hx0_left_nonneg : 0 ≤ x0 - left := by linarith
  have hx_right_nonpos : x - right ≤ 0 := by linarith
  have hx_left_nonneg : 0 ≤ x - left := by linarith
  rw [abs_of_nonpos hx0_right_nonpos, abs_of_nonneg hx0_left_nonneg] at hcloser0
  rw [abs_of_nonpos hx_right_nonpos, abs_of_nonneg hx_left_nonneg]
  linarith

/-- Symmetric monotonicity for the left endpoint of an adjacent cell. -/
theorem abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
    {left x x0 right : ℝ}
    (hleft_lt_x : left < x)
    (hxle : x ≤ x0)
    (hx0_lt_right : x0 < right)
    (hcloser0 : |x0 - left| < |x0 - right|) :
    |x - left| < |x - right| := by
  have hx0_left_nonneg : 0 ≤ x0 - left := by linarith
  have hx0_right_nonpos : x0 - right ≤ 0 := by linarith
  have hx_left_nonneg : 0 ≤ x - left := by linarith
  have hx_right_nonpos : x - right ≤ 0 := by linarith
  rw [abs_of_nonneg hx0_left_nonneg, abs_of_nonpos hx0_right_nonpos] at hcloser0
  rw [abs_of_nonneg hx_left_nonneg, abs_of_nonpos hx_right_nonpos]
  linarith

/-- Exact companion to the rounded `8192` high-prefix split.  Archived optional
D1 interval certificates can compare rounded and exact states blockwise if an
explicit repository-model replay is reopened. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_split_8192 :
    inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) =
      inverseSquareExactReverseAccumulatorFrom
        (inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192))
        8192 (8192 - 4096) := by
  rw [show (10 ^ 9 - 4096 : ℕ) =
    (10 ^ 9 - 8192) + (8192 - 4096) by norm_num]
  rw [inverseSquareExactReverseAccumulatorFrom_add]
  congr

/-- Exact mass of the earlier high-prefix block `10^9, ..., 8193` is at most
`1/8192`.  This tightens the starting box for the final high-prefix binade. -/
theorem inverseSquareExactReverseTenPowNineHighPrefixBefore8192_le_inv_8192 :
    inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ≤
      1 / (8192 : ℝ) := by
  have hn : (10 ^ 9 - 8192 : ℕ) ≤ (10 ^ 9 : ℕ) - 1 := by norm_num
  have htel := inverseSquareExactReverseAccumulatorFrom_le_telescope
    (kTop := 10 ^ 9) (n := 10 ^ 9 - 8192) hn
  have hden : ((10 ^ 9 : ℕ) - (10 ^ 9 - 8192 : ℕ) : ℕ) = 8192 := by norm_num
  rw [hden] at htel
  have hnonneg : 0 ≤ 1 / ((10 ^ 9 : ℕ) : ℝ) := by norm_num
  nlinarith

/-- Coarse but block-local rounded bound before the final high-prefix binade:
after the `10^9, ..., 8193` block, the single-precision state is at most
`1/4096`.  The full high-prefix bound is only `1/2048`; this sharper split
bound is intended for the next `8192, ..., 4097` interval certificate. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixBefore8192_le_inv_4096 :
    inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ≤
      1 / (4096 : ℝ) := by
  have h :=
    (inverseSquareSingleReverseAccumulatorFrom_le_start_add_two_mul_exact_zero_start
      (start := 0)
      (FloatingPointFormat.finiteSystem_zero FloatingPointFormat.ieeeSingleFormat)
      (10 ^ 9) (10 ^ 9 - 8192))
  have hexact :=
    inverseSquareExactReverseTenPowNineHighPrefixBefore8192_le_inv_8192
  have hmul :
      2 * inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ≤
        2 * (1 / (8192 : ℝ)) :=
    mul_le_mul_of_nonneg_left hexact (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ≤
        0 + 2 * inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) :=
      h
    _ = 2 * inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) := by
      ring
    _ ≤ 2 * (1 / (8192 : ℝ)) := hmul
    _ = 1 / (4096 : ℝ) := by norm_num

/-- Exact mass of the final high-prefix binade `8192, ..., 4097` is at most
`1/8192`.  This is the block budget paired with the `8192` split. -/
theorem inverseSquareExactReverseBinade8192To4097_le_inv_8192 :
    inverseSquareExactReverseAccumulatorFrom 0 8192 (8192 - 4096) ≤
      1 / (8192 : ℝ) := by
  have hn : (8192 - 4096 : ℕ) ≤ (8192 : ℕ) - 1 := by norm_num
  have htel := inverseSquareExactReverseAccumulatorFrom_le_telescope
    (kTop := 8192) (n := 8192 - 4096) hn
  have hden : ((8192 : ℕ) - (8192 - 4096 : ℕ) : ℕ) = 4096 := by norm_num
  rw [hden] at htel
  have heq : 1 / (4096 : ℝ) - 1 / (8192 : ℝ) = 1 / (8192 : ℝ) := by
    norm_num
  linarith

/-- Whole-binade rounded increment bound for `8192, ..., 4097`: from any
finite binary32 start, this block increases the rounded accumulator by at most
`1/4096`. -/
theorem inverseSquareSingleReverseBinade8192To4097_le_start_add_inv_4096
    {start : ℝ}
    (hstart : FloatingPointFormat.ieeeSingleFormat.finiteSystem start) :
    inverseSquareSingleReverseAccumulatorFrom start 8192 (8192 - 4096) ≤
      start + 1 / (4096 : ℝ) := by
  have h :=
    (inverseSquareSingleReverseAccumulatorFrom_le_start_add_two_mul_exact_zero_start
      (start := start) hstart 8192 (8192 - 4096))
  have hexact := inverseSquareExactReverseBinade8192To4097_le_inv_8192
  have hmul :
      2 * inverseSquareExactReverseAccumulatorFrom 0 8192 (8192 - 4096) ≤
        2 * (1 / (8192 : ℝ)) :=
    mul_le_mul_of_nonneg_left hexact (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom start 8192 (8192 - 4096) ≤
        start + 2 * inverseSquareExactReverseAccumulatorFrom 0 8192 (8192 - 4096) :=
      h
    _ ≤ start + 2 * (1 / (8192 : ℝ)) := by linarith
    _ = start + 1 / (4096 : ℝ) := by norm_num

/-- Lower endpoint for the exact earlier-block start window feeding the
`8192, ..., 4097` high-prefix binade.  This window is chosen so a later
rounded-start certificate can compose with a compact final-binade window map. -/
noncomputable def inverseSquareSingleReverseHighPrefixBefore8192WindowLower :
    ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16773455 (-13 : ℤ)

/-- Upper endpoint for the exact earlier-block start window feeding the
`8192, ..., 4097` high-prefix binade.  The endpoint intentionally crosses the
binary32 exponent boundary, matching the first step of the final high-prefix
binade. -/
noncomputable def inverseSquareSingleReverseHighPrefixBefore8192WindowUpper :
    ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8388776 (-12 : ℤ)

/-- Exact earlier-block mass lies in the start window needed by the final
high-prefix binade route.  This is a non-enumerative telescope certificate for
the `10^9, ..., 8193` exact block, not a rounded-prefix proof. -/
theorem inverseSquareExactReverseTenPowNineHighPrefixBefore8192_mem_startWindow :
    inverseSquareSingleReverseHighPrefixBefore8192WindowLower ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ∧
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ≤
        inverseSquareSingleReverseHighPrefixBefore8192WindowUpper := by
  constructor
  · have hn : (10 ^ 9 - 8192 : ℕ) ≤ (10 ^ 9 : ℕ) := by norm_num
    have htel := inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ
      (kTop := 10 ^ 9) (n := 10 ^ 9 - 8192) hn
    have hden :
        ((10 ^ 9 : ℕ) - (10 ^ 9 - 8192 : ℕ) + 1 : ℕ) = 8193 := by
      norm_num
    rw [hden] at htel
    have hwindow :
        inverseSquareSingleReverseHighPrefixBefore8192WindowLower ≤
          1 / (8193 : ℝ) - 1 / (((10 ^ 9 : ℕ) + 1 : ℕ) : ℝ) := by
      norm_num [inverseSquareSingleReverseHighPrefixBefore8192WindowLower,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact le_trans hwindow htel
  · have hn : (10 ^ 9 - 8192 : ℕ) ≤ (10 ^ 9 : ℕ) - 1 := by norm_num
    have htel := inverseSquareExactReverseAccumulatorFrom_le_telescope
      (kTop := 10 ^ 9) (n := 10 ^ 9 - 8192) hn
    have hden :
        ((10 ^ 9 : ℕ) - (10 ^ 9 - 8192 : ℕ) : ℕ) = 8192 := by
      norm_num
    rw [hden] at htel
    have hwindow :
        1 / (8192 : ℝ) - 1 / ((10 ^ 9 : ℕ) : ℝ) ≤
          inverseSquareSingleReverseHighPrefixBefore8192WindowUpper := by
      norm_num [inverseSquareSingleReverseHighPrefixBefore8192WindowUpper,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact le_trans htel hwindow

/-- Scaled mantissa increment total for the same-exponent part of the final
high-prefix binade.  After the two boundary additions `8192^{-2}` and
`8191^{-2}`, the remaining terms `8190^{-2}, ..., 4097^{-2}` stay in binary32
exponent `-12` and use scale `q = 37`. -/
theorem inverseSquareSingleReverseHighBinade8190To4097Prefix_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 37 8190 4094 = 8385036 := by
  set_option maxRecDepth 300000 in
  decide

/-- Endpoint-safety certificate for the same-exponent part of the final
high-prefix binade.  This is the compact checked data needed to prove that the
post-boundary start window propagates through `8190^{-2}, ..., 4097^{-2}` into
the high-prefix candidate window. -/
def inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool :
    Bool :=
  (List.range 4094).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 37 8190 n
    let k := 8190 - n
    let d := inverseSquareSingleScaledMantissaIncrement 37 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 37 ∧
      2 ^ 37 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8388776 + p) + d - 1 ∧
      (8390824 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the same-exponent
`8190^{-2}, ..., 4097^{-2}` high-prefix binade tail. -/
theorem inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 140000 in
  decide

/-- Pointwise endpoint-safety extraction for the same-exponent
`8190^{-2}, ..., 4097^{-2}` high-prefix binade tail. -/
theorem inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificate
    {n : ℕ} (hn : n < 4094) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 37 8190 n
    let k := 8190 - n
    let d := inverseSquareSingleScaledMantissaIncrement 37 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 37 ∧
      2 ^ 37 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8388776 + p) + d - 1 ∧
      (8390824 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 4094,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 37 8190 x
        let k := 8190 - x
        let d := inverseSquareSingleScaledMantissaIncrement 37 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 37 ∧
          2 ^ 37 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8388776 + p) + d - 1 ∧
          (8390824 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool] using
      inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- Lower endpoint after the rounded `8192^{-2}` boundary addition in the
final high-prefix binade. -/
noncomputable def inverseSquareSingleReverseHighBinadeAfter8192WindowLower :
    ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16775503 (-13 : ℤ)

/-- Upper endpoint after the rounded `8192^{-2}` boundary addition in the
final high-prefix binade. -/
noncomputable def inverseSquareSingleReverseHighBinadeAfter8192WindowUpper :
    ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8389800 (-12 : ℤ)

/-- Exact addition by `8192^{-2}` maps the pre-binade start window exactly
onto the post-`8192` window. -/
theorem inverseSquareSingleReverseHighBinadeBefore8192Window_add_8192_term_mem_after8192Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseHighPrefixBefore8192WindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseHighPrefixBefore8192WindowUpper) :
    inverseSquareSingleReverseHighBinadeAfter8192WindowLower ≤
        s + inverseSquareTerm 8192 ∧
      s + inverseSquareTerm 8192 ≤
        inverseSquareSingleReverseHighBinadeAfter8192WindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseHighBinadeAfter8192WindowLower =
          inverseSquareSingleReverseHighPrefixBefore8192WindowLower +
            inverseSquareTerm 8192 := by
      norm_num [inverseSquareSingleReverseHighBinadeAfter8192WindowLower,
        inverseSquareSingleReverseHighPrefixBefore8192WindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    rw [hwindow]
    linarith
  · have hwindow :
        inverseSquareSingleReverseHighPrefixBefore8192WindowUpper +
            inverseSquareTerm 8192 =
          inverseSquareSingleReverseHighBinadeAfter8192WindowUpper := by
      norm_num [inverseSquareSingleReverseHighPrefixBefore8192WindowUpper,
        inverseSquareSingleReverseHighBinadeAfter8192WindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    rw [← hwindow]
    linarith

/-- Rounded addition by `8192^{-2}` maps the pre-binade start window into the
post-`8192` window. -/
theorem inverseSquareSingleReverseHighBinadeBefore8192Window_round_8192_step_mem_after8192Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseHighPrefixBefore8192WindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseHighPrefixBefore8192WindowUpper) :
    inverseSquareSingleReverseHighBinadeAfter8192WindowLower ≤
        inverseSquareSingleForwardStep s 8192 ∧
      inverseSquareSingleForwardStep s 8192 ≤
        inverseSquareSingleReverseHighBinadeAfter8192WindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseHighBinadeBefore8192Window_add_8192_term_mem_after8192Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem
        inverseSquareSingleReverseHighBinadeAfter8192WindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 16775503, (-13 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem
        inverseSquareSingleReverseHighBinadeAfter8192WindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8389800, (-12 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 8192)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 8192)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 8192)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Lower endpoint after the rounded `8191^{-2}` boundary addition.  From this
point through `4097^{-2}` the final high-prefix binade stays in one binary32
exponent. -/
noncomputable def inverseSquareSingleReverseHighBinadeAfter8191WindowLower :
    ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8388776 (-12 : ℤ)

/-- Upper endpoint after the rounded `8191^{-2}` boundary addition. -/
noncomputable def inverseSquareSingleReverseHighBinadeAfter8191WindowUpper :
    ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8390824 (-12 : ℤ)

/-- Rounded addition by `8191^{-2}` maps the post-`8192` window into the
same-exponent tail window. -/
theorem inverseSquareSingleReverseHighBinadeAfter8192Window_round_8191_step_mem_after8191Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseHighBinadeAfter8192WindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseHighBinadeAfter8192WindowUpper) :
    inverseSquareSingleReverseHighBinadeAfter8191WindowLower ≤
        inverseSquareSingleForwardStep s 8191 ∧
      inverseSquareSingleForwardStep s 8191 ≤
        inverseSquareSingleReverseHighBinadeAfter8191WindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let predL : ℝ := fmt.normalizedValue false 8388775 (-12 : ℤ)
  let targetL : ℝ := inverseSquareSingleReverseHighBinadeAfter8191WindowLower
  let targetU : ℝ := inverseSquareSingleReverseHighBinadeAfter8191WindowUpper
  let succU : ℝ := fmt.normalizedValue false 8390825 (-12 : ℤ)
  let x : ℝ := s + inverseSquareTerm 8191
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredMant : fmt.normalizedMantissa 8388775 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have htargetLMant : fmt.normalizedMantissa 8388776 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have htargetUMant : fmt.normalizedMantissa 8390824 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hsuccMant : fmt.normalizedMantissa 8390825 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hexp : fmt.exponentInRange (-12 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hpredSystem : fmt.normalizedSystem predL :=
    ⟨false, 8388775, (-12 : ℤ), hpredMant, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL := by
    exact ⟨false, 8388776, (-12 : ℤ), htargetLMant, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU := by
    exact ⟨false, 8390824, (-12 : ℤ), htargetUMant, hexp, rfl⟩
  have hpred_pos : 0 < predL := by
    simpa [predL, fmt] using
      fmt.normalizedValue_false_pos
        (m := 8388775) (e := (-12 : ℤ)) hpredMant
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, inverseSquareSingleReverseHighBinadeAfter8191WindowUpper,
      fmt] using
      fmt.normalizedValue_false_pos
        (m := 8390824) (e := (-12 : ℤ)) htargetUMant
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 8388775, (-12 : ℤ), hpredMant, htargetLMant,
      Or.inl ⟨rfl, ?_⟩⟩
    simp [targetL, inverseSquareSingleReverseHighBinadeAfter8191WindowLower,
      fmt]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, 8390824, (-12 : ℤ), htargetUMant, hsuccMant,
      Or.inl ⟨rfl, rfl⟩⟩
  have hpred_lt_base :
      predL <
        inverseSquareSingleReverseHighBinadeAfter8192WindowLower +
          inverseSquareTerm 8191 := by
    norm_num [predL, inverseSquareSingleReverseHighBinadeAfter8192WindowLower,
      inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hbaseL_le_x :
      inverseSquareSingleReverseHighBinadeAfter8192WindowLower +
          inverseSquareTerm 8191 ≤ x := by
    simp [x]
    linarith
  have hbaseL_closer :
      |(inverseSquareSingleReverseHighBinadeAfter8192WindowLower +
            inverseSquareTerm 8191) - targetL| <
        |(inverseSquareSingleReverseHighBinadeAfter8192WindowLower +
            inverseSquareTerm 8191) - predL| := by
    norm_num [targetL, predL,
      inverseSquareSingleReverseHighBinadeAfter8191WindowLower,
      inverseSquareSingleReverseHighBinadeAfter8192WindowLower,
      inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseHighBinadeAfter8192WindowUpper +
          inverseSquareTerm 8191 := by
    simp [x]
    linarith
  have hbaseU_lt_succ :
      inverseSquareSingleReverseHighBinadeAfter8192WindowUpper +
          inverseSquareTerm 8191 < succU := by
    norm_num [succU, inverseSquareSingleReverseHighBinadeAfter8192WindowUpper,
      inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hbaseU_closer :
      |(inverseSquareSingleReverseHighBinadeAfter8192WindowUpper +
            inverseSquareTerm 8191) - targetU| <
        |(inverseSquareSingleReverseHighBinadeAfter8192WindowUpper +
            inverseSquareTerm 8191) - succU| := by
    norm_num [targetU, succU,
      inverseSquareSingleReverseHighBinadeAfter8191WindowUpper,
      inverseSquareSingleReverseHighBinadeAfter8192WindowUpper,
      inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpred_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpred_lt_base hbaseL_le_x hxlt hbaseL_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredSystem htargetLSystem hadjL hpred_pos hxpred hcase
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      targetL, x, fmt] using hge
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hbaseU_lt_succ
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hbaseU_lt_succ hbaseU_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      targetU, x, fmt] using hle

/-- Lower endpoint after `n` additions inside the same-exponent
`8190^{-2}, ..., 4097^{-2}` high-prefix tail. -/
noncomputable def inverseSquareSingleReverseHighBinadeTailWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8388776 + inverseSquareSingleReverseScaledMantissaPrefix 37 8190 n)
    (-12 : ℤ)

/-- Upper endpoint after `n` additions inside the same-exponent
`8190^{-2}, ..., 4097^{-2}` high-prefix tail. -/
noncomputable def inverseSquareSingleReverseHighBinadeTailWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8390824 + inverseSquareSingleReverseScaledMantissaPrefix 37 8190 n)
    (-12 : ℤ)

theorem inverseSquareSingleReverseHighBinadeTailWindowLower_zero :
    inverseSquareSingleReverseHighBinadeTailWindowLower 0 =
      inverseSquareSingleReverseHighBinadeAfter8191WindowLower := by
  norm_num [inverseSquareSingleReverseHighBinadeTailWindowLower,
    inverseSquareSingleReverseHighBinadeAfter8191WindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseHighBinadeTailWindowUpper_zero :
    inverseSquareSingleReverseHighBinadeTailWindowUpper 0 =
      inverseSquareSingleReverseHighBinadeAfter8191WindowUpper := by
  norm_num [inverseSquareSingleReverseHighBinadeTailWindowUpper,
    inverseSquareSingleReverseHighBinadeAfter8191WindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseHighBinadeTailWindowLower_final :
    inverseSquareSingleReverseHighBinadeTailWindowLower 4094 =
      inverseSquareSingleReverseHighPrefixCandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8388776 +
          inverseSquareSingleReverseScaledMantissaPrefix 37 8190 4094)
        (-12 : ℤ) =
      inverseSquareSingleReverseHighPrefixCandidateWindowLower
  rw [inverseSquareSingleReverseHighBinade8190To4097Prefix_eq]
  norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseHighBinadeTailWindowUpper_final :
    inverseSquareSingleReverseHighBinadeTailWindowUpper 4094 =
      inverseSquareSingleReverseHighPrefixCandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8390824 +
          inverseSquareSingleReverseScaledMantissaPrefix 37 8190 4094)
        (-12 : ℤ) =
      inverseSquareSingleReverseHighPrefixCandidateWindowUpper
  rw [inverseSquareSingleReverseHighBinade8190To4097Prefix_eq]
  norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- One arbitrary-start step of the final same-exponent high-prefix tail. -/
theorem inverseSquareSingleReverseHighBinadeTailWindow_round_step_mem
    {n : ℕ} (hn : n < 4094) {start : ℝ}
    (hlo : inverseSquareSingleReverseHighBinadeTailWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseHighBinadeTailWindowUpper n) :
    inverseSquareSingleReverseHighBinadeTailWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (8190 - n) ∧
      inverseSquareSingleForwardStep start (8190 - n) ≤
        inverseSquareSingleReverseHighBinadeTailWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 37 8190 n
  let k := 8190 - n
  let d := inverseSquareSingleScaledMantissaIncrement 37 k
  let mL := 8388776 + p
  let mU := 8390824 + p
  let e : ℤ := -12
  have hcert :=
    inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificate
      hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseHighBinadeTailWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseHighBinadeTailWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 37)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseHighBinadeTailWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseHighBinadeTailWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseHighBinadeTailWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 37)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseHighBinadeTailWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseHighBinadeTailWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseHighBinadeTailWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseHighBinadeTailWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseHighBinadeTailWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 37)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseHighBinadeTailWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8388776 +
              (inverseSquareSingleReverseScaledMantissaPrefix 37 8190 n +
                inverseSquareSingleScaledMantissaIncrement 37 (8190 - n)))
            (-12 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8388776 +
              (inverseSquareSingleReverseScaledMantissaPrefix 37 8190 n +
                inverseSquareSingleScaledMantissaIncrement 37 (8190 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseHighBinadeTailWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseHighBinadeTailWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseHighBinadeTailWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseHighBinadeTailWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseHighBinadeTailWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 37)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseHighBinadeTailWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8390824 +
              (inverseSquareSingleReverseScaledMantissaPrefix 37 8190 n +
                inverseSquareSingleScaledMantissaIncrement 37 (8190 - n)))
            (-12 : ℤ) := by
      have hnat :
          mU + d =
            8390824 +
              (inverseSquareSingleReverseScaledMantissaPrefix 37 8190 n +
                inverseSquareSingleScaledMantissaIncrement 37 (8190 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseHighBinadeTailWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the same-exponent `8190^{-2}, ..., 4097^{-2}` tail:
any start in the post-`8191` window remains in the corresponding tail prefix
window. -/
theorem inverseSquareSingleReverseHighBinadeTailWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseHighBinadeAfter8191WindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseHighBinadeAfter8191WindowUpper)
    (n : ℕ) (hn : n ≤ 4094) :
    inverseSquareSingleReverseHighBinadeTailWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 8190 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 8190 n ≤
        inverseSquareSingleReverseHighBinadeTailWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseHighBinadeTailWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseHighBinadeTailWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 4094 := by omega
      have hnlt : n < 4094 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseHighBinadeTailWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window certificate for the same-exponent
`8190^{-2}, ..., 4097^{-2}` tail. -/
def inverseSquareSingleReverseHighBinade8190To4097Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseHighBinadeAfter8191WindowLower ≤ start →
      start ≤ inverseSquareSingleReverseHighBinadeAfter8191WindowUpper →
        inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 8190 4094 ∧
          inverseSquareSingleReverseAccumulatorFrom start 8190 4094 ≤
            inverseSquareSingleReverseHighPrefixCandidateWindowUpper

/-- Closed whole-window certificate for the same-exponent
`8190^{-2}, ..., 4097^{-2}` tail. -/
theorem inverseSquareSingleReverseHighBinade8190To4097Window_closed :
    inverseSquareSingleReverseHighBinade8190To4097Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseHighBinadeTailWindow_prefix_mem
      (start := start) hlo hhi 4094 (by norm_num)
  rw [← inverseSquareSingleReverseHighBinadeTailWindowLower_final,
    ← inverseSquareSingleReverseHighBinadeTailWindowUpper_final]
  exact hprefix

/-- Whole-window map for the final high-prefix binade
`8192^{-2}, ..., 4097^{-2}`: any start in the certified pre-binade window
lands in the high-prefix candidate window after the two boundary additions and
the same-exponent tail. -/
def inverseSquareSingleReverseHighBinade8192To4097WindowMapsToCandidate : Prop :=
  ∀ start,
    inverseSquareSingleReverseHighPrefixBefore8192WindowLower ≤ start →
      start ≤ inverseSquareSingleReverseHighPrefixBefore8192WindowUpper →
        inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 8192 (8192 - 4096) ∧
          inverseSquareSingleReverseAccumulatorFrom start 8192 (8192 - 4096) ≤
            inverseSquareSingleReverseHighPrefixCandidateWindowUpper

/-- Closed whole-window map for the final high-prefix binade
`8192^{-2}, ..., 4097^{-2}`. -/
theorem inverseSquareSingleReverseHighBinade8192To4097WindowMapsToCandidate_closed :
    inverseSquareSingleReverseHighBinade8192To4097WindowMapsToCandidate := by
  intro start hlo hhi
  have hafter8192 :
      inverseSquareSingleReverseHighBinadeAfter8192WindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 8192 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 8192 1 ≤
          inverseSquareSingleReverseHighBinadeAfter8192WindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseHighBinadeBefore8192Window_round_8192_step_mem_after8192Window
        hlo hhi
  have hafter8191 :
      inverseSquareSingleReverseHighBinadeAfter8191WindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 8192 2 ∧
        inverseSquareSingleReverseAccumulatorFrom start 8192 2 ≤
          inverseSquareSingleReverseHighBinadeAfter8191WindowUpper := by
    have hstep :=
      inverseSquareSingleReverseHighBinadeAfter8192Window_round_8191_step_mem_after8191Window
        (s := inverseSquareSingleReverseAccumulatorFrom start 8192 1)
        hafter8192.1 hafter8192.2
    simpa [inverseSquareSingleReverseAccumulatorFrom] using hstep
  have htail :=
    inverseSquareSingleReverseHighBinade8190To4097Window_closed
      (inverseSquareSingleReverseAccumulatorFrom start 8192 2)
      hafter8191.1 hafter8191.2
  rw [show (8192 - 4096 : ℕ) = 2 + 4094 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show (8192 - 2 : ℕ) = 8190 by norm_num]
  exact htail

/-- The rounded high-index prefix state is an IEEE-single finite-system value.
This does not yet locate the state in the candidate window, but it supplies the
finite-format premise needed by later nearest-cell/window certificates. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixState_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      inverseSquareSingleReverseTenPowNineHighPrefixState := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixState
  exact inverseSquareSingleReverseAccumulatorFrom_finiteSystem_of_start
    (FloatingPointFormat.finiteSystem_zero FloatingPointFormat.ieeeSingleFormat)
    (10 ^ 9) (10 ^ 9 - 4096)

/-- The actual rounded high-index prefix state in the archived repository-model
reverse-order run is nonnegative.  This is a reusable invariant for the
optional D1 high-prefix interval route, not an active Chapter 1 gate target. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixState_nonneg :
    0 ≤ inverseSquareSingleReverseTenPowNineHighPrefixState := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixState
  exact inverseSquareSingleReverseAccumulatorFrom_nonneg_of_start_nonneg
    (FloatingPointFormat.finiteSystem_zero FloatingPointFormat.ieeeSingleFormat)
    (by norm_num) (10 ^ 9) (10 ^ 9 - 4096)

/-- Every earlier rounded prefix state is bounded by the rounded high-prefix
state reached after all terms above `4096` have been consumed. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixState_prefix_le_highPrefix
    {j : ℕ} (hj : j ≤ 10 ^ 9 - 4096) :
    inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j ≤
      inverseSquareSingleReverseTenPowNineHighPrefixState := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixState
  exact inverseSquareSingleReverseAccumulatorFrom_le_of_le_steps
    (FloatingPointFormat.finiteSystem_zero FloatingPointFormat.ieeeSingleFormat)
    hj

/-- Crude high-prefix upper envelope obtained from the one-step nearestness
comparison with the previous finite accumulator.  It is intentionally stated as
a reusable error-recurrence foothold, not as the final candidate-window bound. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixState_le_two_mul_exact :
    inverseSquareSingleReverseTenPowNineHighPrefixState ≤
      2 * inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixState
  have h :=
    (inverseSquareSingleReverseAccumulatorFrom_le_start_add_two_mul_exact_zero_start
      (start := 0)
      (FloatingPointFormat.finiteSystem_zero FloatingPointFormat.ieeeSingleFormat)
      (10 ^ 9) (10 ^ 9 - 4096))
  calc
    inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        0 + 2 * inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) :=
      h
    _ = 2 * inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
      ring

/-- Concrete coarse upper bound for the actual rounded high-prefix state.  The
candidate-window target is much sharper, but this bound records that the rounded
high-prefix trace remains in a small positive interval without expanding the
`10^9 - 4096` operations. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixState_le_inv_2048 :
    inverseSquareSingleReverseTenPowNineHighPrefixState ≤ 1 / (2048 : ℝ) := by
  have hstate :=
    inverseSquareSingleReverseTenPowNineHighPrefixState_le_two_mul_exact
  have hexact :=
    inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096
  have hmul :
      2 * inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        2 * (1 / (4096 : ℝ)) :=
    mul_le_mul_of_nonneg_left hexact (by norm_num)
  calc
    inverseSquareSingleReverseTenPowNineHighPrefixState ≤
        2 * inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) :=
      hstate
    _ ≤ 2 * (1 / (4096 : ℝ)) := hmul
    _ = 1 / (2048 : ℝ) := by norm_num

/-- Every exact input to a high-prefix rounded addition in the source's
`10^9` reverse-order run lies in binary32's finite normal range.  This is a
single quantified adapter over the whole high-index prefix, not an expansion
into individual trace cases. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixStep_exactInput_finiteNormalRange
    {j : ℕ} (hj : j < 10 ^ 9 - 4096) :
    FloatingPointFormat.ieeeSingleFormat.finiteNormalRange
      (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
        inverseSquareTerm ((10 ^ 9 : ℕ) - j)) := by
  have hjle : j ≤ 10 ^ 9 - 4096 := le_of_lt hj
  have hkge : 4097 ≤ (10 ^ 9 : ℕ) - j :=
    inverseSquareReverseTenPowNineHighPrefix_index_ge_4097 (j := j) hj
  have hkpos : 0 < (10 ^ 9 : ℕ) - j := by omega
  have hkle : (10 ^ 9 : ℕ) - j ≤ 10 ^ 9 := by omega
  have hs_nonneg :
      0 ≤ inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j := by
    exact inverseSquareSingleReverseAccumulatorFrom_nonneg_of_start_nonneg
      (FloatingPointFormat.finiteSystem_zero FloatingPointFormat.ieeeSingleFormat)
      (by norm_num) (10 ^ 9) j
  have hmin_le_t :
      FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤
        inverseSquareTerm ((10 ^ 9 : ℕ) - j) := by
    exact inverseSquareTerm_ge_ieeeSingle_minNormal_of_pos_le_ten_pow_nine
      hkpos hkle
  have ht_nonneg : 0 ≤ inverseSquareTerm ((10 ^ 9 : ℕ) - j) :=
    le_trans (le_of_lt FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude_pos)
      hmin_le_t
  have hx_nonneg :
      0 ≤ inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
        inverseSquareTerm ((10 ^ 9 : ℕ) - j) :=
    add_nonneg hs_nonneg ht_nonneg
  have hmin_le_x :
      FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤
        inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
          inverseSquareTerm ((10 ^ 9 : ℕ) - j) := by
    linarith
  have hs_le_prefix :
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j ≤
        inverseSquareSingleReverseTenPowNineHighPrefixState := by
    exact inverseSquareSingleReverseTenPowNineHighPrefixState_prefix_le_highPrefix
      hjle
  have hs_le_small :
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j ≤
        1 / (2048 : ℝ) :=
    le_trans hs_le_prefix
      inverseSquareSingleReverseTenPowNineHighPrefixState_le_inv_2048
  have ht_le_small :
      inverseSquareTerm ((10 ^ 9 : ℕ) - j) ≤ 1 / (2 : ℝ) ^ 24 := by
    exact inverseSquareTerm_le_two_pow_neg_24_of_reverse_ten_pow_nine_high_prefix
      (j := j) hj
  have hx_le_small :
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
          inverseSquareTerm ((10 ^ 9 : ℕ) - j) ≤
        1 / (2048 : ℝ) + 1 / (2 : ℝ) ^ 24 := by
    linarith
  have hsmall_le_one :
      1 / (2048 : ℝ) + 1 / (2 : ℝ) ^ 24 ≤ 1 := by
    norm_num
  have hone_le_max :
      (1 : ℝ) ≤ FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude := by
    norm_num [FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR,
      zpow_neg]
    change (1 : ℝ) ≤
      (340282346638528859811704183484516925440 : ℝ)
    norm_num
  have hsmall_le_max :
      1 / (2048 : ℝ) + 1 / (2 : ℝ) ^ 24 ≤
        FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude :=
    le_trans hsmall_le_one hone_le_max
  have hx_le_max :
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
          inverseSquareTerm ((10 ^ 9 : ℕ) - j) ≤
        FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude :=
    le_trans hx_le_small hsmall_le_max
  rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hx_nonneg]
  exact ⟨hmin_le_x, hx_le_max⟩

/-- Standard relative-error model for every rounded addition in the high-index
prefix of Higham §1.12.3's reverse-order `10^9`-term run. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixStep_standardModel_lt
    {j : ℕ} (hj : j < 10 ^ 9 - 4096) :
    ∃ δ : ℝ,
      |δ| < FloatingPointFormat.ieeeSingleFormat.unitRoundoff ∧
        inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (j + 1) =
          (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
            inverseSquareTerm ((10 ^ 9 : ℕ) - j)) * (1 + δ) := by
  have hrange :
      FloatingPointFormat.ieeeSingleFormat.finiteNormalRange
        (BasicOp.exact BasicOp.add
          (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j)
          (inverseSquareTerm ((10 ^ 9 : ℕ) - j))) := by
    simpa [BasicOp.exact] using
      inverseSquareSingleReverseTenPowNineHighPrefixStep_exactInput_finiteNormalRange
        (j := j) hj
  rcases
      (FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
        (fmt := FloatingPointFormat.ieeeSingleFormat) (op := BasicOp.add)
        (x := inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j)
        (y := inverseSquareTerm ((10 ^ 9 : ℕ) - j)) hrange) with
    ⟨δ, hδ, hmodel⟩
  refine ⟨δ, hδ, ?_⟩
  simpa [inverseSquareSingleForwardStep, BasicOp.exact] using hmodel

/-- Absolute-error form of the standard model for every high-prefix rounded
addition.  This is the source-shaped local recurrence error used by later
whole-prefix interval bounds. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_exactInput
    {j : ℕ} (hj : j < 10 ^ 9 - 4096) :
    |inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (j + 1) -
        (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
          inverseSquareTerm ((10 ^ 9 : ℕ) - j))| <
      FloatingPointFormat.ieeeSingleFormat.unitRoundoff *
        (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
          inverseSquareTerm ((10 ^ 9 : ℕ) - j)) := by
  let x : ℝ :=
    inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
      inverseSquareTerm ((10 ^ 9 : ℕ) - j)
  rcases
      inverseSquareSingleReverseTenPowNineHighPrefixStep_standardModel_lt
        (j := j) hj with
    ⟨δ, hδ, hmodel⟩
  have hmodelx :
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (j + 1) =
        x * (1 + δ) := by
    simpa [x] using hmodel
  have hxrange :
      FloatingPointFormat.ieeeSingleFormat.finiteNormalRange x := by
    simpa [x] using
      inverseSquareSingleReverseTenPowNineHighPrefixStep_exactInput_finiteNormalRange
        (j := j) hj
  have hs_nonneg :
      0 ≤ inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j := by
    exact inverseSquareSingleReverseAccumulatorFrom_nonneg_of_start_nonneg
      (FloatingPointFormat.finiteSystem_zero FloatingPointFormat.ieeeSingleFormat)
      (by norm_num) (10 ^ 9) j
  have ht_nonneg :
      0 ≤ inverseSquareTerm ((10 ^ 9 : ℕ) - j) :=
    inverseSquareTerm_nonneg ((10 ^ 9 : ℕ) - j)
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact add_nonneg hs_nonneg ht_nonneg
  have hx_abs_pos : 0 < |x| :=
    lt_of_lt_of_le FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude_pos
      hxrange.1
  have hx_ne : x ≠ 0 := abs_pos.mp hx_abs_pos
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
  have hdiff : x * (1 + δ) - x = x * δ := by ring
  change
    |inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (j + 1) - x| <
      FloatingPointFormat.ieeeSingleFormat.unitRoundoff * x
  rw [hmodelx, hdiff, abs_mul, abs_of_pos hx_pos]
  have hmul :=
    mul_lt_mul_of_pos_left hδ hx_pos
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Coarse uniform version of the high-prefix local standard-model error:
every rounded high-prefix addition has absolute error below `u` times the
same explicit positive envelope.  This is deliberately a whole-prefix bound,
not a per-index certificate list. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_coarse
    {j : ℕ} (hj : j < 10 ^ 9 - 4096) :
    |inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (j + 1) -
        (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
          inverseSquareTerm ((10 ^ 9 : ℕ) - j))| <
      FloatingPointFormat.ieeeSingleFormat.unitRoundoff *
        (1 / (2048 : ℝ) + 1 / (2 : ℝ) ^ 24) := by
  have hjle : j ≤ 10 ^ 9 - 4096 := le_of_lt hj
  have hs_le_prefix :
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j ≤
        inverseSquareSingleReverseTenPowNineHighPrefixState :=
    inverseSquareSingleReverseTenPowNineHighPrefixState_prefix_le_highPrefix
      hjle
  have hs_le_small :
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j ≤
        1 / (2048 : ℝ) :=
    le_trans hs_le_prefix
      inverseSquareSingleReverseTenPowNineHighPrefixState_le_inv_2048
  have ht_le_small :
      inverseSquareTerm ((10 ^ 9 : ℕ) - j) ≤ 1 / (2 : ℝ) ^ 24 :=
    inverseSquareTerm_le_two_pow_neg_24_of_reverse_ten_pow_nine_high_prefix
      (j := j) hj
  have hx_le_small :
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
          inverseSquareTerm ((10 ^ 9 : ℕ) - j) ≤
        1 / (2048 : ℝ) + 1 / (2 : ℝ) ^ 24 := by
    linarith
  have herr :=
    inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_exactInput
      (j := j) hj
  exact lt_of_lt_of_le herr
    (mul_le_mul_of_nonneg_left hx_le_small
      (le_of_lt FloatingPointFormat.ieeeSingleFormat.unitRoundoff_pos))

/-- The local high-prefix standard-model absolute-error envelope at step `j`.
It is intentionally source-shaped: the factor multiplies the exact input to
the rounded addition at that step. -/
noncomputable def inverseSquareSingleReverseTenPowNineHighPrefixStepStdError
    (j : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.unitRoundoff *
    (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j +
      inverseSquareTerm ((10 ^ 9 : ℕ) - j))

/-- Recursive accumulated local-error envelope for the rounded high-prefix
trace.  This is the block-level object produced by composing the per-step
standard-model bounds, without expanding the prefix into individual cases. -/
noncomputable def inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope :
    ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope n +
        inverseSquareSingleReverseTenPowNineHighPrefixStepStdError n

/-- Each local high-prefix standard-model error envelope is nonnegative. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixStepStdError_nonneg
    (j : ℕ) :
    0 ≤ inverseSquareSingleReverseTenPowNineHighPrefixStepStdError j := by
  have hs_nonneg :
      0 ≤ inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) j := by
    exact inverseSquareSingleReverseAccumulatorFrom_nonneg_of_start_nonneg
      (FloatingPointFormat.finiteSystem_zero FloatingPointFormat.ieeeSingleFormat)
      (by norm_num) (10 ^ 9) j
  have ht_nonneg :
      0 ≤ inverseSquareTerm ((10 ^ 9 : ℕ) - j) :=
    inverseSquareTerm_nonneg ((10 ^ 9 : ℕ) - j)
  unfold inverseSquareSingleReverseTenPowNineHighPrefixStepStdError
  exact mul_nonneg
    (le_of_lt FloatingPointFormat.ieeeSingleFormat.unitRoundoff_pos)
    (add_nonneg hs_nonneg ht_nonneg)

/-- The accumulated high-prefix standard-model error envelope is nonnegative. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope_nonneg
    (n : ℕ) :
    0 ≤ inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope n := by
  induction n with
  | zero =>
      simp [inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope]
  | succ n ih =>
      simp [inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope]
      exact add_nonneg ih
        (inverseSquareSingleReverseTenPowNineHighPrefixStepStdError_nonneg n)

/-- Accumulated high-prefix error recurrence: for every prefix length up to the
source split point, the rounded prefix differs from the exact prefix by at most
the recursive sum of the local standard-model envelopes. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefix_abs_error_le_stdErrorEnvelope
    {n : ℕ} (hn : n ≤ 10 ^ 9 - 4096) :
    |inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) n -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) n| ≤
      inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope n := by
  induction n with
  | zero =>
      simp [inverseSquareSingleReverseAccumulatorFrom,
        inverseSquareExactReverseAccumulatorFrom,
        inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope]
  | succ n ih =>
      have hnle : n ≤ 10 ^ 9 - 4096 := by omega
      have hnlt : n < 10 ^ 9 - 4096 := by omega
      have hlocal_lt :=
        inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_exactInput
          (j := n) hnlt
      have hlocal :
          |inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (n + 1) -
              (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) n +
                inverseSquareTerm ((10 ^ 9 : ℕ) - n))| ≤
            inverseSquareSingleReverseTenPowNineHighPrefixStepStdError n := by
        exact le_of_lt (by
          simpa [inverseSquareSingleReverseTenPowNineHighPrefixStepStdError]
            using hlocal_lt)
      have hprev := ih hnle
      have hrewrite :
          inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (n + 1) -
              inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (n + 1) =
            (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (n + 1) -
              (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) n +
                inverseSquareTerm ((10 ^ 9 : ℕ) - n))) +
              (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) n -
                inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) n) := by
        rw [inverseSquareExactReverseAccumulatorFrom_succ]
        ring
      calc
        |inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (n + 1) -
            inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (n + 1)| =
            |(inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (n + 1) -
              (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) n +
                inverseSquareTerm ((10 ^ 9 : ℕ) - n))) +
              (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) n -
                inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) n)| := by
              rw [hrewrite]
        _ ≤
            |inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (n + 1) -
              (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) n +
                inverseSquareTerm ((10 ^ 9 : ℕ) - n))| +
              |inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) n -
                inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) n| :=
              abs_add_le _ _
        _ ≤
            inverseSquareSingleReverseTenPowNineHighPrefixStepStdError n +
              inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope n := by
              exact add_le_add hlocal hprev
        _ =
            inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope (n + 1) := by
              simp [inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope,
                add_comm]

/-- Final high-prefix specialization of the accumulated standard-model error
envelope.  This is an archived optional D1 bridge: if the repository-model
replay is explicitly reopened, comparing this envelope with the candidate-window
margin is one possible high-prefix route. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixState_abs_error_le_stdErrorEnvelope :
    |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
      inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope
        (10 ^ 9 - 4096) := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixState
  exact inverseSquareSingleReverseTenPowNineHighPrefix_abs_error_le_stdErrorEnvelope
    (n := 10 ^ 9 - 4096) (by rfl)

/-- Concrete binary32 candidate for the rounded high-index prefix state in
Higham §1.12.3's reverse-order `10^9`-term run.  Its usual hexadecimal IEEE
encoding is `0x397ff6b4`. -/
noncomputable def inverseSquareSingleReverseTenPowNineHighPrefixCandidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16774836 (-12 : ℤ)

/-- The binary32 state obtained from the concrete high-prefix candidate after
the first low-index reverse suffix addition, namely the exact `4096^{-2}`
term.  Its usual hexadecimal IEEE encoding is `0x3980035a`. -/
noncomputable def inverseSquareSingleReverseAfter4096Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8389466 (-11 : ℤ)

/-- The binary32 state obtained from the concrete high-prefix candidate after
the first two low-index reverse suffix additions, `4096^{-2}` and `4095^{-2}`.
Its usual hexadecimal IEEE encoding is `0x39800b5b`. -/
noncomputable def inverseSquareSingleReverseAfter4095Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8391515 (-11 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`4094^{-2}, ..., 2049^{-2}` has been applied to the after-`4095` state, just
before the boundary addition `2048^{-2}`.  Its usual hexadecimal IEEE encoding
is `0x39ffef4f`. -/
noncomputable def inverseSquareSingleReverseBefore2048Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16772943 (-11 : ℤ)

/-- The binary32 state obtained after the `2048^{-2}` boundary step from
`inverseSquareSingleReverseBefore2048Candidate`.  Its usual hexadecimal IEEE
encoding is `0x3a0007a8`. -/
noncomputable def inverseSquareSingleReverseAfter2048Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8390568 (-10 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`2047^{-2}, ..., 1025^{-2}` has been applied to the after-`2048` state, just
before the boundary addition `1024^{-2}`.  Its usual hexadecimal IEEE encoding
is `0x3a7fdfb6`. -/
noncomputable def inverseSquareSingleReverseBefore1024Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16768950 (-10 : ℤ)

/-- The binary32 state obtained after the exact `1024^{-2}` boundary step from
`inverseSquareSingleReverseBefore1024Candidate`.  Its usual hexadecimal IEEE
encoding is `0x3a800fdb`. -/
noncomputable def inverseSquareSingleReverseAfter1024Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8392667 (-9 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`1023^{-2}, ..., 513^{-2}` has been applied to the after-`1024` state, just
before the boundary addition `512^{-2}`.  Its usual hexadecimal IEEE encoding
is `0x3affbfeb`. -/
noncomputable def inverseSquareSingleReverseBefore512Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16760811 (-9 : ℤ)

/-- The binary32 state obtained after the `512^{-2}` boundary step from
`inverseSquareSingleReverseBefore512Candidate`.  Its usual hexadecimal IEEE
encoding is `0x3b001ff6`. -/
noncomputable def inverseSquareSingleReverseAfter512Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8396790 (-8 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`511^{-2}, ..., 257^{-2}` has been applied to the after-`512` state, just
before the boundary addition `256^{-2}`.  Its usual hexadecimal IEEE encoding
is `0x3b7f801f`. -/
noncomputable def inverseSquareSingleReverseBefore256Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16744479 (-8 : ℤ)

/-- The binary32 state obtained after the `256^{-2}` boundary step from
`inverseSquareSingleReverseBefore256Candidate`.  Its usual hexadecimal IEEE
encoding is `0x3b804010`. -/
noncomputable def inverseSquareSingleReverseAfter256Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8405008 (-7 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`255^{-2}, ..., 129^{-2}` has been applied to the after-`256` state, just
before the boundary addition `128^{-2}`.  Its usual hexadecimal IEEE encoding
is `0x3bff00a3`. -/
noncomputable def inverseSquareSingleReverseBefore128Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16711843 (-7 : ℤ)

/-- The binary32 state obtained after the `128^{-2}` boundary step from
`inverseSquareSingleReverseBefore128Candidate`.  Its usual hexadecimal IEEE
encoding is `0x3c008052`. -/
noncomputable def inverseSquareSingleReverseAfter128Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8421458 (-6 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`127^{-2}, ..., 65^{-2}` has been applied to the after-`128` state, just
before the boundary addition `64^{-2}`.  Its usual hexadecimal IEEE encoding
is `0x3c7e02a3`. -/
noncomputable def inverseSquareSingleReverseBefore64Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16646819 (-6 : ℤ)

/-- The binary32 state obtained after the `64^{-2}` boundary step from
`inverseSquareSingleReverseBefore64Candidate`.  Its usual hexadecimal IEEE
encoding is `0x3c810152`. -/
noncomputable def inverseSquareSingleReverseAfter64Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8454482 (-5 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`63^{-2}, ..., 33^{-2}` has been applied to the after-`64` state, just before
the boundary addition `32^{-2}`.  Its usual hexadecimal IEEE encoding is
`0x3cfc0aa4`. -/
noncomputable def inverseSquareSingleReverseBefore32Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16517796 (-5 : ℤ)

/-- The binary32 state obtained after the exact `32^{-2}` boundary step from
`inverseSquareSingleReverseBefore32Candidate`.  Its usual hexadecimal IEEE
encoding is `0x3d020552`. -/
noncomputable def inverseSquareSingleReverseAfter32Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8521042 (-4 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`31^{-2}, ..., 17^{-2}` has been applied to the after-`32` state, just before
the boundary addition `16^{-2}`.  Its usual hexadecimal IEEE encoding is
`0x3d782a9f`. -/
noncomputable def inverseSquareSingleReverseBefore16Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16263839 (-4 : ℤ)

/-- The binary32 state obtained after the `16^{-2}` boundary step from
`inverseSquareSingleReverseBefore16Candidate`.  Its usual hexadecimal IEEE
encoding is `0x3d841550`. -/
noncomputable def inverseSquareSingleReverseAfter16Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8656208 (-3 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`15^{-2}, ..., 9^{-2}` has been applied to the after-`16` state, just before
the boundary addition `8^{-2}`.  Its usual hexadecimal IEEE encoding is
`0x3df0aa22`. -/
noncomputable def inverseSquareSingleReverseBefore8Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 15772194 (-3 : ℤ)

/-- The binary32 state obtained after the exact `8^{-2}` boundary step from
`inverseSquareSingleReverseBefore8Candidate`.  Its usual hexadecimal IEEE
encoding is `0x3e085511`. -/
noncomputable def inverseSquareSingleReverseAfter8Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8934673 (-2 : ℤ)

/-- The binary32 state obtained after the same-exponent reverse suffix band
`7^{-2}, 6^{-2}, 5^{-2}` has been applied to the after-`8` state, just before
the final four additions.  Its usual hexadecimal IEEE encoding is `0x3e62a27c`. -/
noncomputable def inverseSquareSingleReverseBefore4Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 14852732 (-2 : ℤ)

/-- The binary32 state obtained after adding `4^{-2}` to the before-`4` state.
Its usual hexadecimal IEEE encoding is `0x3e91513e`. -/
noncomputable def inverseSquareSingleReverseAfter4Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 9523518 (-1 : ℤ)

/-- The binary32 state obtained after adding `3^{-2}` to the after-`4` state.
Its usual hexadecimal IEEE encoding is `0x3eca34cc`. -/
noncomputable def inverseSquareSingleReverseAfter3Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13251788 (-1 : ℤ)

/-- The binary32 state obtained after adding `2^{-2}` to the after-`3` state.
Its usual hexadecimal IEEE encoding is `0x3f251a66`. -/
noncomputable def inverseSquareSingleReverseAfter2Candidate : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 10820198 (0 : ℤ)

/-- The concrete high-prefix candidate lies in the repository-model
suffix-start window that leads to the displayed reverse accumulator. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartWindow :
    inverseSquareSingleReverseSuffixStartLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate ∧
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
        inverseSquareSingleReverseSuffixStartUpper := by
  constructor
  · norm_num [inverseSquareSingleReverseSuffixStartLower,
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  · norm_num [inverseSquareSingleReverseSuffixStartUpper,
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- The concrete high-prefix candidate lies in the tighter suffix-start window
used by the archived optional repository-model final suffix. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartTightWindow :
    inverseSquareSingleReverseSuffixStartLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate ∧
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
        inverseSquareSingleReverseSuffixStartUpperTight := by
  constructor
  · exact inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartWindow.1
  · norm_num [inverseSquareSingleReverseSuffixStartUpperTight,
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- The first concrete reverse-suffix step from the high-prefix candidate is
exactly representable: adding `4096^{-2}` to the candidate lands on the named
binary32 state `0x3980035a`. -/
theorem inverseSquareSingleReverseCandidate_add_4096_term_rounds_to_after4096 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate 4096 =
      inverseSquareSingleReverseAfter4096Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfinite :
      fmt.finiteSystem
        (inverseSquareSingleReverseTenPowNineHighPrefixCandidate +
          inverseSquareTerm 4096) := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8389466, (-11 : ℤ), ?hm, ?he, ?hval⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    · norm_num [inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
  calc
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate 4096 =
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate +
        inverseSquareTerm 4096 := by
        simpa [inverseSquareSingleForwardStep, fmt, BasicOp.exact] using
          (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add)
            (x := inverseSquareSingleReverseTenPowNineHighPrefixCandidate)
            (y := inverseSquareTerm 4096)
            hfinite)
    _ = inverseSquareSingleReverseAfter4096Candidate := by
      norm_num [inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
        inverseSquareSingleReverseAfter4096Candidate, inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]

/-- The second concrete reverse-suffix step from the high-prefix candidate:
adding `4095^{-2}` to the named after-`4096` state rounds to the named
binary32 state `0x39800b5b`. -/
theorem inverseSquareSingleReverseAfter4096_add_4095_term_rounds_to_after4095 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseAfter4096Candidate 4095 =
      inverseSquareSingleReverseAfter4095Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hmpred : fmt.normalizedMantissa (8389466 + 2049 - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmtarget : fmt.normalizedMantissa (8389466 + 2049) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmsucc : fmt.normalizedMantissa (8389466 + 2049 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hexp : fmt.exponentInRange ((25 : ℤ) - (36 : ℤ)) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hstep :
      inverseSquareSingleForwardStep
          (fmt.normalizedValue false 8389466 ((25 : ℤ) - (36 : ℤ))) 4095 =
        fmt.normalizedValue false (8389466 + 2049) ((25 : ℤ) - (36 : ℤ)) :=
    inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale
      (m := 8389466) (d := 2049) (k := 4095) (q := 36)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hmpred hmtarget hmsucc hexp
  simpa [inverseSquareSingleReverseAfter4096Candidate,
    inverseSquareSingleReverseAfter4095Candidate, fmt] using hstep

/-- Kernel-checked mantissa prefix sum for the first after-`4095` reverse
suffix band, namely the same-exponent additions `4094^{-2}, ..., 2049^{-2}`. -/
theorem inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046 = 8381428 := by
  set_option maxRecDepth 40000 in
  decide

/-- Boolean certificate for the first after-`4095` same-exponent reverse
suffix band.  Each entry verifies the integer half-cell inequalities and the
normal mantissa range for the next rounded state. -/
def inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool : Bool :=
  (List.range 2046).all (fun n =>
    let m := 8391515 + inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
    let k := 4094 - n
    let d := inverseSquareSingleScaledMantissaIncrement 36 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 36 ∧
      2 ^ 36 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the first after-`4095` same-exponent
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool_eq_true :
    inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool = true := by
  set_option maxRecDepth 60000 in
  decide

/-- Pointwise extraction of the first after-`4095` same-exponent reverse suffix
band certificate. -/
theorem inverseSquareSingleReverseAfter4095Band4094To2049Certificate
    {n : ℕ} (hn : n < 2046) :
    let m := 8391515 + inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
    let k := 4094 - n
    let d := inverseSquareSingleScaledMantissaIncrement 36 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 36 ∧
      2 ^ 36 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 2046,
        let m := 8391515 + inverseSquareSingleReverseScaledMantissaPrefix 36 4094 x
        let k := 4094 - x
        let d := inverseSquareSingleScaledMantissaIncrement 36 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 36 ∧
          2 ^ 36 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool] using
      inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool_eq_true
  simpa using hall n hn

/-- The first after-`4095` reverse suffix band is proved by a compact
mantissa-prefix certificate: after any certified number of additions from
`4094` downwards, the accumulator is the corresponding binary32 mantissa in
the exponent `-11` band. -/
theorem inverseSquareSingleReverseAfter4095Accumulator_4094_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 2046) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter4095Candidate 4094 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8391515 + inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n)
        (-11 : ℤ) := by
  induction n with
  | zero =>
      simp [inverseSquareSingleReverseAfter4095Candidate]
  | succ n ih =>
      have hnle : n ≤ 2046 := by omega
      have hnlt : n < 2046 := by omega
      have hcert :=
        inverseSquareSingleReverseAfter4095Band4094To2049Certificate hnlt
      let m := 8391515 + inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
      let k := 4094 - n
      let d := inverseSquareSingleScaledMantissaIncrement 36 k
      rcases hcert with
        ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
      have hmin' : 8388608 ≤ m + d - 1 := by
        simpa [m, d, k] using hmin
      have hmax' : m + d + 1 < 16777216 := by
        simpa [m, d, k] using hmax
      have hmpred :
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d - 1) := by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa,
          FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
        omega
      have hmtarget :
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d) := by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa,
          FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
        omega
      have hmsucc :
          FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d + 1) := by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa,
          FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
        omega
      have hexp :
          FloatingPointFormat.ieeeSingleFormat.exponentInRange
            ((25 : ℤ) - (36 : ℤ)) := by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.exponentInRange]
      have hstep :
          inverseSquareSingleForwardStep
              (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
                ((25 : ℤ) - (36 : ℤ))) k =
            FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
              ((25 : ℤ) - (36 : ℤ)) :=
        inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale
          (m := m) (d := d) (k := k) (q := 36)
          hdpos hkpos hleft hright hmpred hmtarget hmsucc hexp
      calc
        inverseSquareSingleReverseAccumulatorFrom
            inverseSquareSingleReverseAfter4095Candidate 4094 (n + 1) =
          inverseSquareSingleForwardStep
            (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m
              ((25 : ℤ) - (36 : ℤ))) k := by
            simp [inverseSquareSingleReverseAccumulatorFrom, ih hnle, m, k]
        _ =
          FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d)
            ((25 : ℤ) - (36 : ℤ)) := hstep
        _ =
          FloatingPointFormat.ieeeSingleFormat.normalizedValue false
            (8391515 +
              inverseSquareSingleReverseScaledMantissaPrefix 36 4094 (n + 1))
            (-11 : ℤ) := by
            simp [m, d, k, inverseSquareSingleReverseScaledMantissaPrefix,
              add_assoc]

/-- Result of the first same-exponent after-`4095` suffix band.  The state just
before the `2048^{-2}` boundary step is the named mantissa `16772943` in the
same exponent band. -/
theorem inverseSquareSingleReverseAfter4095Accumulator_4094_to_before2048 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter4095Candidate 4094 2046 =
      inverseSquareSingleReverseBefore2048Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter4095Accumulator_4094_bandPrefix_of_le
      2046 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter4095Candidate 4094 2046 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8391515 + inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046)
        (-11 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore2048Candidate := by
        rw [inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq]
        rfl

/-- Boundary step after the first same-exponent reverse suffix band: adding
`2048^{-2}` to `inverseSquareSingleReverseBefore2048Candidate` is an exact
midpoint between two exponent-`-10` binary32 values, and nearest/even selects
the even right endpoint `0x3a0007a8`. -/
theorem inverseSquareSingleReverseBefore2048_add_2048_term_rounds_to_after2048 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore2048Candidate 2048 =
      inverseSquareSingleReverseAfter2048Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let x : ℝ := inverseSquareSingleReverseBefore2048Candidate + inverseSquareTerm 2048
  let a : ℝ := fmt.normalizedValue false 8390567 (-10 : ℤ)
  let b : ℝ := inverseSquareSingleReverseAfter2048Candidate
  have hmleft : fmt.normalizedMantissa 8390567 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmright : fmt.normalizedMantissa (8390567 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 8390567, (-10 : ℤ), hmleft, hmright, Or.inl ⟨rfl, ?_⟩⟩
    simp [b, inverseSquareSingleReverseAfter2048Candidate, fmt]
  have hstrict : a < x ∧ x < b := by
    constructor <;> norm_num [x, a, b,
      inverseSquareSingleReverseBefore2048Candidate,
      inverseSquareSingleReverseAfter2048Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, inverseSquareSingleReverseBefore2048Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, zpow_neg]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, inverseSquareSingleReverseBefore2048Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, FloatingPointFormat.minNormalMagnitude,
        zpow_neg]
    · calc
        x = (16781135 : ℝ) / 34359738368 := by
          norm_num [x, inverseSquareSingleReverseBefore2048Candidate,
            inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
            FloatingPointFormat.betaR, zpow_neg]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 8390567 (-10 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    norm_num [x, a, b, inverseSquareSingleReverseBefore2048Candidate,
      inverseSquareSingleReverseAfter2048Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hodd : ¬ FloatingPointFormat.evenMantissa 8390567 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hmleft hleft htie hodd
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, x, b, inverseSquareSingleReverseAfter2048Candidate, fmt] using
    hround

/-- Kernel-checked mantissa prefix sum for the second reverse suffix
same-exponent band, namely the additions `2047^{-2}, ..., 1025^{-2}`. -/
theorem inverseSquareSingleReverseAfter2048Prefix_2047_to_1025_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 35 2047 1023 = 8378382 := by
  set_option maxRecDepth 30000 in
  decide

/-- Boolean certificate for the second reverse same-exponent band.  Each entry
verifies the integer half-cell inequalities and the normal mantissa range for
the next rounded state. -/
def inverseSquareSingleReverseAfter2048Band2047To1025CertificateBool : Bool :=
  (List.range 1023).all (fun n =>
    let m := 8390568 + inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n
    let k := 2047 - n
    let d := inverseSquareSingleScaledMantissaIncrement 35 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 35 ∧
      2 ^ 35 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the second reverse same-exponent band. -/
theorem inverseSquareSingleReverseAfter2048Band2047To1025CertificateBool_eq_true :
    inverseSquareSingleReverseAfter2048Band2047To1025CertificateBool = true := by
  set_option maxRecDepth 40000 in
  decide

/-- Pointwise extraction of the second reverse same-exponent band certificate. -/
theorem inverseSquareSingleReverseAfter2048Band2047To1025Certificate
    {n : ℕ} (hn : n < 1023) :
    let m := 8390568 + inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n
    let k := 2047 - n
    let d := inverseSquareSingleScaledMantissaIncrement 35 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 35 ∧
      2 ^ 35 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 1023,
        let m := 8390568 + inverseSquareSingleReverseScaledMantissaPrefix 35 2047 x
        let k := 2047 - x
        let d := inverseSquareSingleScaledMantissaIncrement 35 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 35 ∧
          2 ^ 35 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter2048Band2047To1025CertificateBool] using
      inverseSquareSingleReverseAfter2048Band2047To1025CertificateBool_eq_true
  simpa using hall n hn

/-- The second reverse suffix band is proved by the reusable same-exponent band
certificate theorem. -/
theorem inverseSquareSingleReverseAfter2048Accumulator_2047_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 1023) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter2048Candidate 2047 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8390568 + inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n)
        (-10 : ℤ) := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (35 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8390568) (q := 35) (kTop := 2047) (count := 1023)
      hexp
      (fun {n} hn =>
        inverseSquareSingleReverseAfter2048Band2047To1025Certificate hn)
      n hn
  simpa [inverseSquareSingleReverseAfter2048Candidate] using hband

/-- Result of the second same-exponent reverse suffix band.  The state just
before the `1024^{-2}` boundary step is the named mantissa `16768950` in the
exponent `-10` band. -/
theorem inverseSquareSingleReverseAfter2048Accumulator_2047_to_before1024 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter2048Candidate 2047 1023 =
      inverseSquareSingleReverseBefore1024Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter2048Accumulator_2047_bandPrefix_of_le
      1023 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter2048Candidate 2047 1023 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8390568 + inverseSquareSingleReverseScaledMantissaPrefix 35 2047 1023)
        (-10 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore1024Candidate := by
        rw [inverseSquareSingleReverseAfter2048Prefix_2047_to_1025_eq]
        rfl

/-- Boundary step after the second same-exponent reverse suffix band: adding
`1024^{-2}` to `inverseSquareSingleReverseBefore1024Candidate` is exactly
representable as the exponent-`-9` binary32 state `0x3a800fdb`. -/
theorem inverseSquareSingleReverseBefore1024_add_1024_term_rounds_to_after1024 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore1024Candidate 1024 =
      inverseSquareSingleReverseAfter1024Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfinite :
      fmt.finiteSystem
        (inverseSquareSingleReverseBefore1024Candidate +
          inverseSquareTerm 1024) := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8392667, (-9 : ℤ), ?hm, ?he, ?hval⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    · norm_num [inverseSquareSingleReverseBefore1024Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
  calc
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore1024Candidate 1024 =
      inverseSquareSingleReverseBefore1024Candidate +
        inverseSquareTerm 1024 := by
        simpa [inverseSquareSingleForwardStep, fmt, BasicOp.exact] using
          (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add)
            (x := inverseSquareSingleReverseBefore1024Candidate)
            (y := inverseSquareTerm 1024)
            hfinite)
    _ = inverseSquareSingleReverseAfter1024Candidate := by
      norm_num [inverseSquareSingleReverseBefore1024Candidate,
        inverseSquareSingleReverseAfter1024Candidate, inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]

/-- Kernel-checked mantissa prefix sum for the third reverse suffix
same-exponent band, namely the additions `1023^{-2}, ..., 513^{-2}`. -/
theorem inverseSquareSingleReverseAfter1024Prefix_1023_to_513_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 34 1023 511 = 8368144 := by
  set_option maxRecDepth 30000 in
  decide

/-- Boolean certificate for the third reverse same-exponent band.  Each entry
verifies the integer half-cell inequalities and the normal mantissa range for
the next rounded state. -/
def inverseSquareSingleReverseAfter1024Band1023To513CertificateBool : Bool :=
  (List.range 511).all (fun n =>
    let m := 8392667 + inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n
    let k := 1023 - n
    let d := inverseSquareSingleScaledMantissaIncrement 34 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 34 ∧
      2 ^ 34 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the third reverse same-exponent band. -/
theorem inverseSquareSingleReverseAfter1024Band1023To513CertificateBool_eq_true :
    inverseSquareSingleReverseAfter1024Band1023To513CertificateBool = true := by
  set_option maxRecDepth 30000 in
  decide

/-- Pointwise extraction of the third reverse same-exponent band certificate. -/
theorem inverseSquareSingleReverseAfter1024Band1023To513Certificate
    {n : ℕ} (hn : n < 511) :
    let m := 8392667 + inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n
    let k := 1023 - n
    let d := inverseSquareSingleScaledMantissaIncrement 34 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 34 ∧
      2 ^ 34 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 511,
        let m := 8392667 + inverseSquareSingleReverseScaledMantissaPrefix 34 1023 x
        let k := 1023 - x
        let d := inverseSquareSingleScaledMantissaIncrement 34 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 34 ∧
          2 ^ 34 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter1024Band1023To513CertificateBool] using
      inverseSquareSingleReverseAfter1024Band1023To513CertificateBool_eq_true
  simpa using hall n hn

/-- The third reverse suffix band is proved by the reusable same-exponent band
certificate theorem. -/
theorem inverseSquareSingleReverseAfter1024Accumulator_1023_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 511) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter1024Candidate 1023 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8392667 + inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n)
        (-9 : ℤ) := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (34 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8392667) (q := 34) (kTop := 1023) (count := 511)
      hexp
      (fun {n} hn =>
        inverseSquareSingleReverseAfter1024Band1023To513Certificate hn)
      n hn
  simpa [inverseSquareSingleReverseAfter1024Candidate] using hband

/-- Result of the third same-exponent reverse suffix band.  The state just
before the `512^{-2}` boundary step is the named mantissa `16760811` in the
exponent `-9` band. -/
theorem inverseSquareSingleReverseAfter1024Accumulator_1023_to_before512 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter1024Candidate 1023 511 =
      inverseSquareSingleReverseBefore512Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter1024Accumulator_1023_bandPrefix_of_le
      511 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter1024Candidate 1023 511 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8392667 + inverseSquareSingleReverseScaledMantissaPrefix 34 1023 511)
        (-9 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore512Candidate := by
        rw [inverseSquareSingleReverseAfter1024Prefix_1023_to_513_eq]
        rfl

/-- Boundary step after the third same-exponent reverse suffix band: adding
`512^{-2}` to `inverseSquareSingleReverseBefore512Candidate` is an exact
midpoint between two exponent-`-8` binary32 values, and nearest/even selects
the even right endpoint `0x3b001ff6`. -/
theorem inverseSquareSingleReverseBefore512_add_512_term_rounds_to_after512 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore512Candidate 512 =
      inverseSquareSingleReverseAfter512Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let x : ℝ := inverseSquareSingleReverseBefore512Candidate + inverseSquareTerm 512
  let a : ℝ := fmt.normalizedValue false 8396789 (-8 : ℤ)
  let b : ℝ := inverseSquareSingleReverseAfter512Candidate
  have hmleft : fmt.normalizedMantissa 8396789 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmright : fmt.normalizedMantissa (8396789 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 8396789, (-8 : ℤ), hmleft, hmright, Or.inl ⟨rfl, ?_⟩⟩
    simp [b, inverseSquareSingleReverseAfter512Candidate, fmt]
  have hstrict : a < x ∧ x < b := by
    constructor <;> norm_num [x, a, b,
      inverseSquareSingleReverseBefore512Candidate,
      inverseSquareSingleReverseAfter512Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, inverseSquareSingleReverseBefore512Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, zpow_neg]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, inverseSquareSingleReverseBefore512Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, FloatingPointFormat.minNormalMagnitude,
        zpow_neg]
    · calc
        x = (16793579 : ℝ) / 8589934592 := by
          norm_num [x, inverseSquareSingleReverseBefore512Candidate,
            inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
            FloatingPointFormat.betaR, zpow_neg]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 8396789 (-8 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    norm_num [x, a, b, inverseSquareSingleReverseBefore512Candidate,
      inverseSquareSingleReverseAfter512Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hodd : ¬ FloatingPointFormat.evenMantissa 8396789 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hmleft hleft htie hodd
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, x, b, inverseSquareSingleReverseAfter512Candidate, fmt] using
    hround

/-- Kernel-checked mantissa prefix sum for the fourth reverse suffix
same-exponent band, namely the additions `511^{-2}, ..., 257^{-2}`. -/
theorem inverseSquareSingleReverseAfter512Prefix_511_to_257_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 33 511 255 = 8347689 := by
  set_option maxRecDepth 20000 in
  decide

/-- Boolean certificate for the fourth reverse same-exponent band.  Each entry
verifies the integer half-cell inequalities and the normal mantissa range for
the next rounded state. -/
def inverseSquareSingleReverseAfter512Band511To257CertificateBool : Bool :=
  (List.range 255).all (fun n =>
    let m := 8396790 + inverseSquareSingleReverseScaledMantissaPrefix 33 511 n
    let k := 511 - n
    let d := inverseSquareSingleScaledMantissaIncrement 33 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 33 ∧
      2 ^ 33 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the fourth reverse same-exponent band. -/
theorem inverseSquareSingleReverseAfter512Band511To257CertificateBool_eq_true :
    inverseSquareSingleReverseAfter512Band511To257CertificateBool = true := by
  set_option maxRecDepth 20000 in
  decide

/-- Pointwise extraction of the fourth reverse same-exponent band certificate. -/
theorem inverseSquareSingleReverseAfter512Band511To257Certificate
    {n : ℕ} (hn : n < 255) :
    let m := 8396790 + inverseSquareSingleReverseScaledMantissaPrefix 33 511 n
    let k := 511 - n
    let d := inverseSquareSingleScaledMantissaIncrement 33 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 33 ∧
      2 ^ 33 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 255,
        let m := 8396790 + inverseSquareSingleReverseScaledMantissaPrefix 33 511 x
        let k := 511 - x
        let d := inverseSquareSingleScaledMantissaIncrement 33 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 33 ∧
          2 ^ 33 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter512Band511To257CertificateBool] using
      inverseSquareSingleReverseAfter512Band511To257CertificateBool_eq_true
  simpa using hall n hn

/-- The fourth reverse suffix band is proved by the reusable same-exponent
band certificate theorem. -/
theorem inverseSquareSingleReverseAfter512Accumulator_511_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 255) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter512Candidate 511 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8396790 + inverseSquareSingleReverseScaledMantissaPrefix 33 511 n)
        (-8 : ℤ) := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (33 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8396790) (q := 33) (kTop := 511) (count := 255)
      hexp
      (fun {n} hn =>
        inverseSquareSingleReverseAfter512Band511To257Certificate hn)
      n hn
  simpa [inverseSquareSingleReverseAfter512Candidate] using hband

/-- Result of the fourth same-exponent reverse suffix band.  The state just
before the `256^{-2}` boundary step is the named mantissa `16744479` in the
exponent `-8` band. -/
theorem inverseSquareSingleReverseAfter512Accumulator_511_to_before256 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter512Candidate 511 255 =
      inverseSquareSingleReverseBefore256Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter512Accumulator_511_bandPrefix_of_le
      255 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter512Candidate 511 255 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8396790 + inverseSquareSingleReverseScaledMantissaPrefix 33 511 255)
        (-8 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore256Candidate := by
        rw [inverseSquareSingleReverseAfter512Prefix_511_to_257_eq]
        rfl

/-- Boundary step after the fourth same-exponent reverse suffix band: adding
`256^{-2}` to `inverseSquareSingleReverseBefore256Candidate` is an exact
midpoint between two exponent-`-7` binary32 values, and nearest/even selects
the even right endpoint `0x3b804010`. -/
theorem inverseSquareSingleReverseBefore256_add_256_term_rounds_to_after256 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore256Candidate 256 =
      inverseSquareSingleReverseAfter256Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let x : ℝ := inverseSquareSingleReverseBefore256Candidate + inverseSquareTerm 256
  let a : ℝ := fmt.normalizedValue false 8405007 (-7 : ℤ)
  let b : ℝ := inverseSquareSingleReverseAfter256Candidate
  have hmleft : fmt.normalizedMantissa 8405007 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmright : fmt.normalizedMantissa (8405007 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 8405007, (-7 : ℤ), hmleft, hmright, Or.inl ⟨rfl, ?_⟩⟩
    simp [b, inverseSquareSingleReverseAfter256Candidate, fmt]
  have hstrict : a < x ∧ x < b := by
    constructor <;> norm_num [x, a, b,
      inverseSquareSingleReverseBefore256Candidate,
      inverseSquareSingleReverseAfter256Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, inverseSquareSingleReverseBefore256Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, zpow_neg]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, inverseSquareSingleReverseBefore256Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, FloatingPointFormat.minNormalMagnitude,
        zpow_neg]
    · calc
        x = (16810015 : ℝ) / 4294967296 := by
          norm_num [x, inverseSquareSingleReverseBefore256Candidate,
            inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
            FloatingPointFormat.betaR, zpow_neg]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 8405007 (-7 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    norm_num [x, a, b, inverseSquareSingleReverseBefore256Candidate,
      inverseSquareSingleReverseAfter256Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hodd : ¬ FloatingPointFormat.evenMantissa 8405007 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hmleft hleft htie hodd
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, x, b, inverseSquareSingleReverseAfter256Candidate, fmt] using
    hround

/-- Kernel-checked mantissa prefix sum for the fifth reverse suffix
same-exponent band, namely the additions `255^{-2}, ..., 129^{-2}`. -/
theorem inverseSquareSingleReverseAfter256Prefix_255_to_129_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 32 255 127 = 8306835 := by
  set_option maxRecDepth 10000 in
  decide

/-- Boolean certificate for the fifth reverse same-exponent band.  Each entry
verifies the integer half-cell inequalities and the normal mantissa range for
the next rounded state. -/
def inverseSquareSingleReverseAfter256Band255To129CertificateBool : Bool :=
  (List.range 127).all (fun n =>
    let m := 8405008 + inverseSquareSingleReverseScaledMantissaPrefix 32 255 n
    let k := 255 - n
    let d := inverseSquareSingleScaledMantissaIncrement 32 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 32 ∧
      2 ^ 32 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the fifth reverse same-exponent band. -/
theorem inverseSquareSingleReverseAfter256Band255To129CertificateBool_eq_true :
    inverseSquareSingleReverseAfter256Band255To129CertificateBool = true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise extraction of the fifth reverse same-exponent band certificate. -/
theorem inverseSquareSingleReverseAfter256Band255To129Certificate
    {n : ℕ} (hn : n < 127) :
    let m := 8405008 + inverseSquareSingleReverseScaledMantissaPrefix 32 255 n
    let k := 255 - n
    let d := inverseSquareSingleScaledMantissaIncrement 32 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 32 ∧
      2 ^ 32 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 127,
        let m := 8405008 + inverseSquareSingleReverseScaledMantissaPrefix 32 255 x
        let k := 255 - x
        let d := inverseSquareSingleScaledMantissaIncrement 32 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 32 ∧
          2 ^ 32 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter256Band255To129CertificateBool] using
      inverseSquareSingleReverseAfter256Band255To129CertificateBool_eq_true
  simpa using hall n hn

/-- The fifth reverse suffix band is proved by the reusable same-exponent
band certificate theorem. -/
theorem inverseSquareSingleReverseAfter256Accumulator_255_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 127) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter256Candidate 255 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8405008 + inverseSquareSingleReverseScaledMantissaPrefix 32 255 n)
        (-7 : ℤ) := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (32 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8405008) (q := 32) (kTop := 255) (count := 127)
      hexp
      (fun {n} hn =>
        inverseSquareSingleReverseAfter256Band255To129Certificate hn)
      n hn
  simpa [inverseSquareSingleReverseAfter256Candidate] using hband

/-- Result of the fifth same-exponent reverse suffix band.  The state just
before the `128^{-2}` boundary step is the named mantissa `16711843` in the
exponent `-7` band. -/
theorem inverseSquareSingleReverseAfter256Accumulator_255_to_before128 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter256Candidate 255 127 =
      inverseSquareSingleReverseBefore128Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter256Accumulator_255_bandPrefix_of_le
      127 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter256Candidate 255 127 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8405008 + inverseSquareSingleReverseScaledMantissaPrefix 32 255 127)
        (-7 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore128Candidate := by
        rw [inverseSquareSingleReverseAfter256Prefix_255_to_129_eq]
        rfl

/-- Boundary step after the fifth same-exponent reverse suffix band: adding
`128^{-2}` to `inverseSquareSingleReverseBefore128Candidate` is an exact
midpoint between two exponent-`-6` binary32 values, and nearest/even selects
the even right endpoint `0x3c008052`. -/
theorem inverseSquareSingleReverseBefore128_add_128_term_rounds_to_after128 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore128Candidate 128 =
      inverseSquareSingleReverseAfter128Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let x : ℝ := inverseSquareSingleReverseBefore128Candidate + inverseSquareTerm 128
  let a : ℝ := fmt.normalizedValue false 8421457 (-6 : ℤ)
  let b : ℝ := inverseSquareSingleReverseAfter128Candidate
  have hmleft : fmt.normalizedMantissa 8421457 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmright : fmt.normalizedMantissa (8421457 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 8421457, (-6 : ℤ), hmleft, hmright, Or.inl ⟨rfl, ?_⟩⟩
    simp [b, inverseSquareSingleReverseAfter128Candidate, fmt]
  have hstrict : a < x ∧ x < b := by
    constructor <;> norm_num [x, a, b,
      inverseSquareSingleReverseBefore128Candidate,
      inverseSquareSingleReverseAfter128Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, inverseSquareSingleReverseBefore128Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, zpow_neg]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, inverseSquareSingleReverseBefore128Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, FloatingPointFormat.minNormalMagnitude,
        zpow_neg]
    · calc
        x = (16842915 : ℝ) / 2147483648 := by
          norm_num [x, inverseSquareSingleReverseBefore128Candidate,
            inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
            FloatingPointFormat.betaR, zpow_neg]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 8421457 (-6 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    norm_num [x, a, b, inverseSquareSingleReverseBefore128Candidate,
      inverseSquareSingleReverseAfter128Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hodd : ¬ FloatingPointFormat.evenMantissa 8421457 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hmleft hleft htie hodd
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, x, b, inverseSquareSingleReverseAfter128Candidate, fmt] using
    hround

/-- Kernel-checked mantissa prefix sum for the sixth reverse suffix
same-exponent band, namely the additions `127^{-2}, ..., 65^{-2}`. -/
theorem inverseSquareSingleReverseAfter128Prefix_127_to_65_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 31 127 63 = 8225361 := by
  set_option maxRecDepth 10000 in
  decide

/-- Boolean certificate for the sixth reverse same-exponent band.  Each entry
verifies the integer half-cell inequalities and the normal mantissa range for
the next rounded state. -/
def inverseSquareSingleReverseAfter128Band127To65CertificateBool : Bool :=
  (List.range 63).all (fun n =>
    let m := 8421458 + inverseSquareSingleReverseScaledMantissaPrefix 31 127 n
    let k := 127 - n
    let d := inverseSquareSingleScaledMantissaIncrement 31 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 31 ∧
      2 ^ 31 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the sixth reverse same-exponent band. -/
theorem inverseSquareSingleReverseAfter128Band127To65CertificateBool_eq_true :
    inverseSquareSingleReverseAfter128Band127To65CertificateBool = true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise extraction of the sixth reverse same-exponent band certificate. -/
theorem inverseSquareSingleReverseAfter128Band127To65Certificate
    {n : ℕ} (hn : n < 63) :
    let m := 8421458 + inverseSquareSingleReverseScaledMantissaPrefix 31 127 n
    let k := 127 - n
    let d := inverseSquareSingleScaledMantissaIncrement 31 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 31 ∧
      2 ^ 31 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 63,
        let m := 8421458 + inverseSquareSingleReverseScaledMantissaPrefix 31 127 x
        let k := 127 - x
        let d := inverseSquareSingleScaledMantissaIncrement 31 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 31 ∧
          2 ^ 31 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter128Band127To65CertificateBool] using
      inverseSquareSingleReverseAfter128Band127To65CertificateBool_eq_true
  simpa using hall n hn

/-- The sixth reverse suffix band is proved by the reusable same-exponent
band certificate theorem. -/
theorem inverseSquareSingleReverseAfter128Accumulator_127_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 63) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter128Candidate 127 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8421458 + inverseSquareSingleReverseScaledMantissaPrefix 31 127 n)
        (-6 : ℤ) := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (31 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8421458) (q := 31) (kTop := 127) (count := 63)
      hexp
      (fun {n} hn =>
        inverseSquareSingleReverseAfter128Band127To65Certificate hn)
      n hn
  simpa [inverseSquareSingleReverseAfter128Candidate] using hband

/-- Result of the sixth same-exponent reverse suffix band.  The state just
before the `64^{-2}` boundary step is the named mantissa `16646819` in the
exponent `-6` band. -/
theorem inverseSquareSingleReverseAfter128Accumulator_127_to_before64 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter128Candidate 127 63 =
      inverseSquareSingleReverseBefore64Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter128Accumulator_127_bandPrefix_of_le
      63 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter128Candidate 127 63 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8421458 + inverseSquareSingleReverseScaledMantissaPrefix 31 127 63)
        (-6 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore64Candidate := by
        rw [inverseSquareSingleReverseAfter128Prefix_127_to_65_eq]
        rfl

/-- Boundary step after the sixth same-exponent reverse suffix band: adding
`64^{-2}` to `inverseSquareSingleReverseBefore64Candidate` is an exact
midpoint between two exponent-`-5` binary32 values, and nearest/even selects
the even right endpoint `0x3c810152`. -/
theorem inverseSquareSingleReverseBefore64_add_64_term_rounds_to_after64 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore64Candidate 64 =
      inverseSquareSingleReverseAfter64Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let x : ℝ := inverseSquareSingleReverseBefore64Candidate + inverseSquareTerm 64
  let a : ℝ := fmt.normalizedValue false 8454481 (-5 : ℤ)
  let b : ℝ := inverseSquareSingleReverseAfter64Candidate
  have hmleft : fmt.normalizedMantissa 8454481 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmright : fmt.normalizedMantissa (8454481 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 8454481, (-5 : ℤ), hmleft, hmright, Or.inl ⟨rfl, ?_⟩⟩
    simp [b, inverseSquareSingleReverseAfter64Candidate, fmt]
  have hstrict : a < x ∧ x < b := by
    constructor <;> norm_num [x, a, b,
      inverseSquareSingleReverseBefore64Candidate,
      inverseSquareSingleReverseAfter64Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, inverseSquareSingleReverseBefore64Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, zpow_neg]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, inverseSquareSingleReverseBefore64Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, FloatingPointFormat.minNormalMagnitude,
        zpow_neg]
    · calc
        x = (16908963 : ℝ) / 1073741824 := by
          norm_num [x, inverseSquareSingleReverseBefore64Candidate,
            inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
            FloatingPointFormat.betaR, zpow_neg]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 8454481 (-5 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    norm_num [x, a, b, inverseSquareSingleReverseBefore64Candidate,
      inverseSquareSingleReverseAfter64Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hodd : ¬ FloatingPointFormat.evenMantissa 8454481 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hmleft hleft htie hodd
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, x, b, inverseSquareSingleReverseAfter64Candidate, fmt] using
    hround

/-- Kernel-checked mantissa prefix sum for the seventh reverse suffix
same-exponent band, namely the additions `63^{-2}, ..., 33^{-2}`. -/
theorem inverseSquareSingleReverseAfter64Prefix_63_to_33_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 30 63 31 = 8063314 := by
  set_option maxRecDepth 10000 in
  decide

/-- Boolean certificate for the seventh reverse same-exponent band.  Each
entry verifies the integer half-cell inequalities and the normal mantissa range
for the next rounded state. -/
def inverseSquareSingleReverseAfter64Band63To33CertificateBool : Bool :=
  (List.range 31).all (fun n =>
    let m := 8454482 + inverseSquareSingleReverseScaledMantissaPrefix 30 63 n
    let k := 63 - n
    let d := inverseSquareSingleScaledMantissaIncrement 30 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 30 ∧
      2 ^ 30 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the seventh reverse same-exponent band. -/
theorem inverseSquareSingleReverseAfter64Band63To33CertificateBool_eq_true :
    inverseSquareSingleReverseAfter64Band63To33CertificateBool = true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise extraction of the seventh reverse same-exponent band certificate. -/
theorem inverseSquareSingleReverseAfter64Band63To33Certificate
    {n : ℕ} (hn : n < 31) :
    let m := 8454482 + inverseSquareSingleReverseScaledMantissaPrefix 30 63 n
    let k := 63 - n
    let d := inverseSquareSingleScaledMantissaIncrement 30 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 30 ∧
      2 ^ 30 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 31,
        let m := 8454482 + inverseSquareSingleReverseScaledMantissaPrefix 30 63 x
        let k := 63 - x
        let d := inverseSquareSingleScaledMantissaIncrement 30 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 30 ∧
          2 ^ 30 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter64Band63To33CertificateBool] using
      inverseSquareSingleReverseAfter64Band63To33CertificateBool_eq_true
  simpa using hall n hn

/-- The seventh reverse suffix band is proved by the reusable same-exponent
band certificate theorem. -/
theorem inverseSquareSingleReverseAfter64Accumulator_63_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 31) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter64Candidate 63 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8454482 + inverseSquareSingleReverseScaledMantissaPrefix 30 63 n)
        (-5 : ℤ) := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (30 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8454482) (q := 30) (kTop := 63) (count := 31)
      hexp
      (fun {n} hn =>
        inverseSquareSingleReverseAfter64Band63To33Certificate hn)
      n hn
  simpa [inverseSquareSingleReverseAfter64Candidate] using hband

/-- Result of the seventh same-exponent reverse suffix band.  The state just
before the `32^{-2}` boundary step is the named mantissa `16517796` in the
exponent `-5` band. -/
theorem inverseSquareSingleReverseAfter64Accumulator_63_to_before32 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter64Candidate 63 31 =
      inverseSquareSingleReverseBefore32Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter64Accumulator_63_bandPrefix_of_le
      31 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter64Candidate 63 31 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8454482 + inverseSquareSingleReverseScaledMantissaPrefix 30 63 31)
        (-5 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore32Candidate := by
        rw [inverseSquareSingleReverseAfter64Prefix_63_to_33_eq]
        rfl

/-- Boundary step after the seventh same-exponent reverse suffix band: adding
`32^{-2}` to `inverseSquareSingleReverseBefore32Candidate` is exactly
representable as the exponent-`-4` binary32 state `0x3d020552`. -/
theorem inverseSquareSingleReverseBefore32_add_32_term_rounds_to_after32 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore32Candidate 32 =
      inverseSquareSingleReverseAfter32Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfinite :
      fmt.finiteSystem
        (inverseSquareSingleReverseBefore32Candidate +
          inverseSquareTerm 32) := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8521042, (-4 : ℤ), ?hm, ?he, ?hval⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    · norm_num [inverseSquareSingleReverseBefore32Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
  calc
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore32Candidate 32 =
      inverseSquareSingleReverseBefore32Candidate +
        inverseSquareTerm 32 := by
        simpa [inverseSquareSingleForwardStep, fmt, BasicOp.exact] using
          (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add)
            (x := inverseSquareSingleReverseBefore32Candidate)
            (y := inverseSquareTerm 32)
            hfinite)
    _ = inverseSquareSingleReverseAfter32Candidate := by
      norm_num [inverseSquareSingleReverseBefore32Candidate,
        inverseSquareSingleReverseAfter32Candidate, inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]

/-- Kernel-checked mantissa prefix sum for the eighth reverse suffix
same-exponent band, namely the additions `31^{-2}, ..., 17^{-2}`. -/
theorem inverseSquareSingleReverseAfter32Prefix_31_to_17_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 29 31 15 = 7742797 := by
  set_option maxRecDepth 10000 in
  decide

/-- Boolean certificate for the eighth reverse same-exponent band. -/
def inverseSquareSingleReverseAfter32Band31To17CertificateBool : Bool :=
  (List.range 15).all (fun n =>
    let m := 8521042 + inverseSquareSingleReverseScaledMantissaPrefix 29 31 n
    let k := 31 - n
    let d := inverseSquareSingleScaledMantissaIncrement 29 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 29 ∧
      2 ^ 29 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the eighth reverse same-exponent band. -/
theorem inverseSquareSingleReverseAfter32Band31To17CertificateBool_eq_true :
    inverseSquareSingleReverseAfter32Band31To17CertificateBool = true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise extraction of the eighth reverse same-exponent band certificate. -/
theorem inverseSquareSingleReverseAfter32Band31To17Certificate
    {n : ℕ} (hn : n < 15) :
    let m := 8521042 + inverseSquareSingleReverseScaledMantissaPrefix 29 31 n
    let k := 31 - n
    let d := inverseSquareSingleScaledMantissaIncrement 29 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 29 ∧
      2 ^ 29 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 15,
        let m := 8521042 + inverseSquareSingleReverseScaledMantissaPrefix 29 31 x
        let k := 31 - x
        let d := inverseSquareSingleScaledMantissaIncrement 29 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 29 ∧
          2 ^ 29 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter32Band31To17CertificateBool] using
      inverseSquareSingleReverseAfter32Band31To17CertificateBool_eq_true
  simpa using hall n hn

/-- The eighth reverse suffix band is proved by the reusable same-exponent
band certificate theorem. -/
theorem inverseSquareSingleReverseAfter32Accumulator_31_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 15) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter32Candidate 31 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8521042 + inverseSquareSingleReverseScaledMantissaPrefix 29 31 n)
        (-4 : ℤ) := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (29 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8521042) (q := 29) (kTop := 31) (count := 15)
      hexp
      (fun {n} hn =>
        inverseSquareSingleReverseAfter32Band31To17Certificate hn)
      n hn
  simpa [inverseSquareSingleReverseAfter32Candidate] using hband

/-- Result of the eighth same-exponent reverse suffix band. -/
theorem inverseSquareSingleReverseAfter32Accumulator_31_to_before16 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter32Candidate 31 15 =
      inverseSquareSingleReverseBefore16Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter32Accumulator_31_bandPrefix_of_le
      15 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter32Candidate 31 15 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8521042 + inverseSquareSingleReverseScaledMantissaPrefix 29 31 15)
        (-4 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore16Candidate := by
        rw [inverseSquareSingleReverseAfter32Prefix_31_to_17_eq]
        rfl

/-- Boundary step after the eighth same-exponent reverse suffix band: adding
`16^{-2}` to `inverseSquareSingleReverseBefore16Candidate` is an exact
midpoint between two exponent-`-3` binary32 values, and nearest/even selects
the even right endpoint `0x3d841550`. -/
theorem inverseSquareSingleReverseBefore16_add_16_term_rounds_to_after16 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore16Candidate 16 =
      inverseSquareSingleReverseAfter16Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let x : ℝ := inverseSquareSingleReverseBefore16Candidate + inverseSquareTerm 16
  let a : ℝ := fmt.normalizedValue false 8656207 (-3 : ℤ)
  let b : ℝ := inverseSquareSingleReverseAfter16Candidate
  have hmleft : fmt.normalizedMantissa 8656207 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmright : fmt.normalizedMantissa (8656207 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 8656207, (-3 : ℤ), hmleft, hmright, Or.inl ⟨rfl, ?_⟩⟩
    simp [b, inverseSquareSingleReverseAfter16Candidate, fmt]
  have hstrict : a < x ∧ x < b := by
    constructor <;> norm_num [x, a, b,
      inverseSquareSingleReverseBefore16Candidate,
      inverseSquareSingleReverseAfter16Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      norm_num [x, inverseSquareSingleReverseBefore16Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, zpow_neg]
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, inverseSquareSingleReverseBefore16Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, FloatingPointFormat.minNormalMagnitude,
        zpow_neg]
    · calc
        x = (17312415 : ℝ) / 268435456 := by
          norm_num [x, inverseSquareSingleReverseBefore16Candidate,
            inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
            FloatingPointFormat.betaR, zpow_neg]
        _ ≤ 340282346638528859811704183484516925440 := by
          norm_num
        _ = fmt.maxFiniteMagnitude := by
          norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR,
            zpow_neg]
          rfl
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 8656207 (-3 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    norm_num [x, a, b, inverseSquareSingleReverseBefore16Candidate,
      inverseSquareSingleReverseAfter16Candidate, inverseSquareTerm,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hodd : ¬ FloatingPointFormat.evenMantissa 8656207 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hmleft hleft htie hodd
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, x, b, inverseSquareSingleReverseAfter16Candidate, fmt] using
    hround

/-- Kernel-checked mantissa prefix sum for the ninth reverse suffix
same-exponent band, namely the additions `15^{-2}, ..., 9^{-2}`. -/
theorem inverseSquareSingleReverseAfter16Prefix_15_to_9_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 28 15 7 = 7115986 := by
  set_option maxRecDepth 10000 in
  decide

/-- Boolean certificate for the ninth reverse same-exponent band. -/
def inverseSquareSingleReverseAfter16Band15To9CertificateBool : Bool :=
  (List.range 7).all (fun n =>
    let m := 8656208 + inverseSquareSingleReverseScaledMantissaPrefix 28 15 n
    let k := 15 - n
    let d := inverseSquareSingleScaledMantissaIncrement 28 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 28 ∧
      2 ^ 28 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the ninth reverse same-exponent band. -/
theorem inverseSquareSingleReverseAfter16Band15To9CertificateBool_eq_true :
    inverseSquareSingleReverseAfter16Band15To9CertificateBool = true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise extraction of the ninth reverse same-exponent band certificate. -/
theorem inverseSquareSingleReverseAfter16Band15To9Certificate
    {n : ℕ} (hn : n < 7) :
    let m := 8656208 + inverseSquareSingleReverseScaledMantissaPrefix 28 15 n
    let k := 15 - n
    let d := inverseSquareSingleScaledMantissaIncrement 28 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 28 ∧
      2 ^ 28 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 7,
        let m := 8656208 + inverseSquareSingleReverseScaledMantissaPrefix 28 15 x
        let k := 15 - x
        let d := inverseSquareSingleScaledMantissaIncrement 28 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 28 ∧
          2 ^ 28 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter16Band15To9CertificateBool] using
      inverseSquareSingleReverseAfter16Band15To9CertificateBool_eq_true
  simpa using hall n hn

/-- The ninth reverse suffix band is proved by the reusable same-exponent
band certificate theorem. -/
theorem inverseSquareSingleReverseAfter16Accumulator_15_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 7) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter16Candidate 15 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8656208 + inverseSquareSingleReverseScaledMantissaPrefix 28 15 n)
        (-3 : ℤ) := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (28 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8656208) (q := 28) (kTop := 15) (count := 7)
      hexp
      (fun {n} hn =>
        inverseSquareSingleReverseAfter16Band15To9Certificate hn)
      n hn
  simpa [inverseSquareSingleReverseAfter16Candidate] using hband

/-- Result of the ninth same-exponent reverse suffix band. -/
theorem inverseSquareSingleReverseAfter16Accumulator_15_to_before8 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter16Candidate 15 7 =
      inverseSquareSingleReverseBefore8Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter16Accumulator_15_bandPrefix_of_le
      7 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter16Candidate 15 7 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8656208 + inverseSquareSingleReverseScaledMantissaPrefix 28 15 7)
        (-3 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore8Candidate := by
        rw [inverseSquareSingleReverseAfter16Prefix_15_to_9_eq]
        rfl

/-- Boundary step after the ninth same-exponent reverse suffix band: adding
`8^{-2}` to `inverseSquareSingleReverseBefore8Candidate` is exactly
representable as the exponent-`-2` binary32 state `0x3e085511`. -/
theorem inverseSquareSingleReverseBefore8_add_8_term_rounds_to_after8 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore8Candidate 8 =
      inverseSquareSingleReverseAfter8Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfinite :
      fmt.finiteSystem
        (inverseSquareSingleReverseBefore8Candidate +
          inverseSquareTerm 8) := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8934673, (-2 : ℤ), ?hm, ?he, ?hval⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    · norm_num [inverseSquareSingleReverseBefore8Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
  calc
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore8Candidate 8 =
      inverseSquareSingleReverseBefore8Candidate +
        inverseSquareTerm 8 := by
        simpa [inverseSquareSingleForwardStep, fmt, BasicOp.exact] using
          (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add)
            (x := inverseSquareSingleReverseBefore8Candidate)
            (y := inverseSquareTerm 8)
            hfinite)
    _ = inverseSquareSingleReverseAfter8Candidate := by
      norm_num [inverseSquareSingleReverseBefore8Candidate,
        inverseSquareSingleReverseAfter8Candidate, inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]

/-- Kernel-checked mantissa prefix sum for the final reverse same-exponent
band before the last four terms, namely `7^{-2}, 6^{-2}, 5^{-2}`. -/
theorem inverseSquareSingleReverseAfter8Prefix_7_to_5_eq :
    inverseSquareSingleReverseScaledMantissaPrefix 27 7 3 = 5918059 := by
  set_option maxRecDepth 10000 in
  decide

/-- Boolean certificate for the final reverse same-exponent band before the
last four terms. -/
def inverseSquareSingleReverseAfter8Band7To5CertificateBool : Bool :=
  (List.range 3).all (fun n =>
    let m := 8934673 + inverseSquareSingleReverseScaledMantissaPrefix 27 7 n
    let k := 7 - n
    let d := inverseSquareSingleScaledMantissaIncrement 27 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 27 ∧
      2 ^ 27 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216))

/-- Kernel-checked certificate for the final reverse same-exponent band before
the last four terms. -/
theorem inverseSquareSingleReverseAfter8Band7To5CertificateBool_eq_true :
    inverseSquareSingleReverseAfter8Band7To5CertificateBool = true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise extraction of the final reverse same-exponent band certificate. -/
theorem inverseSquareSingleReverseAfter8Band7To5Certificate
    {n : ℕ} (hn : n < 3) :
    let m := 8934673 + inverseSquareSingleReverseScaledMantissaPrefix 27 7 n
    let k := 7 - n
    let d := inverseSquareSingleScaledMantissaIncrement 27 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 27 ∧
      2 ^ 27 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ m + d - 1 ∧
      m + d + 1 < 16777216 := by
  have hall :
      ∀ x < 3,
        let m := 8934673 + inverseSquareSingleReverseScaledMantissaPrefix 27 7 x
        let k := 7 - x
        let d := inverseSquareSingleScaledMantissaIncrement 27 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 27 ∧
          2 ^ 27 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter8Band7To5CertificateBool] using
      inverseSquareSingleReverseAfter8Band7To5CertificateBool_eq_true
  simpa using hall n hn

/-- The final reverse same-exponent band before the last four terms is proved
by the reusable same-exponent band certificate theorem. -/
theorem inverseSquareSingleReverseAfter8Accumulator_7_bandPrefix_of_le
    (n : ℕ) (hn : n ≤ 3) :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter8Candidate 7 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8934673 + inverseSquareSingleReverseScaledMantissaPrefix 27 7 n)
        (-2 : ℤ) := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (27 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8934673) (q := 27) (kTop := 7) (count := 3)
      hexp
      (fun {n} hn =>
        inverseSquareSingleReverseAfter8Band7To5Certificate hn)
      n hn
  simpa [inverseSquareSingleReverseAfter8Candidate] using hband

/-- Result of the final reverse same-exponent band before the last four terms. -/
theorem inverseSquareSingleReverseAfter8Accumulator_7_to_before4 :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter8Candidate 7 3 =
      inverseSquareSingleReverseBefore4Candidate := by
  have hband :=
    inverseSquareSingleReverseAfter8Accumulator_7_bandPrefix_of_le
      3 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter8Candidate 7 3 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8934673 + inverseSquareSingleReverseScaledMantissaPrefix 27 7 3)
        (-2 : ℤ) := hband
    _ =
      inverseSquareSingleReverseBefore4Candidate := by
        rw [inverseSquareSingleReverseAfter8Prefix_7_to_5_eq]
        rfl

/-- Adding `4^{-2}` to the before-`4` state is exactly representable. -/
theorem inverseSquareSingleReverseBefore4_add_4_term_rounds_to_after4 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore4Candidate 4 =
      inverseSquareSingleReverseAfter4Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfinite :
      fmt.finiteSystem
        (inverseSquareSingleReverseBefore4Candidate +
          inverseSquareTerm 4) := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 9523518, (-1 : ℤ), ?hm, ?he, ?hval⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    · norm_num [inverseSquareSingleReverseBefore4Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
  calc
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseBefore4Candidate 4 =
      inverseSquareSingleReverseBefore4Candidate +
        inverseSquareTerm 4 := by
        simpa [inverseSquareSingleForwardStep, fmt, BasicOp.exact] using
          (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add)
            (x := inverseSquareSingleReverseBefore4Candidate)
            (y := inverseSquareTerm 4)
            hfinite)
    _ = inverseSquareSingleReverseAfter4Candidate := by
      norm_num [inverseSquareSingleReverseBefore4Candidate,
        inverseSquareSingleReverseAfter4Candidate, inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]

/-- Adding `3^{-2}` to the after-`4` state rounds to the named after-`3`
state by an integer half-cell certificate at exponent `-1`. -/
theorem inverseSquareSingleReverseAfter4_add_3_term_rounds_to_after3 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseAfter4Candidate 3 =
      inverseSquareSingleReverseAfter3Candidate := by
  have hstep :=
    inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale
      (m := 9523518) (d := 3728270) (k := 3) (q := 26)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa,
          FloatingPointFormat.mantissaInRange])
      (by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa,
          FloatingPointFormat.mantissaInRange])
      (by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa,
          FloatingPointFormat.mantissaInRange])
      (by
        norm_num [FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.exponentInRange])
  simpa [inverseSquareSingleReverseAfter4Candidate,
    inverseSquareSingleReverseAfter3Candidate] using hstep

/-- Adding `2^{-2}` to the after-`3` state is exactly representable. -/
theorem inverseSquareSingleReverseAfter3_add_2_term_rounds_to_after2 :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseAfter3Candidate 2 =
      inverseSquareSingleReverseAfter2Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfinite :
      fmt.finiteSystem
        (inverseSquareSingleReverseAfter3Candidate +
          inverseSquareTerm 2) := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 10820198, (0 : ℤ), ?hm, ?he, ?hval⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    · norm_num [inverseSquareSingleReverseAfter3Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
  calc
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseAfter3Candidate 2 =
      inverseSquareSingleReverseAfter3Candidate +
        inverseSquareTerm 2 := by
        simpa [inverseSquareSingleForwardStep, fmt, BasicOp.exact] using
          (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add)
            (x := inverseSquareSingleReverseAfter3Candidate)
            (y := inverseSquareTerm 2)
            hfinite)
    _ = inverseSquareSingleReverseAfter2Candidate := by
      norm_num [inverseSquareSingleReverseAfter3Candidate,
        inverseSquareSingleReverseAfter2Candidate, inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]

/-- Adding `1^{-2}` to the after-`2` state is exactly representable and lands
on the repository-model displayed reverse accumulator. -/
theorem inverseSquareSingleReverseAfter2_add_1_term_rounds_to_printed :
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseAfter2Candidate 1 =
      inverseSquareSingleReversePrintedAccumulator := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfinite :
      fmt.finiteSystem
        (inverseSquareSingleReverseAfter2Candidate +
          inverseSquareTerm 1) := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 13798707, (1 : ℤ), ?hm, ?he, ?hval⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    · norm_num [inverseSquareSingleReverseAfter2Candidate,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
      exact (by
        norm_num :
          (5410099 : ℝ) / 8388608 + 1 = (13798707 : ℝ) / 8388608)
  calc
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseAfter2Candidate 1 =
      inverseSquareSingleReverseAfter2Candidate +
        inverseSquareTerm 1 := by
        simpa [inverseSquareSingleForwardStep, fmt, BasicOp.exact] using
          (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add)
            (x := inverseSquareSingleReverseAfter2Candidate)
            (y := inverseSquareTerm 1)
            hfinite)
    _ = inverseSquareSingleReversePrintedAccumulator := by
      norm_num [inverseSquareSingleReverseAfter2Candidate,
        inverseSquareSingleReversePrintedAccumulator, inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
      exact (by
        norm_num :
          (5410099 : ℝ) / 8388608 + 1 = (13798707 : ℝ) / 8388608)

/-- Archived optional certificate for the repository-model reverse route: the
rounded high-index prefix state lies in the suffix-start window. -/
def inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow : Prop :=
  inverseSquareSingleReverseSuffixStartLower ≤
      inverseSquareSingleReverseTenPowNineHighPrefixState ∧
    inverseSquareSingleReverseTenPowNineHighPrefixState ≤
      inverseSquareSingleReverseSuffixStartUpper

/-- Tighter archived optional certificate for the repository-model reverse
route: the rounded high-index prefix state lies in the refined suffix-start
window. -/
def inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow : Prop :=
  inverseSquareSingleReverseSuffixStartLower ≤
      inverseSquareSingleReverseTenPowNineHighPrefixState ∧
    inverseSquareSingleReverseTenPowNineHighPrefixState ≤
      inverseSquareSingleReverseSuffixStartUpperTight

/-- Archived optional suffix certificate for the repository-model reverse route:
every start in the displayed suffix window maps, after the final `4096` reverse
additions, to the displayed model accumulator. -/
def inverseSquareSingleReverseSuffixWindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseSuffixStartLower ≤ start →
      start ≤ inverseSquareSingleReverseSuffixStartUpper →
        inverseSquareSingleReverseAccumulatorFrom start 4096 4096 =
          inverseSquareSingleReversePrintedAccumulator

/-- Tighter-window form of the archived optional suffix certificate.  This
retains the whole-window replacement for the earlier wider window: every start
in the refined interval maps, after the final `4096` reverse additions, to the
displayed model accumulator. -/
def inverseSquareSingleReverseTightSuffixWindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseSuffixStartLower ≤ start →
      start ≤ inverseSquareSingleReverseSuffixStartUpperTight →
        inverseSquareSingleReverseAccumulatorFrom start 4096 4096 =
          inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete high-prefix equality certificate for the
repository-model reverse-order run. -/
def inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate : Prop :=
  inverseSquareSingleReverseTenPowNineHighPrefixState =
    inverseSquareSingleReverseTenPowNineHighPrefixCandidate

/-- Archived optional concrete suffix certificate from the observed
repository-model high-prefix candidate to the displayed model accumulator. -/
def inverseSquareSingleReverseCandidateSuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate 4096 4096 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the exact `4096^{-2}`
candidate step has been discharged. -/
def inverseSquareSingleReverseAfter4096SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseAfter4096Candidate 4095 4095 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the first two low-index
candidate suffix steps have been discharged. -/
def inverseSquareSingleReverseAfter4095SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseAfter4095Candidate 4094 4094 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the first same-exponent
band `4094^{-2}, ..., 2049^{-2}` has been discharged. -/
def inverseSquareSingleReverseBefore2048SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore2048Candidate 2048 2048 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the `2048^{-2}` boundary
step and the same-exponent band `2047^{-2}, ..., 1025^{-2}` have been
discharged. -/
def inverseSquareSingleReverseBefore1024SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore1024Candidate 1024 1024 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the `1024^{-2}` boundary
step and the same-exponent band `1023^{-2}, ..., 513^{-2}` have been
discharged. -/
def inverseSquareSingleReverseBefore512SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore512Candidate 512 512 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the `512^{-2}` boundary
step and the same-exponent band `511^{-2}, ..., 257^{-2}` have been
discharged. -/
def inverseSquareSingleReverseBefore256SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore256Candidate 256 256 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the `256^{-2}` boundary
step and the same-exponent band `255^{-2}, ..., 129^{-2}` have been
discharged. -/
def inverseSquareSingleReverseBefore128SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore128Candidate 128 128 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the `128^{-2}` boundary
step and the same-exponent band `127^{-2}, ..., 65^{-2}` has been discharged. -/
def inverseSquareSingleReverseBefore64SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore64Candidate 64 64 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the `64^{-2}` boundary
step and the same-exponent band `63^{-2}, ..., 33^{-2}` has been discharged. -/
def inverseSquareSingleReverseBefore32SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore32Candidate 32 32 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the `32^{-2}` boundary
step and the same-exponent band `31^{-2}, ..., 17^{-2}` has been discharged. -/
def inverseSquareSingleReverseBefore16SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore16Candidate 16 16 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the `16^{-2}` boundary
step and the same-exponent band `15^{-2}, ..., 9^{-2}` has been discharged. -/
def inverseSquareSingleReverseBefore8SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore8Candidate 8 8 =
    inverseSquareSingleReversePrintedAccumulator

/-- Archived optional concrete suffix certificate after the `8^{-2}` boundary
step and the band `7^{-2}, 6^{-2}, 5^{-2}` has been discharged. -/
def inverseSquareSingleReverseBefore4SuffixMapsToPrinted : Prop :=
  inverseSquareSingleReverseAccumulatorFrom
      inverseSquareSingleReverseBefore4Candidate 4 4 =
    inverseSquareSingleReversePrintedAccumulator

/-- The concrete high-prefix equality certificate implies the broader
suffix-window certificate. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_candidate
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate) :
    inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow := by
  rw [inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate] at hprefix
  change
    inverseSquareSingleReverseSuffixStartLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixState ∧
      inverseSquareSingleReverseTenPowNineHighPrefixState ≤
        inverseSquareSingleReverseSuffixStartUpper
  rw [hprefix]
  exact inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartWindow

/-- The concrete high-prefix equality certificate implies the refined
suffix-window certificate. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_eq_candidate
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate) :
    inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow := by
  rw [inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate] at hprefix
  change
    inverseSquareSingleReverseSuffixStartLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixState ∧
      inverseSquareSingleReverseTenPowNineHighPrefixState ≤
        inverseSquareSingleReverseSuffixStartUpperTight
  rw [hprefix]
  exact
    inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartTightWindow

/-- The concrete candidate suffix trace implies the broader suffix-window
certificate when the actual high prefix is known to equal that candidate. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidate_certificates
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate)
    (hsuffix : inverseSquareSingleReverseCandidateSuffixMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator := by
  rw [inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096]
  rw [inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate] at hprefix
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseTenPowNineHighPrefixState 4096 4096 =
      inverseSquareSingleReversePrintedAccumulator
  rw [hprefix]
  exact hsuffix

/-- Closing the exact first suffix step reduces the concrete printed-value
suffix certificate from `4096` remaining low-index additions to `4095`. -/
theorem inverseSquareSingleReverseCandidateSuffixMapsToPrinted_of_after4096
    (hsuffix : inverseSquareSingleReverseAfter4096SuffixMapsToPrinted) :
    inverseSquareSingleReverseCandidateSuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate 4096 4096 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 4096 = 1 + 4095 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseTenPowNineHighPrefixCandidate 4096 1 =
        inverseSquareSingleReverseAfter4096Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseTenPowNineHighPrefixCandidate (4096 - 0) =
        inverseSquareSingleReverseAfter4096Candidate
    simpa using
      inverseSquareSingleReverseCandidate_add_4096_term_rounds_to_after4096
  rw [hfirst]
  rw [show 4096 - 1 = 4095 by norm_num]
  exact hsuffix

/-- Closing the second suffix step reduces the after-`4096` suffix certificate
from `4095` remaining low-index additions to `4094`. -/
theorem inverseSquareSingleReverseAfter4096SuffixMapsToPrinted_of_after4095
    (hsuffix : inverseSquareSingleReverseAfter4095SuffixMapsToPrinted) :
    inverseSquareSingleReverseAfter4096SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter4096Candidate 4095 4095 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 4095 = 1 + 4094 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter4096Candidate 4095 1 =
        inverseSquareSingleReverseAfter4095Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseAfter4096Candidate (4095 - 0) =
        inverseSquareSingleReverseAfter4095Candidate
    simpa using
      inverseSquareSingleReverseAfter4096_add_4095_term_rounds_to_after4095
  rw [hfirst]
  rw [show 4095 - 1 = 4094 by norm_num]
  exact hsuffix

/-- Closing the first same-exponent after-`4095` suffix band reduces the
archived optional concrete suffix certificate from `4094` additions to the
boundary certificate beginning with `2048^{-2}`. -/
theorem inverseSquareSingleReverseAfter4095SuffixMapsToPrinted_of_before2048
    (hsuffix : inverseSquareSingleReverseBefore2048SuffixMapsToPrinted) :
    inverseSquareSingleReverseAfter4095SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter4095Candidate 4094 4094 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 4094 = 2046 + 2048 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter4095Accumulator_4094_to_before2048]
  rw [show 4094 - 2046 = 2048 by norm_num]
  exact hsuffix

/-- Closing the `2048^{-2}` boundary step and the following same-exponent band
reduces the archived optional concrete suffix certificate from the
before-`2048` state to the boundary certificate beginning with `1024^{-2}`. -/
theorem inverseSquareSingleReverseBefore2048SuffixMapsToPrinted_of_before1024
    (hsuffix : inverseSquareSingleReverseBefore1024SuffixMapsToPrinted) :
    inverseSquareSingleReverseBefore2048SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore2048Candidate 2048 2048 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 2048 = 1 + (1023 + 1024) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore2048Candidate 2048 1 =
        inverseSquareSingleReverseAfter2048Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore2048Candidate (2048 - 0) =
        inverseSquareSingleReverseAfter2048Candidate
    simpa using
      inverseSquareSingleReverseBefore2048_add_2048_term_rounds_to_after2048
  rw [hfirst]
  rw [show 2048 - 1 = 2047 by norm_num]
  rw [show 1023 + 1024 = 2047 by norm_num]
  rw [show 2047 = 1023 + 1024 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter2048Accumulator_2047_to_before1024]
  rw [show 2047 - 1023 = 1024 by norm_num]
  exact hsuffix

/-- Closing the `1024^{-2}` exact boundary step and the following same-exponent
band reduces the archived optional concrete suffix certificate from the
before-`1024` state to the boundary certificate beginning with `512^{-2}`. -/
theorem inverseSquareSingleReverseBefore1024SuffixMapsToPrinted_of_before512
    (hsuffix : inverseSquareSingleReverseBefore512SuffixMapsToPrinted) :
    inverseSquareSingleReverseBefore1024SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore1024Candidate 1024 1024 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 1024 = 1 + (511 + 512) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore1024Candidate 1024 1 =
        inverseSquareSingleReverseAfter1024Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore1024Candidate (1024 - 0) =
        inverseSquareSingleReverseAfter1024Candidate
    simpa using
      inverseSquareSingleReverseBefore1024_add_1024_term_rounds_to_after1024
  rw [hfirst]
  rw [show 1024 - 1 = 1023 by norm_num]
  rw [show 511 + 512 = 1023 by norm_num]
  rw [show 1023 = 511 + 512 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter1024Accumulator_1023_to_before512]
  rw [show 1023 - 511 = 512 by norm_num]
  exact hsuffix

/-- Closing the `512^{-2}` midpoint boundary step and the following
same-exponent band reduces the archived optional concrete suffix certificate
from the before-`512` state to the boundary certificate beginning with
`256^{-2}`. -/
theorem inverseSquareSingleReverseBefore512SuffixMapsToPrinted_of_before256
    (hsuffix : inverseSquareSingleReverseBefore256SuffixMapsToPrinted) :
    inverseSquareSingleReverseBefore512SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore512Candidate 512 512 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 512 = 1 + (255 + 256) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore512Candidate 512 1 =
        inverseSquareSingleReverseAfter512Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore512Candidate (512 - 0) =
        inverseSquareSingleReverseAfter512Candidate
    simpa using
      inverseSquareSingleReverseBefore512_add_512_term_rounds_to_after512
  rw [hfirst]
  rw [show 512 - 1 = 511 by norm_num]
  rw [show 255 + 256 = 511 by norm_num]
  rw [show 511 = 255 + 256 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter512Accumulator_511_to_before256]
  rw [show 511 - 255 = 256 by norm_num]
  exact hsuffix

/-- Closing the `256^{-2}` midpoint boundary step and the following
same-exponent band reduces the archived optional concrete suffix certificate
from the before-`256` state to the boundary certificate beginning with
`128^{-2}`. -/
theorem inverseSquareSingleReverseBefore256SuffixMapsToPrinted_of_before128
    (hsuffix : inverseSquareSingleReverseBefore128SuffixMapsToPrinted) :
    inverseSquareSingleReverseBefore256SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore256Candidate 256 256 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 256 = 1 + (127 + 128) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore256Candidate 256 1 =
        inverseSquareSingleReverseAfter256Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore256Candidate (256 - 0) =
        inverseSquareSingleReverseAfter256Candidate
    simpa using
      inverseSquareSingleReverseBefore256_add_256_term_rounds_to_after256
  rw [hfirst]
  rw [show 256 - 1 = 255 by norm_num]
  rw [show 127 + 128 = 255 by norm_num]
  rw [show 255 = 127 + 128 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter256Accumulator_255_to_before128]
  rw [show 255 - 127 = 128 by norm_num]
  exact hsuffix

/-- Closing the `128^{-2}` midpoint boundary step and the following
same-exponent band reduces the archived optional concrete suffix certificate
from the before-`128` state to the boundary certificate beginning with
`64^{-2}`. -/
theorem inverseSquareSingleReverseBefore128SuffixMapsToPrinted_of_before64
    (hsuffix : inverseSquareSingleReverseBefore64SuffixMapsToPrinted) :
    inverseSquareSingleReverseBefore128SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore128Candidate 128 128 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 128 = 1 + (63 + 64) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore128Candidate 128 1 =
        inverseSquareSingleReverseAfter128Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore128Candidate (128 - 0) =
        inverseSquareSingleReverseAfter128Candidate
    simpa using
      inverseSquareSingleReverseBefore128_add_128_term_rounds_to_after128
  rw [hfirst]
  rw [show 128 - 1 = 127 by norm_num]
  rw [show 63 + 64 = 127 by norm_num]
  rw [show 127 = 63 + 64 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter128Accumulator_127_to_before64]
  rw [show 127 - 63 = 64 by norm_num]
  exact hsuffix

/-- Closing the `64^{-2}` midpoint boundary step and the following
same-exponent band reduces the archived optional concrete suffix certificate
from the before-`64` state to the boundary certificate beginning with
`32^{-2}`. -/
theorem inverseSquareSingleReverseBefore64SuffixMapsToPrinted_of_before32
    (hsuffix : inverseSquareSingleReverseBefore32SuffixMapsToPrinted) :
    inverseSquareSingleReverseBefore64SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore64Candidate 64 64 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 64 = 1 + (31 + 32) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore64Candidate 64 1 =
        inverseSquareSingleReverseAfter64Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore64Candidate (64 - 0) =
        inverseSquareSingleReverseAfter64Candidate
    simpa using
      inverseSquareSingleReverseBefore64_add_64_term_rounds_to_after64
  rw [hfirst]
  rw [show 64 - 1 = 63 by norm_num]
  rw [show 31 + 32 = 63 by norm_num]
  rw [show 63 = 31 + 32 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter64Accumulator_63_to_before32]
  rw [show 63 - 31 = 32 by norm_num]
  exact hsuffix

/-- Closing the `32^{-2}` exact boundary step and the following same-exponent
band reduces the archived optional concrete suffix certificate from the
before-`32` state to the boundary certificate beginning with `16^{-2}`. -/
theorem inverseSquareSingleReverseBefore32SuffixMapsToPrinted_of_before16
    (hsuffix : inverseSquareSingleReverseBefore16SuffixMapsToPrinted) :
    inverseSquareSingleReverseBefore32SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore32Candidate 32 32 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 32 = 1 + (15 + 16) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore32Candidate 32 1 =
        inverseSquareSingleReverseAfter32Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore32Candidate (32 - 0) =
        inverseSquareSingleReverseAfter32Candidate
    simpa using
      inverseSquareSingleReverseBefore32_add_32_term_rounds_to_after32
  rw [hfirst]
  rw [show 32 - 1 = 31 by norm_num]
  rw [show 15 + 16 = 31 by norm_num]
  rw [show 31 = 15 + 16 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter32Accumulator_31_to_before16]
  rw [show 31 - 15 = 16 by norm_num]
  exact hsuffix

/-- Closing the `16^{-2}` midpoint boundary step and the following
same-exponent band reduces the archived optional concrete suffix certificate
from the before-`16` state to the boundary certificate beginning with
`8^{-2}`. -/
theorem inverseSquareSingleReverseBefore16SuffixMapsToPrinted_of_before8
    (hsuffix : inverseSquareSingleReverseBefore8SuffixMapsToPrinted) :
    inverseSquareSingleReverseBefore16SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore16Candidate 16 16 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 16 = 1 + (7 + 8) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore16Candidate 16 1 =
        inverseSquareSingleReverseAfter16Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore16Candidate (16 - 0) =
        inverseSquareSingleReverseAfter16Candidate
    simpa using
      inverseSquareSingleReverseBefore16_add_16_term_rounds_to_after16
  rw [hfirst]
  rw [show 16 - 1 = 15 by norm_num]
  rw [show 7 + 8 = 15 by norm_num]
  rw [show 15 = 7 + 8 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter16Accumulator_15_to_before8]
  rw [show 15 - 7 = 8 by norm_num]
  exact hsuffix

/-- Closing the `8^{-2}` exact boundary step and the following same-exponent
band reduces the archived optional concrete suffix certificate from the
before-`8` state to the final four explicit additions beginning with `4^{-2}`. -/
theorem inverseSquareSingleReverseBefore8SuffixMapsToPrinted_of_before4
    (hsuffix : inverseSquareSingleReverseBefore4SuffixMapsToPrinted) :
    inverseSquareSingleReverseBefore8SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore8Candidate 8 8 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 8 = 1 + (3 + 4) by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have hfirst :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore8Candidate 8 1 =
        inverseSquareSingleReverseAfter8Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore8Candidate (8 - 0) =
        inverseSquareSingleReverseAfter8Candidate
    simpa using
      inverseSquareSingleReverseBefore8_add_8_term_rounds_to_after8
  rw [hfirst]
  rw [show 8 - 1 = 7 by norm_num]
  rw [show 3 + 4 = 7 by norm_num]
  rw [show 7 = 3 + 4 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [inverseSquareSingleReverseAfter8Accumulator_7_to_before4]
  rw [show 7 - 3 = 4 by norm_num]
  exact hsuffix

/-- The final four low-index reverse additions carry the before-`4` state to
the displayed accumulator in the archived optional repository model. -/
theorem inverseSquareSingleReverseBefore4SuffixMapsToPrinted_closed :
    inverseSquareSingleReverseBefore4SuffixMapsToPrinted := by
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseBefore4Candidate 4 4 =
      inverseSquareSingleReversePrintedAccumulator
  rw [show 4 = 1 + 3 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have h4 :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseBefore4Candidate 4 1 =
        inverseSquareSingleReverseAfter4Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseBefore4Candidate (4 - 0) =
        inverseSquareSingleReverseAfter4Candidate
    simpa using
      inverseSquareSingleReverseBefore4_add_4_term_rounds_to_after4
  rw [h4]
  rw [show 4 - 1 = 3 by norm_num]
  rw [show 3 = 1 + 2 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have h3 :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter4Candidate 3 1 =
        inverseSquareSingleReverseAfter3Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseAfter4Candidate (3 - 0) =
        inverseSquareSingleReverseAfter3Candidate
    simpa using
      inverseSquareSingleReverseAfter4_add_3_term_rounds_to_after3
  rw [h3]
  rw [show 3 - 1 = 2 by norm_num]
  rw [show 2 = 1 + 1 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  have h2 :
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter3Candidate 2 1 =
        inverseSquareSingleReverseAfter2Candidate := by
    change
      inverseSquareSingleForwardStep
          inverseSquareSingleReverseAfter3Candidate (2 - 0) =
        inverseSquareSingleReverseAfter2Candidate
    simpa using
      inverseSquareSingleReverseAfter3_add_2_term_rounds_to_after2
  rw [h2]
  rw [show 2 - 1 = 1 by norm_num]
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter2Candidate 1 1 =
      inverseSquareSingleReversePrintedAccumulator
  change
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseAfter2Candidate (1 - 0) =
      inverseSquareSingleReversePrintedAccumulator
  simpa using inverseSquareSingleReverseAfter2_add_1_term_rounds_to_printed

/-- The concrete suffix certificate is closed from the before-`32` frontier. -/
theorem inverseSquareSingleReverseBefore32SuffixMapsToPrinted_closed :
    inverseSquareSingleReverseBefore32SuffixMapsToPrinted :=
  inverseSquareSingleReverseBefore32SuffixMapsToPrinted_of_before16
    (inverseSquareSingleReverseBefore16SuffixMapsToPrinted_of_before8
      (inverseSquareSingleReverseBefore8SuffixMapsToPrinted_of_before4
        inverseSquareSingleReverseBefore4SuffixMapsToPrinted_closed))

/-- The whole concrete repository-model candidate suffix trace from the named
high-prefix candidate to the displayed reverse accumulator is closed. -/
theorem inverseSquareSingleReverseCandidateSuffixMapsToPrinted_closed :
    inverseSquareSingleReverseCandidateSuffixMapsToPrinted :=
  inverseSquareSingleReverseCandidateSuffixMapsToPrinted_of_after4096
    (inverseSquareSingleReverseAfter4096SuffixMapsToPrinted_of_after4095
      (inverseSquareSingleReverseAfter4095SuffixMapsToPrinted_of_before2048
        (inverseSquareSingleReverseBefore2048SuffixMapsToPrinted_of_before1024
          (inverseSquareSingleReverseBefore1024SuffixMapsToPrinted_of_before512
            (inverseSquareSingleReverseBefore512SuffixMapsToPrinted_of_before256
              (inverseSquareSingleReverseBefore256SuffixMapsToPrinted_of_before128
                (inverseSquareSingleReverseBefore128SuffixMapsToPrinted_of_before64
                  (inverseSquareSingleReverseBefore64SuffixMapsToPrinted_of_before32
                    inverseSquareSingleReverseBefore32SuffixMapsToPrinted_closed))))))))

/-- With the concrete suffix now closed, the archived optional repository-model
displayed value is reduced solely to the high-prefix equality certificate. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_candidate
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidate_certificates
    hprefix inverseSquareSingleReverseCandidateSuffixMapsToPrinted_closed

/-- Certificate-composition theorem for the archived optional §1.12.3
repository-model reverse run.  Once the rounded high-index prefix is shown to
land in the displayed start window and the final `4096`-term suffix is shown to
map that whole window to the repository-model displayed accumulator, the full
`10^9`-term reverse accumulator equals that displayed model value. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_window_certificates
    (hprefix :
      inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow)
    (hsuffix : inverseSquareSingleReverseSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator := by
  rw [inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096]
  exact hsuffix
    inverseSquareSingleReverseTenPowNineHighPrefixState
    hprefix.1 hprefix.2

/-- Tighter-window certificate-composition theorem for the archived optional
§1.12.3 repository-model reverse run.  This whole-window route proves the
rounded high-index prefix lies in the refined start window and the final
`4096`-term suffix maps that refined window to the displayed model value. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates
    (hprefix :
      inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow)
    (hsuffix : inverseSquareSingleReverseTightSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator := by
  rw [inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096]
  exact hsuffix
    inverseSquareSingleReverseTenPowNineHighPrefixState
    hprefix.1 hprefix.2

/-- Expanded-hypothesis form of the reverse-order certificate-composition
theorem, useful when the two window inequalities are available directly rather
than through the packaged predicate. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_window
    (hlo :
      inverseSquareSingleReverseSuffixStartLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixState)
    (hhi :
      inverseSquareSingleReverseTenPowNineHighPrefixState ≤
        inverseSquareSingleReverseSuffixStartUpper)
    (hsuffix : inverseSquareSingleReverseSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_window_certificates
    ⟨hlo, hhi⟩ hsuffix

/-- Expanded-hypothesis form of the refined reverse-order certificate, useful
when the two tight-window inequalities are available directly. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_tight_window
    (hlo :
      inverseSquareSingleReverseSuffixStartLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixState)
    (hhi :
      inverseSquareSingleReverseTenPowNineHighPrefixState ≤
        inverseSquareSingleReverseSuffixStartUpperTight)
    (hsuffix : inverseSquareSingleReverseTightSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates
    ⟨hlo, hhi⟩ hsuffix

/-- If the rounded high-index prefix of the reverse `10^9` run is shown to
agree with the exact high-index prefix, then it lies in the ordinary start
window for the final `4096`-term suffix.  This isolates the remaining rounded
high-prefix trace from the already-proved exact telescoping squeeze. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_exact
    (hprefix :
      inverseSquareSingleReverseTenPowNineHighPrefixState =
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)) :
    inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow := by
  constructor
  · rw [hprefix]
    exact inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow.1
  · rw [hprefix]
    exact inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow.2

/-- Tighter-window version of
`inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_exact`. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_eq_exact
    (hprefix :
      inverseSquareSingleReverseTenPowNineHighPrefixState =
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)) :
    inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow := by
  constructor
  · rw [hprefix]
    exact inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow.1
  · rw [hprefix]
    exact inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow.2

/-- Explicit absolute-error radius around the exact high-prefix mass that is
small enough to place the rounded high-prefix state in the refined final-suffix
start window. -/
noncomputable def inverseSquareSingleReverseHighPrefixTightWindowMargin : ℝ :=
  min
    (inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) -
      inverseSquareSingleReverseSuffixStartLower)
    (inverseSquareSingleReverseSuffixStartUpperTight -
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096))

/-- The refined high-prefix margin is nonnegative because the exact
high-prefix mass lies in the refined suffix-start window. -/
theorem inverseSquareSingleReverseHighPrefixTightWindowMargin_nonneg :
    0 ≤ inverseSquareSingleReverseHighPrefixTightWindowMargin := by
  unfold inverseSquareSingleReverseHighPrefixTightWindowMargin
  apply le_min
  · exact sub_nonneg.mpr
      inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow.1
  · exact sub_nonneg.mpr
      inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow.2

/-- Fully explicit rational lower bound for
`inverseSquareSingleReverseHighPrefixTightWindowMargin`, obtained by replacing
the exact high-prefix mass with the telescoping lower and upper bounds. -/
noncomputable def inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound : ℝ :=
  min
    ((1 / (4097 : ℝ) - 1 / (((10 ^ 9 + 1 : ℕ) : ℝ))) -
      inverseSquareSingleReverseSuffixStartLower)
    (inverseSquareSingleReverseSuffixStartUpperTight - 1 / (4096 : ℝ))

/-- The explicit lower bound for the refined high-prefix margin is positive
enough to be used as a concrete future error target. -/
theorem inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_nonneg :
    0 ≤ inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound := by
  unfold inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound
  apply le_min
  · norm_num [inverseSquareSingleReverseSuffixStartLower,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  · norm_num [inverseSquareSingleReverseSuffixStartUpperTight,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- The explicit rational lower bound is below the exact refined high-prefix
margin.  This turns the remaining high-prefix trace obligation into a concrete
absolute-error inequality. -/
theorem inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_le_margin :
    inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound ≤
      inverseSquareSingleReverseHighPrefixTightWindowMargin := by
  unfold inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound
  unfold inverseSquareSingleReverseHighPrefixTightWindowMargin
  apply min_le_min
  · have htel := inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ
      (kTop := 10 ^ 9) (n := 10 ^ 9 - 4096)
      (by norm_num : (10 ^ 9 - 4096 : ℕ) ≤ (10 ^ 9 : ℕ))
    have hden : (10 ^ 9 - (10 ^ 9 - 4096) + 1 : ℕ) = 4097 := by
      norm_num
    rw [hden] at htel
    linarith
  · have hupper := inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096
    linarith

/-- Sharper shifted-telescope lower endpoint for the exact high-prefix mass.
Unlike `1/4097 - 1/(10^9+1)`, this uses a near-half shift and is within a few
ulps of the exact high-prefix sum while remaining a symbolic lower bound. -/
noncomputable def inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint : ℝ :=
  1 / ((4097 : ℝ) - (4096 : ℝ) / 8193) -
    1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193))

/-- Half-shifted upper endpoint for the exact high-prefix mass. -/
noncomputable def inverseSquareSingleReverseHighPrefixHalfUpperEndpoint : ℝ :=
  1 / ((4097 : ℝ) - (1 : ℝ) / 2) -
    1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))

/-- Stronger explicit rational lower bound for the refined high-prefix margin,
using the shifted lower and half-shifted upper telescoping squeezes. -/
noncomputable def inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound : ℝ :=
  min
    (inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
      inverseSquareSingleReverseSuffixStartLower)
    (inverseSquareSingleReverseSuffixStartUpperTight -
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint)

/-- The shifted explicit margin bound is nonnegative. -/
theorem inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound_nonneg :
    0 ≤ inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound := by
  unfold inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound
  unfold inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint
  unfold inverseSquareSingleReverseHighPrefixHalfUpperEndpoint
  apply le_min
  · norm_num [inverseSquareSingleReverseSuffixStartLower,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  · norm_num [inverseSquareSingleReverseSuffixStartUpperTight,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- The shifted explicit margin bound is below the exact refined high-prefix
margin. -/
theorem inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound_le_margin :
    inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound ≤
      inverseSquareSingleReverseHighPrefixTightWindowMargin := by
  unfold inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound
  unfold inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint
  unfold inverseSquareSingleReverseHighPrefixHalfUpperEndpoint
  unfold inverseSquareSingleReverseHighPrefixTightWindowMargin
  apply min_le_min
  · have hlower :=
      inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193
    linarith
  · have hupper := inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope
    linarith

/-- The concrete high-prefix candidate is close enough to the exact high-prefix
mass for the shifted explicit margin bound.  This is a consistency check for
the candidate route and a quantitative target for the remaining rounded-prefix
trace. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_shiftedMarginLowerBound :
    |inverseSquareSingleReverseTenPowNineHighPrefixCandidate -
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
      inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound := by
  have hlower :
      inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
    change
      1 / ((4097 : ℝ) - (4096 : ℝ) / 8193) -
          1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)) ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)
    exact inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193
  have hupper :
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
    change
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        1 / ((4097 : ℝ) - (1 : ℝ) / 2) -
          1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))
    exact inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope
  have hcand_le_lower :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint := by
    norm_num [inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have horder :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) :=
    le_trans hcand_le_lower hlower
  have habs :
      |inverseSquareSingleReverseTenPowNineHighPrefixCandidate -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| =
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) -
          inverseSquareSingleReverseTenPowNineHighPrefixCandidate := by
    rw [abs_of_nonpos (sub_nonpos.mpr horder)]
    ring
  rw [habs]
  unfold inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound
  apply le_min
  · have hnum :
        inverseSquareSingleReverseHighPrefixHalfUpperEndpoint -
            inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
          inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
            inverseSquareSingleReverseSuffixStartLower := by
      norm_num [inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
        inverseSquareSingleReverseSuffixStartLower,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    linarith
  · have hnum :
        inverseSquareSingleReverseHighPrefixHalfUpperEndpoint -
            inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
          inverseSquareSingleReverseSuffixStartUpperTight -
            inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
      norm_num [inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
        inverseSquareSingleReverseSuffixStartUpperTight,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    linarith

/-- The finite predecessor immediately below the lower endpoint of the
high-prefix candidate window. -/
noncomputable def inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16774836 - 1025) (-12 : ℤ)

/-- The finite successor immediately above the upper endpoint of the
high-prefix candidate window. -/
noncomputable def inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16774836 + 1025) (-12 : ℤ)

/-- Archived optional repository-model target for the rounded high-prefix
trace.  It is enough to place the computed high-prefix state within 1024
binary32 ulps of the observed high-prefix candidate, but this target no longer
blocks the Chapter 1 gate for the historical Fortran printout. -/
def inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow : Prop :=
  inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
      inverseSquareSingleReverseTenPowNineHighPrefixState ∧
    inverseSquareSingleReverseTenPowNineHighPrefixState ≤
      inverseSquareSingleReverseHighPrefixCandidateWindowUpper

/-- Archived optional pre-binade start-window target for the D1 high-prefix
route: the rounded earlier block `10^9, ..., 8193` must enter the window that
the closed `8192, ..., 4097` map consumes.  This is retained for a future
explicit repository-model replay only. -/
def inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow :
    Prop :=
  inverseSquareSingleReverseHighPrefixBefore8192WindowLower ≤
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ∧
    inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ≤
      inverseSquareSingleReverseHighPrefixBefore8192WindowUpper

/-- Concrete binary32 candidate for the rounded earlier high-prefix block
`10^9, ..., 8193`.  Its usual hexadecimal IEEE encoding is `0x38fff94f`.
It is named separately from the final-binade post-`8192` lower endpoint because
it is the next equality target for the remaining pre-binade proof. -/
noncomputable def inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate :
    ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 16775503 (-13 : ℤ)

/-- The rounded earlier-block candidate lies in the start window consumed by
the closed final high-binade map. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate_mem_startWindow :
    inverseSquareSingleReverseHighPrefixBefore8192WindowLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate ∧
      inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate ≤
        inverseSquareSingleReverseHighPrefixBefore8192WindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate,
      inverseSquareSingleReverseHighPrefixBefore8192WindowLower,
      inverseSquareSingleReverseHighPrefixBefore8192WindowUpper,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Equality-to-candidate form of the remaining rounded earlier-block
obligation. -/
def inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate :
    Prop :=
  inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) =
    inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate

/-- The rounded earlier-block state is an IEEE-single finite-system value. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixBefore8192State_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192)) :=
  inverseSquareSingleReverseAccumulatorFrom_finiteSystem_of_start
    (FloatingPointFormat.finiteSystem_zero FloatingPointFormat.ieeeSingleFormat)
    (10 ^ 9) (10 ^ 9 - 8192)

/-- The finite predecessor immediately below the lower endpoint of the
before-`8192` start window. -/
noncomputable def inverseSquareSingleReverseHighPrefixBefore8192WindowLowerPred :
    ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16773455 - 1) (-13 : ℤ)

/-- The finite successor immediately above the upper endpoint of the
before-`8192` start window. -/
noncomputable def inverseSquareSingleReverseHighPrefixBefore8192WindowUpperSucc :
    ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8388776 + 1) (-12 : ℤ)

/-- Strict finite-cell guard for the rounded earlier-block state.  Since the
state is finite, these two strict inequalities force membership in the closed
before-`8192` start window. -/
def inverseSquareSingleReverseTenPowNineHighPrefixBefore8192StartWindowCellGuard :
    Prop :=
  inverseSquareSingleReverseHighPrefixBefore8192WindowLowerPred <
      inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ∧
    inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) <
      inverseSquareSingleReverseHighPrefixBefore8192WindowUpperSucc

/-- Equality with the observed before-`8192` candidate implies the strict
finite-cell guard for the earlier-block start window. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixBefore8192StartWindowCellGuard_of_eq_candidate
    (hpre :
      inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate) :
    inverseSquareSingleReverseTenPowNineHighPrefixBefore8192StartWindowCellGuard := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate at hpre
  unfold inverseSquareSingleReverseTenPowNineHighPrefixBefore8192StartWindowCellGuard
  rw [hpre]
  constructor <;>
    norm_num [inverseSquareSingleReverseHighPrefixBefore8192WindowLowerPred,
      inverseSquareSingleReverseHighPrefixBefore8192WindowUpperSucc,
      inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Finite-cell route for the remaining earlier-block start-window obligation:
once the actual rounded `10^9, ..., 8193` state is strictly between the finite
predecessor of the lower endpoint and the finite successor of the upper
endpoint, finite-grid adjacency forces it into the closed start window consumed
by the final high-prefix binade map. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow_of_cellGuard
    (hguard :
      inverseSquareSingleReverseTenPowNineHighPrefixBefore8192StartWindowCellGuard) :
    inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192)) := by
    exact inverseSquareSingleReverseTenPowNineHighPrefixBefore8192State_finiteSystem
  have hpredSystem :
      fmt.normalizedSystem
        inverseSquareSingleReverseHighPrefixBefore8192WindowLowerPred := by
    refine ⟨false, 16773455 - 1, (-13 : ℤ), ?_, ?_, rfl⟩ <;>
      norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.exponentInRange]
  have hupperSystem :
      fmt.normalizedSystem
        inverseSquareSingleReverseHighPrefixBefore8192WindowUpper := by
    refine ⟨false, 8388776, (-12 : ℤ), ?_, ?_, rfl⟩ <;>
      norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.exponentInRange]
  have hlowerAdj :
      fmt.realOrderAdjacentNormalized
        inverseSquareSingleReverseHighPrefixBefore8192WindowLowerPred
        inverseSquareSingleReverseHighPrefixBefore8192WindowLower := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 16773455 - 1, (-13 : ℤ), ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [inverseSquareSingleReverseHighPrefixBefore8192WindowLower,
        fmt]
  have hupperAdj :
      fmt.realOrderAdjacentNormalized
        inverseSquareSingleReverseHighPrefixBefore8192WindowUpper
        inverseSquareSingleReverseHighPrefixBefore8192WindowUpperSucc := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 8388776, (-12 : ℤ), ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
  have hpred_pos :
      0 < inverseSquareSingleReverseHighPrefixBefore8192WindowLowerPred := by
    norm_num [inverseSquareSingleReverseHighPrefixBefore8192WindowLowerPred,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hupper_pos :
      0 < inverseSquareSingleReverseHighPrefixBefore8192WindowUpper := by
    norm_num [inverseSquareSingleReverseHighPrefixBefore8192WindowUpper,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  unfold inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow
  constructor
  · by_contra hnot
    have hlt :
        inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) <
          inverseSquareSingleReverseHighPrefixBefore8192WindowLower :=
      lt_of_not_ge hnot
    have hle_pred :
        inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) ≤
          inverseSquareSingleReverseHighPrefixBefore8192WindowLowerPred :=
      fmt.finiteSystem_lt_right_adjacent_le_left
        hfin hpredSystem hlowerAdj hpred_pos hlt
    exact not_lt_of_ge hle_pred hguard.1
  · by_contra hnot
    have hlt :
        inverseSquareSingleReverseHighPrefixBefore8192WindowUpper <
          inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) :=
      lt_of_not_ge hnot
    have hsucc_le :
        inverseSquareSingleReverseHighPrefixBefore8192WindowUpperSucc ≤
          inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192) :=
      fmt.right_adjacent_le_finiteSystem_of_left_lt
        hfin hupperSystem hupperAdj hupper_pos hlt
    exact not_lt_of_ge hsucc_le hguard.2

/-- The concrete equality route closes the rounded earlier-block start-window
obligation. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow_of_eq_candidate
    (hpre :
      inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate) :
    inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow
  unfold inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate at hpre
  rw [hpre]
  exact inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate_mem_startWindow

/-- The closed final-binade window map reduces high-prefix candidate-window
membership to the single rounded earlier-block start-window obligation. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_before8192StartWindow
    (hpre :
      inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow
  rw [inverseSquareSingleReverseTenPowNineHighPrefixState_split_8192]
  exact inverseSquareSingleReverseHighBinade8192To4097WindowMapsToCandidate_closed
    (inverseSquareSingleReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 8192))
    hpre.1 hpre.2

/-- Before-`8192` finite-cell route composed with the closed final high-prefix
binade map: proving the strict predecessor/successor guard for the rounded
earlier block is enough to place the full rounded high prefix in the candidate
window. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_before8192StartWindowCellGuard
    (hguard :
      inverseSquareSingleReverseTenPowNineHighPrefixBefore8192StartWindowCellGuard) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_before8192StartWindow
    (inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow_of_cellGuard
      hguard)

/-- Strict real-valued cell guard around the candidate window.  Because the
rounded high-prefix state is already known to be an IEEE-single finite-system
value, these two strict inequalities are enough to force membership in the
closed 1024-ulp candidate window. -/
def inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard :
    Prop :=
  inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred <
      inverseSquareSingleReverseTenPowNineHighPrefixState ∧
    inverseSquareSingleReverseTenPowNineHighPrefixState <
      inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc

/-- The observed high-prefix candidate is centered in the concrete
candidate window. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_candidateWindow :
    inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate ∧
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLower,
      inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- The equality-to-candidate route implies the strict finite-cell guard around
the candidate window. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_eq_candidate
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate) :
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard := by
  rw [inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate] at hprefix
  unfold inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard
  rw [hprefix]
  constructor <;>
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred,
      inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc,
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- The exact high-index reverse prefix lies in the concrete 1024-ulp
candidate window.  This keeps the remaining rounded-prefix task centered on a
small binary32 interval, rather than the wider suffix-start window. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow :
    inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ∧
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
          inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint := by
      norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLower,
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact le_trans hwindow
      inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193
  · have hwindow :
        inverseSquareSingleReverseHighPrefixHalfUpperEndpoint ≤
          inverseSquareSingleReverseHighPrefixCandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
        inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact le_trans inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope
      hwindow

/-- The exact high-index reverse prefix lies strictly inside the predecessor /
successor finite-cell guard around the concrete candidate window.  This is the
non-vacuity check for the strict-cell high-prefix route; the remaining
operation-trace obligation is to place the rounded high-prefix state in the
same strict cell. -/
theorem inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindowCellGuard :
    inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred <
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ∧
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) <
        inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc := by
  constructor
  · have hpred_lt_lower :
        inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred <
          inverseSquareSingleReverseHighPrefixCandidateWindowLower := by
      norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred,
        inverseSquareSingleReverseHighPrefixCandidateWindowLower,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact lt_of_lt_of_le hpred_lt_lower
      inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow.1
  · have hupper_lt_succ :
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper <
          inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc := by
      norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
        inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact lt_of_le_of_lt
      inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow.2
      hupper_lt_succ

/-- Exact margin around the exact high-prefix mass that is sufficient to place
the rounded high-prefix state in the concrete candidate window. -/
noncomputable def inverseSquareSingleReverseHighPrefixCandidateWindowMargin : ℝ :=
  min
    (inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) -
      inverseSquareSingleReverseHighPrefixCandidateWindowLower)
    (inverseSquareSingleReverseHighPrefixCandidateWindowUpper -
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096))

/-- The candidate-window margin is nonnegative because the exact high-prefix
mass lies in the candidate window. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindowMargin_nonneg :
    0 ≤ inverseSquareSingleReverseHighPrefixCandidateWindowMargin := by
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowMargin
  apply le_min
  · exact sub_nonneg.mpr
      inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow.1
  · exact sub_nonneg.mpr
      inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow.2

/-- Archived optional absolute-error route for the rounded high-prefix trace:
if the rounded high-prefix state is within the exact candidate-window margin of
the exact high-prefix mass, then it lies in the concrete candidate window. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_le_candidateWindowMargin
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowMargin) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow := by
  have hmargin_le_lower :
      inverseSquareSingleReverseHighPrefixCandidateWindowMargin ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) -
          inverseSquareSingleReverseHighPrefixCandidateWindowLower := by
    unfold inverseSquareSingleReverseHighPrefixCandidateWindowMargin
    exact min_le_left _ _
  have hmargin_le_upper :
      inverseSquareSingleReverseHighPrefixCandidateWindowMargin ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper -
          inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
    unfold inverseSquareSingleReverseHighPrefixCandidateWindowMargin
    exact min_le_right _ _
  have hbounds := abs_le.mp herr
  constructor
  · have hstate_ge :
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) -
            inverseSquareSingleReverseHighPrefixCandidateWindowMargin ≤
          inverseSquareSingleReverseTenPowNineHighPrefixState := by
      linarith [hbounds.1]
    linarith [hmargin_le_lower, hstate_ge]
  · have hstate_le :
        inverseSquareSingleReverseTenPowNineHighPrefixState ≤
          inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) +
            inverseSquareSingleReverseHighPrefixCandidateWindowMargin := by
      linarith [hbounds.2]
    linarith [hmargin_le_upper, hstate_le]

/-- Fully explicit shifted-telescope lower bound for the candidate-window
margin.  This is the concrete absolute-error target left for the rounded
high-prefix trace. -/
noncomputable def inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound : ℝ :=
  min
    (inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
      inverseSquareSingleReverseHighPrefixCandidateWindowLower)
    (inverseSquareSingleReverseHighPrefixCandidateWindowUpper -
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint)

/-- The shifted candidate-window margin target is nonnegative. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_nonneg :
    0 ≤ inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound := by
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound
  unfold inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint
  unfold inverseSquareSingleReverseHighPrefixHalfUpperEndpoint
  apply le_min
  · norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLower,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  · norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- The shifted explicit candidate-window margin lies below the exact
candidate-window margin. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_le_margin :
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound ≤
      inverseSquareSingleReverseHighPrefixCandidateWindowMargin := by
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowMargin
  apply min_le_min
  · have hlower :
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint ≤
          inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
      change
        1 / ((4097 : ℝ) - (4096 : ℝ) / 8193) -
            1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)) ≤
          inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)
      exact inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193
    exact sub_le_sub_right hlower _
  · have hupper :
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
          inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
      change
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
          1 / ((4097 : ℝ) - (1 : ℝ) / 2) -
            1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))
      exact inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope
    exact sub_le_sub_left hupper _

/-- Fully explicit shifted-telescope lower bound for the strict finite-cell
guard around the candidate window.  It uses the predecessor and successor
finite cells rather than the closed candidate-window endpoints. -/
noncomputable def inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound :
    ℝ :=
  min
    (inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
      inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred)
    (inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc -
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint)

/-- The shifted finite-cell margin target is nonnegative. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_nonneg :
    0 ≤
      inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound := by
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound
  unfold inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint
  unfold inverseSquareSingleReverseHighPrefixHalfUpperEndpoint
  apply le_min
  · norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  · norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- The closed-window shifted margin is bounded by the larger strict-cell
shifted margin. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_le_cellGuardMarginShiftedLowerBound :
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound ≤
      inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound := by
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound
  apply min_le_min
  · have hpred_le_lower :
        inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred ≤
          inverseSquareSingleReverseHighPrefixCandidateWindowLower := by
      norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLower,
        inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact sub_le_sub_left hpred_le_lower _
  · have hupper_le_succ :
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper ≤
          inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc := by
      norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
        inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact sub_le_sub_right hupper_le_succ _

/-- The strict finite-cell margin is genuinely larger than the closed
candidate-window shifted margin. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_lt_cellGuardMarginShiftedLowerBound :
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound <
      inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound := by
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound
  have hold :
      inverseSquareSingleReverseHighPrefixCandidateWindowUpper -
          inverseSquareSingleReverseHighPrefixHalfUpperEndpoint ≤
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
          inverseSquareSingleReverseHighPrefixCandidateWindowLower := by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
      inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
      inverseSquareSingleReverseHighPrefixCandidateWindowLower,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hcell :
      inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc -
          inverseSquareSingleReverseHighPrefixHalfUpperEndpoint ≤
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
          inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred := by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc,
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
      inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
      inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  rw [min_eq_right hold, min_eq_right hcell]
  have hupper_lt_succ :
      inverseSquareSingleReverseHighPrefixCandidateWindowUpper <
        inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc := by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
      inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  exact sub_lt_sub_right hupper_lt_succ _

/-- The strict finite-cell margin has positive radius, so the strict-cell D1
target is not vacuous. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_pos :
    0 <
      inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound :=
  lt_of_le_of_lt
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_nonneg
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_lt_cellGuardMarginShiftedLowerBound

/-- The larger finite-cell D1 margin is still much smaller than the coarse
`1/4096` increment budget for the final high-prefix binade.  Thus the `8192`
split bounds are structural interval data, not a closing proof of D1 by
themselves. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_lt_inv_4096 :
    inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound <
      1 / (4096 : ℝ) := by
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound
  exact lt_of_le_of_lt (min_le_right _ _) (by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc,
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg])

/-- Archived optional D1 target for the reverse high-prefix trace: the rounded
high-prefix state is within the explicit shifted candidate-window margin around
the exact high-prefix mass.  It is not an active Chapter 1 gate target for the
under-specified historical printed decimal. -/
def inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget : Prop :=
  |inverseSquareSingleReverseTenPowNineHighPrefixState -
    inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound

/-- Archived optional strict-cell D1 target: the rounded high-prefix state is
within the larger predecessor/successor-cell margin around the exact high-prefix
mass.  This remains lookup material for a fully specified repository-model
replay, not a historical-output obligation. -/
def inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget :
    Prop :=
  |inverseSquareSingleReverseTenPowNineHighPrefixState -
    inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| <
    inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound

/-- Strict absolute-error route into the finite-cell guard.  This packages the
remaining high-prefix proof as one sharp interval target around the exact
high-prefix mass. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_abs_error_lt_cellGuardMarginShiftedLowerBound
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| <
        inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound) :
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard := by
  have hmargin_le_lower :
      inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) -
          inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred := by
    have hshift_le_exact :
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint ≤
          inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
      change
        1 / ((4097 : ℝ) - (4096 : ℝ) / 8193) -
            1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)) ≤
          inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)
      exact inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193
    unfold inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound
    exact le_trans (min_le_left _ _) (sub_le_sub_right hshift_le_exact _)
  have hmargin_le_upper :
      inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc -
          inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
    have hexact_le_half :
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
          inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
      change
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
          1 / ((4097 : ℝ) - (1 : ℝ) / 2) -
            1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))
      exact inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope
    unfold inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound
    exact le_trans (min_le_right _ _) (sub_le_sub_left hexact_le_half _)
  have hbounds := abs_lt.mp herr
  unfold inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard
  constructor <;> linarith

/-- Named-target version of the strict finite-cell route. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_cellGuardMarginTarget
    (htarget :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget) :
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard :=
  inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_abs_error_lt_cellGuardMarginShiftedLowerBound
    htarget

/-- The older closed-window margin target implies the strict finite-cell margin
target because the finite-cell radius is strictly larger. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_candidateWindowMarginTarget
    (htarget :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget) :
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget
  unfold inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget at htarget
  exact lt_of_le_of_lt htarget
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_lt_cellGuardMarginShiftedLowerBound

/-- Equality with the exact high-prefix mass implies the strict finite-cell
margin target.  This complements the existing candidate-equality route and
records that the strict target has real room around the exact prefix. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_eq_exact
    (hprefix :
      inverseSquareSingleReverseTenPowNineHighPrefixState =
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)) :
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget
  rw [hprefix]
  rw [sub_self, abs_zero]
  exact inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_pos

/-- Route guard for D1: the generic recursive-summation `gamma (n-1)` theorem
cannot be instantiated for the `10^9 - 4096` high-prefix serial sum at IEEE
single unit roundoff.  The remaining high-prefix proof must therefore use a
local interval/window or nearest-cell certificate, not a blanket
`gammaValid` recursive-sum bound. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaGuard_not_valid :
    ¬ (((((10 ^ 9 - 4096) - 1 : ℕ) : ℝ) *
          (2 ^ (-24 : ℤ) : ℝ)) < 1) := by
  norm_num [zpow_neg]

/-- `gammaValid` form of the D1 route guard: any abstract model whose unit
roundoff is IEEE single's `2^-24` fails the recursive-summation validity guard
for the `10^9 - 4096` high-prefix length. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaValid_not_valid
    {fp : FPModel} (hu : fp.u = (2 ^ (-24 : ℤ) : ℝ)) :
    ¬ gammaValid fp (((10 ^ 9 - 4096) - 1 : ℕ)) := by
  unfold gammaValid
  rw [hu]
  exact inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaGuard_not_valid

/-- The uniform coarse local-error bound from the standard-model adapter is
larger than the explicit candidate-window margin after summing over the whole
`10^9 - 4096` high-prefix length.  Thus that coarse envelope is a route guard,
not a closing proof of D1. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginShiftedLowerBound_lt_coarseAccumulatedStdError :
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound <
      (((10 ^ 9 - 4096 : ℕ) : ℝ) *
        FloatingPointFormat.ieeeSingleFormat.unitRoundoff *
          (1 / (2048 : ℝ) + 1 / (2 : ℝ) ^ 24)) := by
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound
  exact lt_of_le_of_lt (min_le_left _ _) (by
    norm_num [inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
      inverseSquareSingleReverseHighPrefixCandidateWindowLower,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.unitRoundoff,
      FloatingPointFormat.machineEpsilon,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg])

/-- Negated guard form of the preceding comparison: the coarse accumulated
standard-model envelope cannot be used directly as the candidate-window margin
target. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefix_coarseAccumulatedStdErrorGuard_not_sufficient :
    ¬ ((((10 ^ 9 - 4096 : ℕ) : ℝ) *
        FloatingPointFormat.ieeeSingleFormat.unitRoundoff *
          (1 / (2048 : ℝ) + 1 / (2 : ℝ) ^ 24)) ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound) := by
  exact not_le_of_gt
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginShiftedLowerBound_lt_coarseAccumulatedStdError

/-- The observed high-prefix candidate is within the explicit shifted
candidate-window margin around the exact high-prefix mass.  This checks that
the archived optional D1 error target is centered on the observed binary32
state, not merely on the wider suffix-start interval. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_candidateWindowMarginShiftedLowerBound :
    |inverseSquareSingleReverseTenPowNineHighPrefixCandidate -
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
      inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound := by
  have hlower :
      inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
    change
      1 / ((4097 : ℝ) - (4096 : ℝ) / 8193) -
          1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)) ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)
    exact inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193
  have hupper :
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
    change
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        1 / ((4097 : ℝ) - (1 : ℝ) / 2) -
          1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))
    exact inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope
  have hcand_le_lower :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint := by
    norm_num [inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have horder :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) :=
    le_trans hcand_le_lower hlower
  have habs :
      |inverseSquareSingleReverseTenPowNineHighPrefixCandidate -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| =
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) -
          inverseSquareSingleReverseTenPowNineHighPrefixCandidate := by
    rw [abs_of_nonpos (sub_nonpos.mpr horder)]
    ring
  rw [habs]
  unfold inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound
  apply le_min
  · have hnum :
        inverseSquareSingleReverseHighPrefixHalfUpperEndpoint -
            inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
          inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
            inverseSquareSingleReverseHighPrefixCandidateWindowLower := by
      norm_num [inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
        inverseSquareSingleReverseHighPrefixCandidateWindowLower,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    linarith
  · have hnum :
        inverseSquareSingleReverseHighPrefixHalfUpperEndpoint -
            inverseSquareSingleReverseTenPowNineHighPrefixCandidate ≤
          inverseSquareSingleReverseHighPrefixCandidateWindowUpper -
            inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
      norm_num [inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
        inverseSquareSingleReverseTenPowNineHighPrefixCandidate,
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    linarith

/-- The old equality-to-candidate route implies the named high-prefix margin
target.  The remaining work is therefore to prove this target for the actual
rounded high-prefix state, possibly by a chunk/window certificate, rather than
by replaying the low-index suffix. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_eq_candidate
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate) :
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget := by
  rw [inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate] at hprefix
  unfold inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget
  rw [hprefix]
  exact
    inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_candidateWindowMarginShiftedLowerBound

/-- The observed high-prefix candidate satisfies the strict finite-cell margin
target around the exact high-prefix mass. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_lt_cellGuardMarginShiftedLowerBound :
    |inverseSquareSingleReverseTenPowNineHighPrefixCandidate -
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| <
      inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound :=
  lt_of_le_of_lt
    inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_candidateWindowMarginShiftedLowerBound
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_lt_cellGuardMarginShiftedLowerBound

/-- Equality with the observed high-prefix candidate implies the strict
finite-cell margin target. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_eq_candidate
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate) :
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget :=
  inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_candidateWindowMarginTarget
    (inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_eq_candidate
      hprefix)

/-- Archived optional absolute-error route for the rounded high-prefix trace:
the shifted candidate-window margin target is enough to prove membership in the
candidate window. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_le_candidateWindowMarginShiftedLowerBound
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_le_candidateWindowMargin
    (le_trans herr
      inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_le_margin)

/-- Named-target version of the candidate-window bridge for D1. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_candidateWindowMarginTarget
    (htarget :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_le_candidateWindowMarginShiftedLowerBound
    htarget

/-- Equality with the exact high-index prefix is enough to place the rounded
high-prefix state in the concrete candidate window. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_eq_exact
    (hprefix :
      inverseSquareSingleReverseTenPowNineHighPrefixState =
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow := by
  change
    inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixState ∧
      inverseSquareSingleReverseTenPowNineHighPrefixState ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper
  rw [hprefix]
  exact inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow

/-- Equality with the observed candidate is enough to place the rounded
high-prefix state in the concrete candidate window. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_eq_candidate
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow := by
  rw [inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate] at hprefix
  change
    inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
        inverseSquareSingleReverseTenPowNineHighPrefixState ∧
      inverseSquareSingleReverseTenPowNineHighPrefixState ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper
  rw [hprefix]
  exact inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_candidateWindow

/-- The concrete candidate window is a subwindow of the refined final-suffix
start window. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindow_mem_printedSuffixStartTightWindow
    {s : ℝ}
    (hlo : inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseHighPrefixCandidateWindowUpper) :
    inverseSquareSingleReverseSuffixStartLower ≤ s ∧
      s ≤ inverseSquareSingleReverseSuffixStartUpperTight := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseSuffixStartLower ≤
          inverseSquareSingleReverseHighPrefixCandidateWindowLower := by
      norm_num [inverseSquareSingleReverseSuffixStartLower,
        inverseSquareSingleReverseHighPrefixCandidateWindowLower,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact le_trans hwindow hlo
  · have hwindow :
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper ≤
          inverseSquareSingleReverseSuffixStartUpperTight := by
      norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
        inverseSquareSingleReverseSuffixStartUpperTight,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    exact le_trans hhi hwindow

/-- Narrowed final-suffix certificate: every start in the concrete high-prefix
candidate window maps, after the final `4096` reverse additions, to the
displayed accumulator in the archived optional repository model. -/
def inverseSquareSingleReverseCandidateWindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseHighPrefixCandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 4096 4096 =
          inverseSquareSingleReversePrintedAccumulator

/-- The older tight suffix-window map implies the narrower candidate-window
suffix map.  Future work may prove the narrower certificate directly. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_tightSuffixWindow
    (hsuffix : inverseSquareSingleReverseTightSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted := by
  intro start hlo hhi
  have hwin :=
    inverseSquareSingleReverseHighPrefixCandidateWindow_mem_printedSuffixStartTightWindow
      hlo hhi
  exact hsuffix start hwin.1 hwin.2

/-- Lower endpoint of the post-`4096^{-2}` candidate window.  The initial
1024-ulp high-prefix window shifts by the exact `4096^{-2}` term into a
512-ulp window at the next binary32 exponent. -/
noncomputable def inverseSquareSingleReverseAfter4096CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8389466 - 512) (-11 : ℤ)

/-- Upper endpoint of the post-`4096^{-2}` candidate window. -/
noncomputable def inverseSquareSingleReverseAfter4096CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8389466 + 512) (-11 : ℤ)

/-- The named after-`4096` candidate is centered in the post-step window. -/
theorem inverseSquareSingleReverseAfter4096Candidate_mem_after4096Window :
    inverseSquareSingleReverseAfter4096CandidateWindowLower ≤
        inverseSquareSingleReverseAfter4096Candidate ∧
      inverseSquareSingleReverseAfter4096Candidate ≤
        inverseSquareSingleReverseAfter4096CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter4096CandidateWindowLower,
      inverseSquareSingleReverseAfter4096CandidateWindowUpper,
      inverseSquareSingleReverseAfter4096Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by the first low-index suffix term maps the whole
high-prefix candidate window into the post-`4096` candidate window.  This is a
compact interval step, not a pointwise suffix enumeration. -/
theorem inverseSquareSingleReverseCandidateWindow_add_4096_term_mem_after4096Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseHighPrefixCandidateWindowUpper) :
    inverseSquareSingleReverseAfter4096CandidateWindowLower ≤
        s + inverseSquareTerm 4096 ∧
      s + inverseSquareTerm 4096 ≤
        inverseSquareSingleReverseAfter4096CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter4096CandidateWindowLower ≤
          inverseSquareSingleReverseHighPrefixCandidateWindowLower +
            inverseSquareTerm 4096 := by
      norm_num [inverseSquareSingleReverseAfter4096CandidateWindowLower,
        inverseSquareSingleReverseHighPrefixCandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseHighPrefixCandidateWindowLower +
            inverseSquareTerm 4096 ≤
          s + inverseSquareTerm 4096 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper +
            inverseSquareTerm 4096 ≤
          inverseSquareSingleReverseAfter4096CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
        inverseSquareSingleReverseAfter4096CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 4096 ≤
          inverseSquareSingleReverseHighPrefixCandidateWindowUpper +
            inverseSquareTerm 4096 := by
      linarith
    exact le_trans hstep hwindow

/-- Finite-cell route for D1: once the actual rounded high-prefix state is
strictly between the predecessor of the lower candidate-window endpoint and the
successor of the upper endpoint, finite-grid adjacency forces it into the
closed candidate window. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuard
    (hguard :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hfin :
      fmt.finiteSystem inverseSquareSingleReverseTenPowNineHighPrefixState := by
    simpa [fmt] using
      inverseSquareSingleReverseTenPowNineHighPrefixState_finiteSystem
  have hpredSystem :
      fmt.normalizedSystem
        inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred := by
    refine ⟨false, 16774836 - 1025, (-12 : ℤ), ?_, ?_, rfl⟩ <;>
      norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.exponentInRange]
  have hupperSystem :
      fmt.normalizedSystem
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper := by
    refine ⟨false, 16774836 + 1024, (-12 : ℤ), ?_, ?_, rfl⟩ <;>
      norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.exponentInRange]
  have hlowerAdj :
      fmt.realOrderAdjacentNormalized
        inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred
        inverseSquareSingleReverseHighPrefixCandidateWindowLower := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 16774836 - 1025, (-12 : ℤ), ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLower,
        fmt]
  have hupperAdj :
      fmt.realOrderAdjacentNormalized
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper
        inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, 16774836 + 1024, (-12 : ℤ), ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
  have hpred_pos :
      0 < inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred := by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hupper_pos :
      0 < inverseSquareSingleReverseHighPrefixCandidateWindowUpper := by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  constructor
  · by_contra hnot
    have hlt :
        inverseSquareSingleReverseTenPowNineHighPrefixState <
          inverseSquareSingleReverseHighPrefixCandidateWindowLower :=
      lt_of_not_ge hnot
    have hle_pred :
        inverseSquareSingleReverseTenPowNineHighPrefixState ≤
          inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred :=
      fmt.finiteSystem_lt_right_adjacent_le_left
        hfin hpredSystem hlowerAdj hpred_pos hlt
    exact not_lt_of_ge hle_pred hguard.1
  · by_contra hnot
    have hlt :
        inverseSquareSingleReverseHighPrefixCandidateWindowUpper <
          inverseSquareSingleReverseTenPowNineHighPrefixState :=
      lt_of_not_ge hnot
    have hsucc_le :
        inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc ≤
          inverseSquareSingleReverseTenPowNineHighPrefixState :=
      fmt.right_adjacent_le_finiteSystem_of_left_lt
        hfin hupperSystem hupperAdj hupper_pos hlt
    exact not_lt_of_ge hsucc_le hguard.2

/-- Strict absolute-error route to candidate-window membership through the
finite-cell guard. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_lt_cellGuardMarginShiftedLowerBound
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| <
        inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuard
    (inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_abs_error_lt_cellGuardMarginShiftedLowerBound
      herr)

/-- Named-target version of the strict finite-cell candidate-window bridge. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuardMarginTarget
    (htarget :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_lt_cellGuardMarginShiftedLowerBound
    htarget

/-- Standard-envelope route to the named candidate-window D1 target: a sharp
bound on the accumulated high-prefix standard-model envelope would place the
actual rounded high-prefix state within the explicit shifted candidate-window
margin. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_stdErrorEnvelope_le
    (henv :
      inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope
          (10 ^ 9 - 4096) ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound) :
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget
  exact le_trans
    inverseSquareSingleReverseTenPowNineHighPrefixState_abs_error_le_stdErrorEnvelope
    henv

/-- Standard-envelope route to the strict finite-cell D1 target.  The
remaining hard work is a sharpened whole-prefix envelope bound, not a low-index
suffix replay. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_stdErrorEnvelope_lt
    (henv :
      inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope
          (10 ^ 9 - 4096) <
        inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound) :
    inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget := by
  unfold inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget
  exact lt_of_le_of_lt
    inverseSquareSingleReverseTenPowNineHighPrefixState_abs_error_le_stdErrorEnvelope
    henv

/-- A sharpened standard-envelope bound against the explicit candidate-window
margin is sufficient for high-prefix candidate-window membership. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_le_candidateWindowMargin
    (henv :
      inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope
          (10 ^ 9 - 4096) ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_candidateWindowMarginTarget
    (inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_stdErrorEnvelope_le
      henv)

/-- A sharpened standard-envelope bound against the larger strict finite-cell
margin is sufficient for high-prefix candidate-window membership. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_lt_cellGuardMargin
    (henv :
      inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope
          (10 ^ 9 - 4096) <
        inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound) :
    inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuardMarginTarget
    (inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_stdErrorEnvelope_lt
      henv)

/-- Rounded addition by the first low-index suffix term also remains in the
post-`4096` candidate window.  The proof uses nearest-finite endpoint
enclosure, so it is still a whole-window theorem rather than a suffix case
split. -/
theorem inverseSquareSingleReverseCandidateWindow_round_4096_step_mem_after4096Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseHighPrefixCandidateWindowUpper) :
    inverseSquareSingleReverseAfter4096CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 4096 ∧
      inverseSquareSingleForwardStep s 4096 ≤
        inverseSquareSingleReverseAfter4096CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseCandidateWindow_add_4096_term_mem_after4096Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter4096CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8389466 - 512, (-11 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter4096CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8389466 + 512, (-11 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 4096)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 4096)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 4096)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-first-step form of the archived optional candidate-window suffix
certificate: every start in the post-`4096` window maps, after the remaining
`4095` low-index reverse additions, to the displayed model accumulator. -/
def inverseSquareSingleReverseAfter4096WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter4096CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter4096CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 4095 4095 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`4096` whole-window suffix certificate implies the original
candidate-window suffix certificate.  The first rounded step is discharged by
the interval enclosure above, then the remaining suffix starts from the
post-`4096` window. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (hsuffix : inverseSquareSingleReverseAfter4096WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter4096CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 4096 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 4096 1 ≤
          inverseSquareSingleReverseAfter4096CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseCandidateWindow_round_4096_step_mem_after4096Window
        hlo hhi
  rw [show 4096 = 1 + 4095 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 4096 - 1 = 4095 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 4096 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint of the post-`4095^{-2}` whole-window suffix state. -/
noncomputable def inverseSquareSingleReverseAfter4095CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8391515 - 512) (-11 : ℤ)

/-- Upper endpoint of the post-`4095^{-2}` whole-window suffix state.  The
upper side keeps one extra ulp because `4095^{-2}` is slightly larger than
2049 ulps in this binary32 exponent band. -/
noncomputable def inverseSquareSingleReverseAfter4095CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8391515 + 513) (-11 : ℤ)

/-- The named after-`4095` candidate lies in the post-`4095` window. -/
theorem inverseSquareSingleReverseAfter4095Candidate_mem_after4095Window :
    inverseSquareSingleReverseAfter4095CandidateWindowLower ≤
        inverseSquareSingleReverseAfter4095Candidate ∧
      inverseSquareSingleReverseAfter4095Candidate ≤
        inverseSquareSingleReverseAfter4095CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter4095CandidateWindowLower,
      inverseSquareSingleReverseAfter4095CandidateWindowUpper,
      inverseSquareSingleReverseAfter4095Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `4095^{-2}` maps the post-`4096` window into the
post-`4095` exact enclosure. -/
theorem inverseSquareSingleReverseAfter4096Window_add_4095_term_mem_after4095Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseAfter4096CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseAfter4096CandidateWindowUpper) :
    inverseSquareSingleReverseAfter4095CandidateWindowLower ≤
        s + inverseSquareTerm 4095 ∧
      s + inverseSquareTerm 4095 ≤
        inverseSquareSingleReverseAfter4095CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter4095CandidateWindowLower ≤
          inverseSquareSingleReverseAfter4096CandidateWindowLower +
            inverseSquareTerm 4095 := by
      norm_num [inverseSquareSingleReverseAfter4095CandidateWindowLower,
        inverseSquareSingleReverseAfter4096CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseAfter4096CandidateWindowLower +
            inverseSquareTerm 4095 ≤
          s + inverseSquareTerm 4095 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseAfter4096CandidateWindowUpper +
            inverseSquareTerm 4095 ≤
          inverseSquareSingleReverseAfter4095CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseAfter4096CandidateWindowUpper,
        inverseSquareSingleReverseAfter4095CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 4095 ≤
          inverseSquareSingleReverseAfter4096CandidateWindowUpper +
            inverseSquareTerm 4095 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `4095^{-2}` maps every post-`4096` start into the
post-`4095` whole-window suffix state. -/
theorem inverseSquareSingleReverseAfter4096Window_round_4095_step_mem_after4095Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseAfter4096CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseAfter4096CandidateWindowUpper) :
    inverseSquareSingleReverseAfter4095CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 4095 ∧
      inverseSquareSingleForwardStep s 4095 ≤
        inverseSquareSingleReverseAfter4095CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseAfter4096Window_add_4095_term_mem_after4095Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter4095CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8391515 - 512, (-11 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter4095CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8391515 + 513, (-11 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 4095)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 4095)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 4095)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-second-step form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter4095WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter4095CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter4095CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 4094 4094 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`4095` whole-window suffix certificate implies the post-`4096`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
    (hsuffix : inverseSquareSingleReverseAfter4095WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4096WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter4095CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 4095 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 4095 1 ≤
          inverseSquareSingleReverseAfter4095CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseAfter4096Window_round_4095_step_mem_after4095Window
        hlo hhi
  rw [show 4095 = 1 + 4094 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 4095 - 1 = 4094 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 4095 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `2048^{-2}`
boundary step, after the `4094^{-2}, ..., 2049^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore2048CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16772943 - 512) (-11 : ℤ)

/-- Upper endpoint for the whole-window state just before the `2048^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore2048CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16772943 + 513) (-11 : ℤ)

/-- The concrete before-`2048` candidate lies in the before-`2048`
whole-window target. -/
theorem inverseSquareSingleReverseBefore2048Candidate_mem_before2048Window :
    inverseSquareSingleReverseBefore2048CandidateWindowLower ≤
        inverseSquareSingleReverseBefore2048Candidate ∧
      inverseSquareSingleReverseBefore2048Candidate ≤
        inverseSquareSingleReverseBefore2048CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore2048CandidateWindowLower,
      inverseSquareSingleReverseBefore2048CandidateWindowUpper,
      inverseSquareSingleReverseBefore2048Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after `n` additions inside the `4094^{-2}, ..., 2049^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter4095BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8391515 - 512) +
      inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n) (-11 : ℤ)

/-- Upper endpoint after `n` additions inside the `4094^{-2}, ..., 2049^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter4095BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8391515 + 513) +
      inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n) (-11 : ℤ)

theorem inverseSquareSingleReverseAfter4095BandWindowLower_zero :
    inverseSquareSingleReverseAfter4095BandWindowLower 0 =
      inverseSquareSingleReverseAfter4095CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter4095BandWindowLower,
    inverseSquareSingleReverseAfter4095CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter4095BandWindowUpper_zero :
    inverseSquareSingleReverseAfter4095BandWindowUpper 0 =
      inverseSquareSingleReverseAfter4095CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter4095BandWindowUpper,
    inverseSquareSingleReverseAfter4095CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter4095BandWindowLower_final :
    inverseSquareSingleReverseAfter4095BandWindowLower 2046 =
      inverseSquareSingleReverseBefore2048CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8391515 - 512) +
          inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046)
        (-11 : ℤ) =
      inverseSquareSingleReverseBefore2048CandidateWindowLower
  rw [inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq]
  norm_num [inverseSquareSingleReverseBefore2048CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter4095BandWindowUpper_final :
    inverseSquareSingleReverseAfter4095BandWindowUpper 2046 =
      inverseSquareSingleReverseBefore2048CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8391515 + 513) +
          inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046)
        (-11 : ℤ) =
      inverseSquareSingleReverseBefore2048CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq]
  norm_num [inverseSquareSingleReverseBefore2048CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the first whole-window reverse suffix band.
It checks that the already-certified `4094^{-2}, ..., 2049^{-2}` increments
remain normal for both endpoints of the post-`4095` window. -/
def inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificateBool :
    Bool :=
  (List.range 2046).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
    let k := 4094 - n
    let d := inverseSquareSingleScaledMantissaIncrement 36 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 36 ∧
      2 ^ 36 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8391515 - 512 + p) + d - 1 ∧
      (8391515 + 513 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the first whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 60000 in
  decide

/-- Pointwise endpoint-safety extraction for the first whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificate
    {n : ℕ} (hn : n < 2046) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
    let k := 4094 - n
    let d := inverseSquareSingleScaledMantissaIncrement 36 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 36 ∧
      2 ^ 36 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8391515 - 512 + p) + d - 1 ∧
      (8391515 + 513 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 2046,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 36 4094 x
        let k := 4094 - x
        let d := inverseSquareSingleScaledMantissaIncrement 36 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 36 ∧
          2 ^ 36 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8391515 - 512 + p) + d - 1 ∧
          (8391515 + 513 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the first whole-window reverse suffix band.
If the current accumulator is inside the prefix window after `n` additions,
then the next rounded addition stays inside the prefix window after `n+1`
additions. -/
theorem inverseSquareSingleReverseAfter4095BandWindow_round_step_mem
    {n : ℕ} (hn : n < 2046) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter4095BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter4095BandWindowUpper n) :
    inverseSquareSingleReverseAfter4095BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (4094 - n) ∧
      inverseSquareSingleForwardStep start (4094 - n) ≤
        inverseSquareSingleReverseAfter4095BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
  let k := 4094 - n
  let d := inverseSquareSingleScaledMantissaIncrement 36 k
  let mL := (8391515 - 512) + p
  let mU := (8391515 + 513) + p
  let e : ℤ := -11
  have hcert :=
    inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificate
      hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter4095BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter4095BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 36)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter4095BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter4095BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter4095BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 36)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter4095BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter4095BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter4095BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter4095BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter4095BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 36)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter4095BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8391003 +
              (inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n +
                inverseSquareSingleScaledMantissaIncrement 36 (4094 - n)))
            (-11 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8391003 +
              (inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n +
                inverseSquareSingleScaledMantissaIncrement 36 (4094 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter4095BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter4095BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter4095BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter4095BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter4095BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 36)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter4095BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8392028 +
              (inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n +
                inverseSquareSingleScaledMantissaIncrement 36 (4094 - n)))
            (-11 : ℤ) := by
      have hnat :
          mU + d =
            8392028 +
              (inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n +
                inverseSquareSingleScaledMantissaIncrement 36 (4094 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter4095BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `4094^{-2}, ..., 2049^{-2}` band:
any start in the post-`4095` candidate window remains in the corresponding
prefix window after any certified number of same-exponent additions. -/
theorem inverseSquareSingleReverseAfter4095BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter4095CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter4095CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 2046) :
    inverseSquareSingleReverseAfter4095BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 4094 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 4094 n ≤
        inverseSquareSingleReverseAfter4095BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter4095BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter4095BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 2046 := by omega
      have hnlt : n < 2046 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter4095BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- The lower endpoint of the post-`4095` window propagates through the whole
`4094^{-2}, ..., 2049^{-2}` band to the lower endpoint of the before-`2048`
window. -/
theorem inverseSquareSingleReverseAfter4095WindowLower_band4094_to_before2048_eq :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter4095CandidateWindowLower 4094 2046 =
      inverseSquareSingleReverseBefore2048CandidateWindowLower := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (36 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hcert :
      ∀ {n : ℕ}, n < 2046 →
        let m :=
          (8391515 - 512) +
            inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
        let k := 4094 - n
        let d := inverseSquareSingleScaledMantissaIncrement 36 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 36 ∧
          2 ^ 36 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    intro n hn
    have h :=
      inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificate
        hn
    let p := inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
    let k := 4094 - n
    let d := inverseSquareSingleScaledMantissaIncrement 36 k
    rcases h with ⟨hk, hd, hleft, hright, hmin, hmax⟩
    exact ⟨hk, hd, hleft, hright, by simpa [p, k, d] using hmin, by
      have hle :
          (8391515 - 512 + p) + d + 1 ≤
            (8391515 + 513 + p) + d + 1 := by omega
      exact lt_of_le_of_lt hle (by simpa [p, k, d] using hmax)⟩
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8391515 - 512) (q := 36) (kTop := 4094) (count := 2046)
      hexp hcert 2046 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter4095CandidateWindowLower 4094 2046 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8391515 - 512) +
          inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046)
        (-11 : ℤ) := by
        have hband' :
            inverseSquareSingleReverseAccumulatorFrom
                (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
                  (8391515 - 512) (-11 : ℤ)) 4094 2046 =
              FloatingPointFormat.ieeeSingleFormat.normalizedValue false
                ((8391515 - 512) +
                  inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046)
                (-11 : ℤ) := by
          simpa only [show (25 : ℤ) - (36 : ℕ) = (-11 : ℤ) by norm_num]
            using hband
        change
          inverseSquareSingleReverseAccumulatorFrom
              (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
                (8391515 - 512) (-11 : ℤ)) 4094 2046 =
            FloatingPointFormat.ieeeSingleFormat.normalizedValue false
              ((8391515 - 512) +
                inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046)
              (-11 : ℤ)
        exact hband'
    _ = inverseSquareSingleReverseBefore2048CandidateWindowLower := by
      rw [inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq]
      norm_num [inverseSquareSingleReverseBefore2048CandidateWindowLower,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]

/-- The upper endpoint of the post-`4095` window propagates through the whole
`4094^{-2}, ..., 2049^{-2}` band to the upper endpoint of the before-`2048`
window. -/
theorem inverseSquareSingleReverseAfter4095WindowUpper_band4094_to_before2048_eq :
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter4095CandidateWindowUpper 4094 2046 =
      inverseSquareSingleReverseBefore2048CandidateWindowUpper := by
  have hexp :
      FloatingPointFormat.ieeeSingleFormat.exponentInRange
        ((25 : ℤ) - (36 : ℤ)) := by
    norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hcert :
      ∀ {n : ℕ}, n < 2046 →
        let m :=
          (8391515 + 513) +
            inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
        let k := 4094 - n
        let d := inverseSquareSingleScaledMantissaIncrement 36 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 36 ∧
          2 ^ 36 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ m + d - 1 ∧
          m + d + 1 < 16777216 := by
    intro n hn
    have h :=
      inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificate
        hn
    let p := inverseSquareSingleReverseScaledMantissaPrefix 36 4094 n
    let k := 4094 - n
    let d := inverseSquareSingleScaledMantissaIncrement 36 k
    rcases h with ⟨hk, hd, hleft, hright, hmin, hmax⟩
    exact ⟨hk, hd, hleft, hright, by
      have hle :
          (8391515 - 512 + p) + d - 1 ≤
            (8391515 + 513 + p) + d - 1 := by omega
      exact le_trans (by simpa [p, k, d] using hmin) hle, by
        simpa [p, k, d] using hmax⟩
  have hband :=
    inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le
      (base := 8391515 + 513) (q := 36) (kTop := 4094) (count := 2046)
      hexp hcert 2046 (by norm_num)
  calc
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter4095CandidateWindowUpper 4094 2046 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8391515 + 513) +
          inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046)
        (-11 : ℤ) := by
        have hband' :
            inverseSquareSingleReverseAccumulatorFrom
                (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
                  (8391515 + 513) (-11 : ℤ)) 4094 2046 =
              FloatingPointFormat.ieeeSingleFormat.normalizedValue false
                ((8391515 + 513) +
                  inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046)
                (-11 : ℤ) := by
          simpa only [show (25 : ℤ) - (36 : ℕ) = (-11 : ℤ) by norm_num]
            using hband
        change
          inverseSquareSingleReverseAccumulatorFrom
              (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
                (8391515 + 513) (-11 : ℤ)) 4094 2046 =
            FloatingPointFormat.ieeeSingleFormat.normalizedValue false
              ((8391515 + 513) +
                inverseSquareSingleReverseScaledMantissaPrefix 36 4094 2046)
              (-11 : ℤ)
        exact hband'
    _ = inverseSquareSingleReverseBefore2048CandidateWindowUpper := by
      rw [inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq]
      norm_num [inverseSquareSingleReverseBefore2048CandidateWindowUpper,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]

/-- Whole-window band certificate for the `4094^{-2}, ..., 2049^{-2}` reverse
suffix chunk: every post-`4095` window start lands in the before-`2048`
window after the 2046 same-exponent additions. -/
def inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter4095CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter4095CandidateWindowUpper →
        inverseSquareSingleReverseBefore2048CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 4094 2046 ∧
          inverseSquareSingleReverseAccumulatorFrom start 4094 2046 ≤
            inverseSquareSingleReverseBefore2048CandidateWindowUpper

/-- Closed whole-window band certificate for the `4094^{-2}, ..., 2049^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window_closed :
    inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter4095BandWindow_prefix_mem
      (start := start) hlo hhi 2046 (by norm_num)
  rw [← inverseSquareSingleReverseAfter4095BandWindowLower_final,
    ← inverseSquareSingleReverseAfter4095BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`4095` candidate band lands in the before-`2048`
window.  This records that the whole-window band target is centered on the
already-closed concrete chunk certificate. -/
theorem inverseSquareSingleReverseAfter4095Candidate_band4094_to_before2048_mem_before2048Window :
    inverseSquareSingleReverseBefore2048CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter4095Candidate 4094 2046 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter4095Candidate 4094 2046 ≤
        inverseSquareSingleReverseBefore2048CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter4095Accumulator_4094_to_before2048]
  exact inverseSquareSingleReverseBefore2048Candidate_mem_before2048Window

/-- Remaining suffix certificate after the `4094^{-2}, ..., 2049^{-2}` band
has placed the state in the before-`2048` whole-window target. -/
def inverseSquareSingleReverseBefore2048WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore2048CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore2048CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 2048 2048 =
          inverseSquareSingleReversePrintedAccumulator

/-- Lower endpoint of the whole-window suffix state immediately after the
rounded `2048^{-2}` boundary step.  The before-`2048` window spans an
exponent boundary, so the lower side becomes 257 ulps in the new exponent. -/
noncomputable def inverseSquareSingleReverseAfter2048CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8390568 - 257) (-10 : ℤ)

/-- Upper endpoint of the whole-window suffix state immediately after the
rounded `2048^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter2048CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8390568 + 256) (-10 : ℤ)

/-- The named after-`2048` candidate lies in the post-`2048` whole-window
target. -/
theorem inverseSquareSingleReverseAfter2048Candidate_mem_after2048Window :
    inverseSquareSingleReverseAfter2048CandidateWindowLower ≤
        inverseSquareSingleReverseAfter2048Candidate ∧
      inverseSquareSingleReverseAfter2048Candidate ≤
        inverseSquareSingleReverseAfter2048CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter2048CandidateWindowLower,
      inverseSquareSingleReverseAfter2048CandidateWindowUpper,
      inverseSquareSingleReverseAfter2048Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `2048^{-2}` maps the before-`2048` whole window into
the exact post-`2048` enclosure. -/
theorem inverseSquareSingleReverseBefore2048Window_add_2048_term_mem_after2048Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore2048CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore2048CandidateWindowUpper) :
    inverseSquareSingleReverseAfter2048CandidateWindowLower ≤
        s + inverseSquareTerm 2048 ∧
      s + inverseSquareTerm 2048 ≤
        inverseSquareSingleReverseAfter2048CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter2048CandidateWindowLower ≤
          inverseSquareSingleReverseBefore2048CandidateWindowLower +
            inverseSquareTerm 2048 := by
      norm_num [inverseSquareSingleReverseAfter2048CandidateWindowLower,
        inverseSquareSingleReverseBefore2048CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore2048CandidateWindowLower +
            inverseSquareTerm 2048 ≤
          s + inverseSquareTerm 2048 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore2048CandidateWindowUpper +
            inverseSquareTerm 2048 ≤
          inverseSquareSingleReverseAfter2048CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseBefore2048CandidateWindowUpper,
        inverseSquareSingleReverseAfter2048CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 2048 ≤
          inverseSquareSingleReverseBefore2048CandidateWindowUpper +
            inverseSquareTerm 2048 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `2048^{-2}` maps every before-`2048` whole-window
start into the post-`2048` whole-window suffix state. -/
theorem inverseSquareSingleReverseBefore2048Window_round_2048_step_mem_after2048Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore2048CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore2048CandidateWindowUpper) :
    inverseSquareSingleReverseAfter2048CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 2048 ∧
      inverseSquareSingleForwardStep s 2048 ≤
        inverseSquareSingleReverseAfter2048CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore2048Window_add_2048_term_mem_after2048Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter2048CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8390568 - 257, (-10 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter2048CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8390568 + 256, (-10 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 2048)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 2048)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 2048)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-`2048` form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter2048WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter2048CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter2048CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 2047 2047 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`2048` whole-window suffix certificate implies the before-`2048`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_after2048Window
    (hsuffix : inverseSquareSingleReverseAfter2048WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter2048CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 2048 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 2048 1 ≤
          inverseSquareSingleReverseAfter2048CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore2048Window_round_2048_step_mem_after2048Window
        hlo hhi
  rw [show 2048 = 1 + 2047 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 2048 - 1 = 2047 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 2048 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `1024^{-2}`
boundary step, after the `2047^{-2}, ..., 1025^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore1024CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16768950 - 257) (-10 : ℤ)

/-- Upper endpoint for the whole-window state just before the `1024^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore1024CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16768950 + 256) (-10 : ℤ)

/-- The concrete before-`1024` candidate lies in the before-`1024`
whole-window target. -/
theorem inverseSquareSingleReverseBefore1024Candidate_mem_before1024Window :
    inverseSquareSingleReverseBefore1024CandidateWindowLower ≤
        inverseSquareSingleReverseBefore1024Candidate ∧
      inverseSquareSingleReverseBefore1024Candidate ≤
        inverseSquareSingleReverseBefore1024CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore1024CandidateWindowLower,
      inverseSquareSingleReverseBefore1024CandidateWindowUpper,
      inverseSquareSingleReverseBefore1024Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after `n` additions inside the `2047^{-2}, ..., 1025^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter2048BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8390568 - 257) +
      inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n) (-10 : ℤ)

/-- Upper endpoint after `n` additions inside the `2047^{-2}, ..., 1025^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter2048BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8390568 + 256) +
      inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n) (-10 : ℤ)

theorem inverseSquareSingleReverseAfter2048BandWindowLower_zero :
    inverseSquareSingleReverseAfter2048BandWindowLower 0 =
      inverseSquareSingleReverseAfter2048CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter2048BandWindowLower,
    inverseSquareSingleReverseAfter2048CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter2048BandWindowUpper_zero :
    inverseSquareSingleReverseAfter2048BandWindowUpper 0 =
      inverseSquareSingleReverseAfter2048CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter2048BandWindowUpper,
    inverseSquareSingleReverseAfter2048CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter2048BandWindowLower_final :
    inverseSquareSingleReverseAfter2048BandWindowLower 1023 =
      inverseSquareSingleReverseBefore1024CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8390568 - 257) +
          inverseSquareSingleReverseScaledMantissaPrefix 35 2047 1023)
        (-10 : ℤ) =
      inverseSquareSingleReverseBefore1024CandidateWindowLower
  rw [inverseSquareSingleReverseAfter2048Prefix_2047_to_1025_eq]
  norm_num [inverseSquareSingleReverseBefore1024CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter2048BandWindowUpper_final :
    inverseSquareSingleReverseAfter2048BandWindowUpper 1023 =
      inverseSquareSingleReverseBefore1024CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8390568 + 256) +
          inverseSquareSingleReverseScaledMantissaPrefix 35 2047 1023)
        (-10 : ℤ) =
      inverseSquareSingleReverseBefore1024CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter2048Prefix_2047_to_1025_eq]
  norm_num [inverseSquareSingleReverseBefore1024CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the second whole-window reverse suffix
band. It checks that the already-certified `2047^{-2}, ..., 1025^{-2}`
increments remain normal for both endpoints of the post-`2048` window. -/
def inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificateBool :
    Bool :=
  (List.range 1023).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n
    let k := 2047 - n
    let d := inverseSquareSingleScaledMantissaIncrement 35 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 35 ∧
      2 ^ 35 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8390568 - 257 + p) + d - 1 ∧
      (8390568 + 256 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the second whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 40000 in
  decide

/-- Pointwise endpoint-safety extraction for the second whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificate
    {n : ℕ} (hn : n < 1023) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n
    let k := 2047 - n
    let d := inverseSquareSingleScaledMantissaIncrement 35 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 35 ∧
      2 ^ 35 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8390568 - 257 + p) + d - 1 ∧
      (8390568 + 256 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 1023,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 35 2047 x
        let k := 2047 - x
        let d := inverseSquareSingleScaledMantissaIncrement 35 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 35 ∧
          2 ^ 35 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8390568 - 257 + p) + d - 1 ∧
          (8390568 + 256 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the second whole-window reverse suffix band.
If the current accumulator is inside the prefix window after `n` additions,
then the next rounded addition stays inside the prefix window after `n+1`
additions. -/
theorem inverseSquareSingleReverseAfter2048BandWindow_round_step_mem
    {n : ℕ} (hn : n < 1023) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter2048BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter2048BandWindowUpper n) :
    inverseSquareSingleReverseAfter2048BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (2047 - n) ∧
      inverseSquareSingleForwardStep start (2047 - n) ≤
        inverseSquareSingleReverseAfter2048BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n
  let k := 2047 - n
  let d := inverseSquareSingleScaledMantissaIncrement 35 k
  let mL := (8390568 - 257) + p
  let mU := (8390568 + 256) + p
  let e : ℤ := -10
  have hcert :=
    inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificate
      hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter2048BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter2048BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 35)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter2048BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter2048BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter2048BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 35)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter2048BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter2048BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter2048BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter2048BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter2048BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 35)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter2048BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8390311 +
              (inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n +
                inverseSquareSingleScaledMantissaIncrement 35 (2047 - n)))
            (-10 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8390311 +
              (inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n +
                inverseSquareSingleScaledMantissaIncrement 35 (2047 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter2048BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter2048BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter2048BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter2048BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter2048BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 35)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter2048BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8390824 +
              (inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n +
                inverseSquareSingleScaledMantissaIncrement 35 (2047 - n)))
            (-10 : ℤ) := by
      have hnat :
          mU + d =
            8390824 +
              (inverseSquareSingleReverseScaledMantissaPrefix 35 2047 n +
                inverseSquareSingleScaledMantissaIncrement 35 (2047 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter2048BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `2047^{-2}, ..., 1025^{-2}` band:
any start in the post-`2048` candidate window remains in the corresponding
prefix window after any certified number of same-exponent additions. -/
theorem inverseSquareSingleReverseAfter2048BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter2048CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter2048CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 1023) :
    inverseSquareSingleReverseAfter2048BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 2047 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 2047 n ≤
        inverseSquareSingleReverseAfter2048BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter2048BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter2048BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 1023 := by omega
      have hnlt : n < 1023 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter2048BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window band certificate for the `2047^{-2}, ..., 1025^{-2}` reverse
suffix chunk: every post-`2048` window start lands in the before-`1024`
window after the 1023 same-exponent additions. -/
def inverseSquareSingleReverseAfter2048Band2047ToBefore1024Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter2048CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter2048CandidateWindowUpper →
        inverseSquareSingleReverseBefore1024CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 2047 1023 ∧
          inverseSquareSingleReverseAccumulatorFrom start 2047 1023 ≤
            inverseSquareSingleReverseBefore1024CandidateWindowUpper

/-- Closed whole-window band certificate for the `2047^{-2}, ..., 1025^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter2048Band2047ToBefore1024Window_closed :
    inverseSquareSingleReverseAfter2048Band2047ToBefore1024Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter2048BandWindow_prefix_mem
      (start := start) hlo hhi 1023 (by norm_num)
  rw [← inverseSquareSingleReverseAfter2048BandWindowLower_final,
    ← inverseSquareSingleReverseAfter2048BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`2048` candidate band lands in the before-`1024`
window.  This records that the whole-window band target is centered on the
already-closed concrete chunk certificate. -/
theorem inverseSquareSingleReverseAfter2048Candidate_band2047_to_before1024_mem_before1024Window :
    inverseSquareSingleReverseBefore1024CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter2048Candidate 2047 1023 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter2048Candidate 2047 1023 ≤
        inverseSquareSingleReverseBefore1024CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter2048Accumulator_2047_to_before1024]
  exact inverseSquareSingleReverseBefore1024Candidate_mem_before1024Window

/-- Remaining suffix certificate after the `2047^{-2}, ..., 1025^{-2}` band
has placed the state in the before-`1024` whole-window target. -/
def inverseSquareSingleReverseBefore1024WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore1024CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore1024CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 1024 1024 =
          inverseSquareSingleReversePrintedAccumulator

/-- A whole-window certificate for the `2047^{-2}, ..., 1025^{-2}` band plus a
before-`1024` suffix certificate imply the post-`2048` suffix certificate. -/
theorem inverseSquareSingleReverseAfter2048WindowMapsToPrinted_of_band2047_to_before1024Window
    (hband : inverseSquareSingleReverseAfter2048Band2047ToBefore1024Window)
    (hsuffix : inverseSquareSingleReverseBefore1024WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter2048WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 2047 = 1023 + 1024 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 2047 - 1023 = 1024 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 2047 1023)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`1024` whole-window suffix map is supplied, the entire
post-`2048` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter2048WindowMapsToPrinted_of_before1024Window
    (hsuffix : inverseSquareSingleReverseBefore1024WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter2048WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter2048WindowMapsToPrinted_of_band2047_to_before1024Window
    inverseSquareSingleReverseAfter2048Band2047ToBefore1024Window_closed
    hsuffix

/-- Once the before-`1024` whole-window suffix map is supplied, the
before-`2048` whole-window suffix map is closed by the rounded boundary step
and certified same-exponent band. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before1024Window
    (hsuffix : inverseSquareSingleReverseBefore1024WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_after2048Window
    (inverseSquareSingleReverseAfter2048WindowMapsToPrinted_of_before1024Window
      hsuffix)

/-- Lower endpoint of the whole-window suffix state immediately after the
rounded `1024^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter1024CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8392667 - 129) (-9 : ℤ)

/-- Upper endpoint of the whole-window suffix state immediately after the
rounded `1024^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter1024CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8392667 + 128) (-9 : ℤ)

/-- The named after-`1024` candidate lies in the post-`1024` whole-window
target. -/
theorem inverseSquareSingleReverseAfter1024Candidate_mem_after1024Window :
    inverseSquareSingleReverseAfter1024CandidateWindowLower ≤
        inverseSquareSingleReverseAfter1024Candidate ∧
      inverseSquareSingleReverseAfter1024Candidate ≤
        inverseSquareSingleReverseAfter1024CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter1024CandidateWindowLower,
      inverseSquareSingleReverseAfter1024CandidateWindowUpper,
      inverseSquareSingleReverseAfter1024Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `1024^{-2}` maps the before-`1024` whole window into
the exact post-`1024` enclosure. -/
theorem inverseSquareSingleReverseBefore1024Window_add_1024_term_mem_after1024Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore1024CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore1024CandidateWindowUpper) :
    inverseSquareSingleReverseAfter1024CandidateWindowLower ≤
        s + inverseSquareTerm 1024 ∧
      s + inverseSquareTerm 1024 ≤
        inverseSquareSingleReverseAfter1024CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter1024CandidateWindowLower ≤
          inverseSquareSingleReverseBefore1024CandidateWindowLower +
            inverseSquareTerm 1024 := by
      norm_num [inverseSquareSingleReverseAfter1024CandidateWindowLower,
        inverseSquareSingleReverseBefore1024CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore1024CandidateWindowLower +
            inverseSquareTerm 1024 ≤
          s + inverseSquareTerm 1024 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore1024CandidateWindowUpper +
            inverseSquareTerm 1024 ≤
          inverseSquareSingleReverseAfter1024CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseBefore1024CandidateWindowUpper,
        inverseSquareSingleReverseAfter1024CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 1024 ≤
          inverseSquareSingleReverseBefore1024CandidateWindowUpper +
            inverseSquareTerm 1024 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `1024^{-2}` maps every before-`1024` whole-window
start into the post-`1024` whole-window suffix state. -/
theorem inverseSquareSingleReverseBefore1024Window_round_1024_step_mem_after1024Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore1024CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore1024CandidateWindowUpper) :
    inverseSquareSingleReverseAfter1024CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 1024 ∧
      inverseSquareSingleForwardStep s 1024 ≤
        inverseSquareSingleReverseAfter1024CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore1024Window_add_1024_term_mem_after1024Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter1024CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8392667 - 129, (-9 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter1024CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8392667 + 128, (-9 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 1024)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 1024)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 1024)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-`1024` form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter1024WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter1024CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter1024CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 1023 1023 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`1024` whole-window suffix certificate implies the before-`1024`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_after1024Window
    (hsuffix : inverseSquareSingleReverseAfter1024WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore1024WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter1024CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 1024 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 1024 1 ≤
          inverseSquareSingleReverseAfter1024CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore1024Window_round_1024_step_mem_after1024Window
        hlo hhi
  rw [show 1024 = 1 + 1023 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 1024 - 1 = 1023 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 1024 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `512^{-2}`
boundary step, after the `1023^{-2}, ..., 513^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore512CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16760811 - 129) (-9 : ℤ)

/-- Upper endpoint for the whole-window state just before the `512^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore512CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16760811 + 128) (-9 : ℤ)

/-- The concrete before-`512` candidate lies in the before-`512`
whole-window target. -/
theorem inverseSquareSingleReverseBefore512Candidate_mem_before512Window :
    inverseSquareSingleReverseBefore512CandidateWindowLower ≤
        inverseSquareSingleReverseBefore512Candidate ∧
      inverseSquareSingleReverseBefore512Candidate ≤
        inverseSquareSingleReverseBefore512CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore512CandidateWindowLower,
      inverseSquareSingleReverseBefore512CandidateWindowUpper,
      inverseSquareSingleReverseBefore512Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after `n` additions inside the `1023^{-2}, ..., 513^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter1024BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8392667 - 129) +
      inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n) (-9 : ℤ)

/-- Upper endpoint after `n` additions inside the `1023^{-2}, ..., 513^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter1024BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8392667 + 128) +
      inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n) (-9 : ℤ)

theorem inverseSquareSingleReverseAfter1024BandWindowLower_zero :
    inverseSquareSingleReverseAfter1024BandWindowLower 0 =
      inverseSquareSingleReverseAfter1024CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter1024BandWindowLower,
    inverseSquareSingleReverseAfter1024CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter1024BandWindowUpper_zero :
    inverseSquareSingleReverseAfter1024BandWindowUpper 0 =
      inverseSquareSingleReverseAfter1024CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter1024BandWindowUpper,
    inverseSquareSingleReverseAfter1024CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter1024BandWindowLower_final :
    inverseSquareSingleReverseAfter1024BandWindowLower 511 =
      inverseSquareSingleReverseBefore512CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8392667 - 129) +
          inverseSquareSingleReverseScaledMantissaPrefix 34 1023 511)
        (-9 : ℤ) =
      inverseSquareSingleReverseBefore512CandidateWindowLower
  rw [inverseSquareSingleReverseAfter1024Prefix_1023_to_513_eq]
  norm_num [inverseSquareSingleReverseBefore512CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter1024BandWindowUpper_final :
    inverseSquareSingleReverseAfter1024BandWindowUpper 511 =
      inverseSquareSingleReverseBefore512CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8392667 + 128) +
          inverseSquareSingleReverseScaledMantissaPrefix 34 1023 511)
        (-9 : ℤ) =
      inverseSquareSingleReverseBefore512CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter1024Prefix_1023_to_513_eq]
  norm_num [inverseSquareSingleReverseBefore512CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the third whole-window reverse suffix
band. It checks that the already-certified `1023^{-2}, ..., 513^{-2}`
increments remain normal for both endpoints of the post-`1024` window. -/
def inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificateBool :
    Bool :=
  (List.range 511).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n
    let k := 1023 - n
    let d := inverseSquareSingleScaledMantissaIncrement 34 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 34 ∧
      2 ^ 34 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8392667 - 129 + p) + d - 1 ∧
      (8392667 + 128 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the third whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 30000 in
  decide

/-- Pointwise endpoint-safety extraction for the third whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificate
    {n : ℕ} (hn : n < 511) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n
    let k := 1023 - n
    let d := inverseSquareSingleScaledMantissaIncrement 34 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 34 ∧
      2 ^ 34 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8392667 - 129 + p) + d - 1 ∧
      (8392667 + 128 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 511,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 34 1023 x
        let k := 1023 - x
        let d := inverseSquareSingleScaledMantissaIncrement 34 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 34 ∧
          2 ^ 34 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8392667 - 129 + p) + d - 1 ∧
          (8392667 + 128 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the third whole-window reverse suffix band.
If the current accumulator is inside the prefix window after `n` additions,
then the next rounded addition stays inside the prefix window after `n+1`
additions. -/
theorem inverseSquareSingleReverseAfter1024BandWindow_round_step_mem
    {n : ℕ} (hn : n < 511) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter1024BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter1024BandWindowUpper n) :
    inverseSquareSingleReverseAfter1024BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (1023 - n) ∧
      inverseSquareSingleForwardStep start (1023 - n) ≤
        inverseSquareSingleReverseAfter1024BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n
  let k := 1023 - n
  let d := inverseSquareSingleScaledMantissaIncrement 34 k
  let mL := (8392667 - 129) + p
  let mU := (8392667 + 128) + p
  let e : ℤ := -9
  have hcert :=
    inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificate
      hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter1024BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter1024BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 34)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter1024BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter1024BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter1024BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 34)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter1024BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter1024BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter1024BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter1024BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter1024BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 34)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter1024BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8392538 +
              (inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n +
                inverseSquareSingleScaledMantissaIncrement 34 (1023 - n)))
            (-9 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8392538 +
              (inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n +
                inverseSquareSingleScaledMantissaIncrement 34 (1023 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter1024BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter1024BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter1024BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter1024BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter1024BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 34)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter1024BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8392795 +
              (inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n +
                inverseSquareSingleScaledMantissaIncrement 34 (1023 - n)))
            (-9 : ℤ) := by
      have hnat :
          mU + d =
            8392795 +
              (inverseSquareSingleReverseScaledMantissaPrefix 34 1023 n +
                inverseSquareSingleScaledMantissaIncrement 34 (1023 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter1024BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `1023^{-2}, ..., 513^{-2}` band:
any start in the post-`1024` candidate window remains in the corresponding
prefix window after any certified number of same-exponent additions. -/
theorem inverseSquareSingleReverseAfter1024BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter1024CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter1024CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 511) :
    inverseSquareSingleReverseAfter1024BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 1023 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 1023 n ≤
        inverseSquareSingleReverseAfter1024BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter1024BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter1024BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 511 := by omega
      have hnlt : n < 511 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter1024BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window band certificate for the `1023^{-2}, ..., 513^{-2}` reverse
suffix chunk: every post-`1024` window start lands in the before-`512`
window after the 511 same-exponent additions. -/
def inverseSquareSingleReverseAfter1024Band1023ToBefore512Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter1024CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter1024CandidateWindowUpper →
        inverseSquareSingleReverseBefore512CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 1023 511 ∧
          inverseSquareSingleReverseAccumulatorFrom start 1023 511 ≤
            inverseSquareSingleReverseBefore512CandidateWindowUpper

/-- Closed whole-window band certificate for the `1023^{-2}, ..., 513^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter1024Band1023ToBefore512Window_closed :
    inverseSquareSingleReverseAfter1024Band1023ToBefore512Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter1024BandWindow_prefix_mem
      (start := start) hlo hhi 511 (by norm_num)
  rw [← inverseSquareSingleReverseAfter1024BandWindowLower_final,
    ← inverseSquareSingleReverseAfter1024BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`1024` candidate band lands in the before-`512`
window.  This records that the whole-window band target is centered on the
already-closed concrete chunk certificate. -/
theorem inverseSquareSingleReverseAfter1024Candidate_band1023_to_before512_mem_before512Window :
    inverseSquareSingleReverseBefore512CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter1024Candidate 1023 511 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter1024Candidate 1023 511 ≤
        inverseSquareSingleReverseBefore512CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter1024Accumulator_1023_to_before512]
  exact inverseSquareSingleReverseBefore512Candidate_mem_before512Window

/-- Remaining suffix certificate after the `1023^{-2}, ..., 513^{-2}` band
has placed the state in the before-`512` whole-window target. -/
def inverseSquareSingleReverseBefore512WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore512CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore512CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 512 512 =
          inverseSquareSingleReversePrintedAccumulator

/-- A whole-window certificate for the `1023^{-2}, ..., 513^{-2}` band plus a
before-`512` suffix certificate imply the post-`1024` suffix certificate. -/
theorem inverseSquareSingleReverseAfter1024WindowMapsToPrinted_of_band1023_to_before512Window
    (hband : inverseSquareSingleReverseAfter1024Band1023ToBefore512Window)
    (hsuffix : inverseSquareSingleReverseBefore512WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter1024WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 1023 = 511 + 512 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 1023 - 511 = 512 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 1023 511)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`512` whole-window suffix map is supplied, the entire
post-`1024` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter1024WindowMapsToPrinted_of_before512Window
    (hsuffix : inverseSquareSingleReverseBefore512WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter1024WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter1024WindowMapsToPrinted_of_band1023_to_before512Window
    inverseSquareSingleReverseAfter1024Band1023ToBefore512Window_closed
    hsuffix

/-- Once the before-`512` whole-window suffix map is supplied, the
before-`1024` whole-window suffix map is closed by the rounded boundary step
and certified same-exponent band. -/
theorem inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before512Window
    (hsuffix : inverseSquareSingleReverseBefore512WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore1024WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_after1024Window
    (inverseSquareSingleReverseAfter1024WindowMapsToPrinted_of_before512Window
      hsuffix)

/-- Once the before-`512` whole-window suffix map is supplied, the
before-`2048` whole-window suffix map is closed through the before-`1024`
boundary and band. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before512Window
    (hsuffix : inverseSquareSingleReverseBefore512WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before1024Window
    (inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before512Window
      hsuffix)

/-- Lower endpoint of the whole-window suffix state immediately after the
rounded `512^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter512CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8396790 - 65) (-8 : ℤ)

/-- Upper endpoint of the whole-window suffix state immediately after the
rounded `512^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter512CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8396790 + 64) (-8 : ℤ)

/-- The named after-`512` candidate lies in the post-`512` whole-window
target. -/
theorem inverseSquareSingleReverseAfter512Candidate_mem_after512Window :
    inverseSquareSingleReverseAfter512CandidateWindowLower ≤
        inverseSquareSingleReverseAfter512Candidate ∧
      inverseSquareSingleReverseAfter512Candidate ≤
        inverseSquareSingleReverseAfter512CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter512CandidateWindowLower,
      inverseSquareSingleReverseAfter512CandidateWindowUpper,
      inverseSquareSingleReverseAfter512Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `512^{-2}` maps the before-`512` whole window into
the exact post-`512` enclosure. -/
theorem inverseSquareSingleReverseBefore512Window_add_512_term_mem_after512Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore512CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore512CandidateWindowUpper) :
    inverseSquareSingleReverseAfter512CandidateWindowLower ≤
        s + inverseSquareTerm 512 ∧
      s + inverseSquareTerm 512 ≤
        inverseSquareSingleReverseAfter512CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter512CandidateWindowLower ≤
          inverseSquareSingleReverseBefore512CandidateWindowLower +
            inverseSquareTerm 512 := by
      norm_num [inverseSquareSingleReverseAfter512CandidateWindowLower,
        inverseSquareSingleReverseBefore512CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore512CandidateWindowLower +
            inverseSquareTerm 512 ≤
          s + inverseSquareTerm 512 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore512CandidateWindowUpper +
            inverseSquareTerm 512 ≤
          inverseSquareSingleReverseAfter512CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseBefore512CandidateWindowUpper,
        inverseSquareSingleReverseAfter512CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 512 ≤
          inverseSquareSingleReverseBefore512CandidateWindowUpper +
            inverseSquareTerm 512 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `512^{-2}` maps every before-`512` whole-window
start into the post-`512` whole-window suffix state. -/
theorem inverseSquareSingleReverseBefore512Window_round_512_step_mem_after512Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore512CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore512CandidateWindowUpper) :
    inverseSquareSingleReverseAfter512CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 512 ∧
      inverseSquareSingleForwardStep s 512 ≤
        inverseSquareSingleReverseAfter512CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore512Window_add_512_term_mem_after512Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter512CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8396790 - 65, (-8 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter512CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8396790 + 64, (-8 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 512)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 512)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 512)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-`512` form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter512WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter512CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter512CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 511 511 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`512` whole-window suffix certificate implies the before-`512`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_after512Window
    (hsuffix : inverseSquareSingleReverseAfter512WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore512WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter512CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 512 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 512 1 ≤
          inverseSquareSingleReverseAfter512CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore512Window_round_512_step_mem_after512Window
        hlo hhi
  rw [show 512 = 1 + 511 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 512 - 1 = 511 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 512 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `256^{-2}`
boundary step, after the `511^{-2}, ..., 257^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore256CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16744479 - 65) (-8 : ℤ)

/-- Upper endpoint for the whole-window state just before the `256^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore256CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16744479 + 64) (-8 : ℤ)

/-- The concrete before-`256` candidate lies in the before-`256`
whole-window target. -/
theorem inverseSquareSingleReverseBefore256Candidate_mem_before256Window :
    inverseSquareSingleReverseBefore256CandidateWindowLower ≤
        inverseSquareSingleReverseBefore256Candidate ∧
      inverseSquareSingleReverseBefore256Candidate ≤
        inverseSquareSingleReverseBefore256CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore256CandidateWindowLower,
      inverseSquareSingleReverseBefore256CandidateWindowUpper,
      inverseSquareSingleReverseBefore256Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after `n` additions inside the `511^{-2}, ..., 257^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter512BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8396790 - 65) +
      inverseSquareSingleReverseScaledMantissaPrefix 33 511 n) (-8 : ℤ)

/-- Upper endpoint after `n` additions inside the `511^{-2}, ..., 257^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter512BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8396790 + 64) +
      inverseSquareSingleReverseScaledMantissaPrefix 33 511 n) (-8 : ℤ)

theorem inverseSquareSingleReverseAfter512BandWindowLower_zero :
    inverseSquareSingleReverseAfter512BandWindowLower 0 =
      inverseSquareSingleReverseAfter512CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter512BandWindowLower,
    inverseSquareSingleReverseAfter512CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter512BandWindowUpper_zero :
    inverseSquareSingleReverseAfter512BandWindowUpper 0 =
      inverseSquareSingleReverseAfter512CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter512BandWindowUpper,
    inverseSquareSingleReverseAfter512CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter512BandWindowLower_final :
    inverseSquareSingleReverseAfter512BandWindowLower 255 =
      inverseSquareSingleReverseBefore256CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8396790 - 65) +
          inverseSquareSingleReverseScaledMantissaPrefix 33 511 255)
        (-8 : ℤ) =
      inverseSquareSingleReverseBefore256CandidateWindowLower
  rw [inverseSquareSingleReverseAfter512Prefix_511_to_257_eq]
  norm_num [inverseSquareSingleReverseBefore256CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter512BandWindowUpper_final :
    inverseSquareSingleReverseAfter512BandWindowUpper 255 =
      inverseSquareSingleReverseBefore256CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8396790 + 64) +
          inverseSquareSingleReverseScaledMantissaPrefix 33 511 255)
        (-8 : ℤ) =
      inverseSquareSingleReverseBefore256CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter512Prefix_511_to_257_eq]
  norm_num [inverseSquareSingleReverseBefore256CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the fourth whole-window reverse suffix
band. It checks that the already-certified `511^{-2}, ..., 257^{-2}`
increments remain normal for both endpoints of the post-`512` window. -/
def inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificateBool :
    Bool :=
  (List.range 255).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 33 511 n
    let k := 511 - n
    let d := inverseSquareSingleScaledMantissaIncrement 33 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 33 ∧
      2 ^ 33 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8396790 - 65 + p) + d - 1 ∧
      (8396790 + 64 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the fourth whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 20000 in
  decide

/-- Pointwise endpoint-safety extraction for the fourth whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificate
    {n : ℕ} (hn : n < 255) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 33 511 n
    let k := 511 - n
    let d := inverseSquareSingleScaledMantissaIncrement 33 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 33 ∧
      2 ^ 33 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8396790 - 65 + p) + d - 1 ∧
      (8396790 + 64 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 255,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 33 511 x
        let k := 511 - x
        let d := inverseSquareSingleScaledMantissaIncrement 33 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 33 ∧
          2 ^ 33 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8396790 - 65 + p) + d - 1 ∧
          (8396790 + 64 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the fourth whole-window reverse suffix band.
If the current accumulator is inside the prefix window after `n` additions,
then the next rounded addition stays inside the prefix window after `n+1`
additions. -/
theorem inverseSquareSingleReverseAfter512BandWindow_round_step_mem
    {n : ℕ} (hn : n < 255) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter512BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter512BandWindowUpper n) :
    inverseSquareSingleReverseAfter512BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (511 - n) ∧
      inverseSquareSingleForwardStep start (511 - n) ≤
        inverseSquareSingleReverseAfter512BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 33 511 n
  let k := 511 - n
  let d := inverseSquareSingleScaledMantissaIncrement 33 k
  let mL := (8396790 - 65) + p
  let mU := (8396790 + 64) + p
  let e : ℤ := -8
  have hcert :=
    inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificate
      hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter512BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter512BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 33)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter512BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter512BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter512BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 33)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter512BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter512BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter512BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter512BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter512BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 33)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter512BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8396725 +
              (inverseSquareSingleReverseScaledMantissaPrefix 33 511 n +
                inverseSquareSingleScaledMantissaIncrement 33 (511 - n)))
            (-8 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8396725 +
              (inverseSquareSingleReverseScaledMantissaPrefix 33 511 n +
                inverseSquareSingleScaledMantissaIncrement 33 (511 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter512BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter512BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter512BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter512BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter512BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 33)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter512BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8396854 +
              (inverseSquareSingleReverseScaledMantissaPrefix 33 511 n +
                inverseSquareSingleScaledMantissaIncrement 33 (511 - n)))
            (-8 : ℤ) := by
      have hnat :
          mU + d =
            8396854 +
              (inverseSquareSingleReverseScaledMantissaPrefix 33 511 n +
                inverseSquareSingleScaledMantissaIncrement 33 (511 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter512BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `511^{-2}, ..., 257^{-2}` band:
any start in the post-`512` candidate window remains in the corresponding
prefix window after any certified number of same-exponent additions. -/
theorem inverseSquareSingleReverseAfter512BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter512CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter512CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 255) :
    inverseSquareSingleReverseAfter512BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 511 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 511 n ≤
        inverseSquareSingleReverseAfter512BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter512BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter512BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 255 := by omega
      have hnlt : n < 255 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter512BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window band certificate for the `511^{-2}, ..., 257^{-2}` reverse
suffix chunk: every post-`512` window start lands in the before-`256`
window after the 255 same-exponent additions. -/
def inverseSquareSingleReverseAfter512Band511ToBefore256Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter512CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter512CandidateWindowUpper →
        inverseSquareSingleReverseBefore256CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 511 255 ∧
          inverseSquareSingleReverseAccumulatorFrom start 511 255 ≤
            inverseSquareSingleReverseBefore256CandidateWindowUpper

/-- Closed whole-window band certificate for the `511^{-2}, ..., 257^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter512Band511ToBefore256Window_closed :
    inverseSquareSingleReverseAfter512Band511ToBefore256Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter512BandWindow_prefix_mem
      (start := start) hlo hhi 255 (by norm_num)
  rw [← inverseSquareSingleReverseAfter512BandWindowLower_final,
    ← inverseSquareSingleReverseAfter512BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`512` candidate band lands in the before-`256`
window.  This records that the whole-window band target is centered on the
already-closed concrete chunk certificate. -/
theorem inverseSquareSingleReverseAfter512Candidate_band511_to_before256_mem_before256Window :
    inverseSquareSingleReverseBefore256CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter512Candidate 511 255 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter512Candidate 511 255 ≤
        inverseSquareSingleReverseBefore256CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter512Accumulator_511_to_before256]
  exact inverseSquareSingleReverseBefore256Candidate_mem_before256Window

/-- Remaining suffix certificate after the `511^{-2}, ..., 257^{-2}` band
has placed the state in the before-`256` whole-window target. -/
def inverseSquareSingleReverseBefore256WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore256CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore256CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 256 256 =
          inverseSquareSingleReversePrintedAccumulator

/-- A whole-window certificate for the `511^{-2}, ..., 257^{-2}` band plus a
before-`256` suffix certificate imply the post-`512` suffix certificate. -/
theorem inverseSquareSingleReverseAfter512WindowMapsToPrinted_of_band511_to_before256Window
    (hband : inverseSquareSingleReverseAfter512Band511ToBefore256Window)
    (hsuffix : inverseSquareSingleReverseBefore256WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter512WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 511 = 255 + 256 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 511 - 255 = 256 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 511 255)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`256` whole-window suffix map is supplied, the entire
post-`512` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter512WindowMapsToPrinted_of_before256Window
    (hsuffix : inverseSquareSingleReverseBefore256WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter512WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter512WindowMapsToPrinted_of_band511_to_before256Window
    inverseSquareSingleReverseAfter512Band511ToBefore256Window_closed
    hsuffix

/-- Once the before-`256` whole-window suffix map is supplied, the
before-`512` whole-window suffix map is closed by the rounded boundary step
and certified same-exponent band. -/
theorem inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before256Window
    (hsuffix : inverseSquareSingleReverseBefore256WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore512WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_after512Window
    (inverseSquareSingleReverseAfter512WindowMapsToPrinted_of_before256Window
      hsuffix)

/-- Once the before-`256` whole-window suffix map is supplied, the
before-`1024` whole-window suffix map is closed through the before-`512`
boundary and band. -/
theorem inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before256Window
    (hsuffix : inverseSquareSingleReverseBefore256WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore1024WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before512Window
    (inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before256Window
      hsuffix)

/-- Once the before-`256` whole-window suffix map is supplied, the
before-`2048` whole-window suffix map is closed through the before-`512`
boundary and band. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before256Window
    (hsuffix : inverseSquareSingleReverseBefore256WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before512Window
    (inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before256Window
      hsuffix)

/-- Lower endpoint of the whole-window suffix state immediately after the
rounded `256^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter256CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8405008 - 33) (-7 : ℤ)

/-- Upper endpoint of the whole-window suffix state immediately after the
rounded `256^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter256CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8405008 + 32) (-7 : ℤ)

/-- The named after-`256` candidate lies in the post-`256` whole-window
target. -/
theorem inverseSquareSingleReverseAfter256Candidate_mem_after256Window :
    inverseSquareSingleReverseAfter256CandidateWindowLower ≤
        inverseSquareSingleReverseAfter256Candidate ∧
      inverseSquareSingleReverseAfter256Candidate ≤
        inverseSquareSingleReverseAfter256CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter256CandidateWindowLower,
      inverseSquareSingleReverseAfter256CandidateWindowUpper,
      inverseSquareSingleReverseAfter256Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `256^{-2}` maps the before-`256` whole window into
the exact post-`256` enclosure. -/
theorem inverseSquareSingleReverseBefore256Window_add_256_term_mem_after256Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore256CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore256CandidateWindowUpper) :
    inverseSquareSingleReverseAfter256CandidateWindowLower ≤
        s + inverseSquareTerm 256 ∧
      s + inverseSquareTerm 256 ≤
        inverseSquareSingleReverseAfter256CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter256CandidateWindowLower ≤
          inverseSquareSingleReverseBefore256CandidateWindowLower +
            inverseSquareTerm 256 := by
      norm_num [inverseSquareSingleReverseAfter256CandidateWindowLower,
        inverseSquareSingleReverseBefore256CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore256CandidateWindowLower +
            inverseSquareTerm 256 ≤
          s + inverseSquareTerm 256 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore256CandidateWindowUpper +
            inverseSquareTerm 256 ≤
          inverseSquareSingleReverseAfter256CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseBefore256CandidateWindowUpper,
        inverseSquareSingleReverseAfter256CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 256 ≤
          inverseSquareSingleReverseBefore256CandidateWindowUpper +
            inverseSquareTerm 256 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `256^{-2}` maps every before-`256` whole-window
start into the post-`256` whole-window suffix state. -/
theorem inverseSquareSingleReverseBefore256Window_round_256_step_mem_after256Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore256CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore256CandidateWindowUpper) :
    inverseSquareSingleReverseAfter256CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 256 ∧
      inverseSquareSingleForwardStep s 256 ≤
        inverseSquareSingleReverseAfter256CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore256Window_add_256_term_mem_after256Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter256CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8405008 - 33, (-7 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter256CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8405008 + 32, (-7 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 256)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 256)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 256)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-`256` form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter256WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter256CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter256CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 255 255 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`256` whole-window suffix certificate implies the before-`256`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_after256Window
    (hsuffix : inverseSquareSingleReverseAfter256WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore256WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter256CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 256 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 256 1 ≤
          inverseSquareSingleReverseAfter256CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore256Window_round_256_step_mem_after256Window
        hlo hhi
  rw [show 256 = 1 + 255 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 256 - 1 = 255 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 256 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `128^{-2}`
boundary step, after the `255^{-2}, ..., 129^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore128CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16711843 - 33) (-7 : ℤ)

/-- Upper endpoint for the whole-window state just before the `128^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore128CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16711843 + 32) (-7 : ℤ)

/-- The concrete before-`128` candidate lies in the before-`128`
whole-window target. -/
theorem inverseSquareSingleReverseBefore128Candidate_mem_before128Window :
    inverseSquareSingleReverseBefore128CandidateWindowLower ≤
        inverseSquareSingleReverseBefore128Candidate ∧
      inverseSquareSingleReverseBefore128Candidate ≤
        inverseSquareSingleReverseBefore128CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore128CandidateWindowLower,
      inverseSquareSingleReverseBefore128CandidateWindowUpper,
      inverseSquareSingleReverseBefore128Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after `n` additions inside the `255^{-2}, ..., 129^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter256BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8405008 - 33) +
      inverseSquareSingleReverseScaledMantissaPrefix 32 255 n) (-7 : ℤ)

/-- Upper endpoint after `n` additions inside the `255^{-2}, ..., 129^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter256BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8405008 + 32) +
      inverseSquareSingleReverseScaledMantissaPrefix 32 255 n) (-7 : ℤ)

theorem inverseSquareSingleReverseAfter256BandWindowLower_zero :
    inverseSquareSingleReverseAfter256BandWindowLower 0 =
      inverseSquareSingleReverseAfter256CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter256BandWindowLower,
    inverseSquareSingleReverseAfter256CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter256BandWindowUpper_zero :
    inverseSquareSingleReverseAfter256BandWindowUpper 0 =
      inverseSquareSingleReverseAfter256CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter256BandWindowUpper,
    inverseSquareSingleReverseAfter256CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter256BandWindowLower_final :
    inverseSquareSingleReverseAfter256BandWindowLower 127 =
      inverseSquareSingleReverseBefore128CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8405008 - 33) +
          inverseSquareSingleReverseScaledMantissaPrefix 32 255 127)
        (-7 : ℤ) =
      inverseSquareSingleReverseBefore128CandidateWindowLower
  rw [inverseSquareSingleReverseAfter256Prefix_255_to_129_eq]
  norm_num [inverseSquareSingleReverseBefore128CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter256BandWindowUpper_final :
    inverseSquareSingleReverseAfter256BandWindowUpper 127 =
      inverseSquareSingleReverseBefore128CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8405008 + 32) +
          inverseSquareSingleReverseScaledMantissaPrefix 32 255 127)
        (-7 : ℤ) =
      inverseSquareSingleReverseBefore128CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter256Prefix_255_to_129_eq]
  norm_num [inverseSquareSingleReverseBefore128CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the fifth whole-window reverse suffix
band. It checks that the already-certified `255^{-2}, ..., 129^{-2}`
increments remain normal for both endpoints of the post-`256` window. -/
def inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificateBool :
    Bool :=
  (List.range 127).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 32 255 n
    let k := 255 - n
    let d := inverseSquareSingleScaledMantissaIncrement 32 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 32 ∧
      2 ^ 32 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8405008 - 33 + p) + d - 1 ∧
      (8405008 + 32 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the fifth whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise endpoint-safety extraction for the fifth whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificate
    {n : ℕ} (hn : n < 127) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 32 255 n
    let k := 255 - n
    let d := inverseSquareSingleScaledMantissaIncrement 32 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 32 ∧
      2 ^ 32 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8405008 - 33 + p) + d - 1 ∧
      (8405008 + 32 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 127,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 32 255 x
        let k := 255 - x
        let d := inverseSquareSingleScaledMantissaIncrement 32 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 32 ∧
          2 ^ 32 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8405008 - 33 + p) + d - 1 ∧
          (8405008 + 32 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the fifth whole-window reverse suffix band.
If the current accumulator is inside the prefix window after `n` additions,
then the next rounded addition stays inside the prefix window after `n+1`
additions. -/
theorem inverseSquareSingleReverseAfter256BandWindow_round_step_mem
    {n : ℕ} (hn : n < 127) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter256BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter256BandWindowUpper n) :
    inverseSquareSingleReverseAfter256BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (255 - n) ∧
      inverseSquareSingleForwardStep start (255 - n) ≤
        inverseSquareSingleReverseAfter256BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 32 255 n
  let k := 255 - n
  let d := inverseSquareSingleScaledMantissaIncrement 32 k
  let mL := (8405008 - 33) + p
  let mU := (8405008 + 32) + p
  let e : ℤ := -7
  have hcert :=
    inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificate
      hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter256BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter256BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 32)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter256BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter256BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter256BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 32)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter256BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter256BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter256BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter256BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter256BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 32)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter256BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8404975 +
              (inverseSquareSingleReverseScaledMantissaPrefix 32 255 n +
                inverseSquareSingleScaledMantissaIncrement 32 (255 - n)))
            (-7 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8404975 +
              (inverseSquareSingleReverseScaledMantissaPrefix 32 255 n +
                inverseSquareSingleScaledMantissaIncrement 32 (255 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter256BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter256BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter256BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter256BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter256BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 32)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter256BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8405040 +
              (inverseSquareSingleReverseScaledMantissaPrefix 32 255 n +
                inverseSquareSingleScaledMantissaIncrement 32 (255 - n)))
            (-7 : ℤ) := by
      have hnat :
          mU + d =
            8405040 +
              (inverseSquareSingleReverseScaledMantissaPrefix 32 255 n +
                inverseSquareSingleScaledMantissaIncrement 32 (255 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter256BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `255^{-2}, ..., 129^{-2}` band:
any start in the post-`256` candidate window remains in the corresponding
prefix window after any certified number of same-exponent additions. -/
theorem inverseSquareSingleReverseAfter256BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter256CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter256CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 127) :
    inverseSquareSingleReverseAfter256BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 255 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 255 n ≤
        inverseSquareSingleReverseAfter256BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter256BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter256BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 127 := by omega
      have hnlt : n < 127 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter256BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window band certificate for the `255^{-2}, ..., 129^{-2}` reverse
suffix chunk: every post-`256` window start lands in the before-`128`
window after the 127 same-exponent additions. -/
def inverseSquareSingleReverseAfter256Band255ToBefore128Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter256CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter256CandidateWindowUpper →
        inverseSquareSingleReverseBefore128CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 255 127 ∧
          inverseSquareSingleReverseAccumulatorFrom start 255 127 ≤
            inverseSquareSingleReverseBefore128CandidateWindowUpper

/-- Closed whole-window band certificate for the `255^{-2}, ..., 129^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter256Band255ToBefore128Window_closed :
    inverseSquareSingleReverseAfter256Band255ToBefore128Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter256BandWindow_prefix_mem
      (start := start) hlo hhi 127 (by norm_num)
  rw [← inverseSquareSingleReverseAfter256BandWindowLower_final,
    ← inverseSquareSingleReverseAfter256BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`256` candidate band lands in the before-`128`
window.  This records that the whole-window band target is centered on the
already-closed concrete chunk certificate. -/
theorem inverseSquareSingleReverseAfter256Candidate_band255_to_before128_mem_before128Window :
    inverseSquareSingleReverseBefore128CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter256Candidate 255 127 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter256Candidate 255 127 ≤
        inverseSquareSingleReverseBefore128CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter256Accumulator_255_to_before128]
  exact inverseSquareSingleReverseBefore128Candidate_mem_before128Window

/-- Remaining suffix certificate after the `255^{-2}, ..., 129^{-2}` band
has placed the state in the before-`128` whole-window target. -/
def inverseSquareSingleReverseBefore128WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore128CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore128CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 128 128 =
          inverseSquareSingleReversePrintedAccumulator

/-- A whole-window certificate for the `255^{-2}, ..., 129^{-2}` band plus a
before-`128` suffix certificate imply the post-`256` suffix certificate. -/
theorem inverseSquareSingleReverseAfter256WindowMapsToPrinted_of_band255_to_before128Window
    (hband : inverseSquareSingleReverseAfter256Band255ToBefore128Window)
    (hsuffix : inverseSquareSingleReverseBefore128WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter256WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 255 = 127 + 128 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 255 - 127 = 128 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 255 127)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`128` whole-window suffix map is supplied, the entire
post-`256` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter256WindowMapsToPrinted_of_before128Window
    (hsuffix : inverseSquareSingleReverseBefore128WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter256WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter256WindowMapsToPrinted_of_band255_to_before128Window
    inverseSquareSingleReverseAfter256Band255ToBefore128Window_closed
    hsuffix

/-- Once the before-`128` whole-window suffix map is supplied, the
before-`256` whole-window suffix map is closed by the rounded boundary step
and certified same-exponent band. -/
theorem inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before128Window
    (hsuffix : inverseSquareSingleReverseBefore128WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore256WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_after256Window
    (inverseSquareSingleReverseAfter256WindowMapsToPrinted_of_before128Window
      hsuffix)

/-- Once the before-`128` whole-window suffix map is supplied, the
before-`512` whole-window suffix map is closed through the before-`256`
boundary and band. -/
theorem inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before128Window
    (hsuffix : inverseSquareSingleReverseBefore128WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore512WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before256Window
    (inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before128Window
      hsuffix)

/-- Once the before-`128` whole-window suffix map is supplied, the
before-`1024` whole-window suffix map is closed through the before-`256`
boundary and band. -/
theorem inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before128Window
    (hsuffix : inverseSquareSingleReverseBefore128WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore1024WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before256Window
    (inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before128Window
      hsuffix)

/-- Once the before-`128` whole-window suffix map is supplied, the
before-`2048` whole-window suffix map is closed through the before-`256`
boundary and band. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before128Window
    (hsuffix : inverseSquareSingleReverseBefore128WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before256Window
    (inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before128Window
      hsuffix)

/-- Lower endpoint of the whole-window suffix state immediately after the
rounded `128^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter128CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8421458 - 17) (-6 : ℤ)

/-- Upper endpoint of the whole-window suffix state immediately after the
rounded `128^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter128CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8421458 + 16) (-6 : ℤ)

/-- The named after-`128` candidate lies in the post-`128` whole-window
target. -/
theorem inverseSquareSingleReverseAfter128Candidate_mem_after128Window :
    inverseSquareSingleReverseAfter128CandidateWindowLower ≤
        inverseSquareSingleReverseAfter128Candidate ∧
      inverseSquareSingleReverseAfter128Candidate ≤
        inverseSquareSingleReverseAfter128CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter128CandidateWindowLower,
      inverseSquareSingleReverseAfter128CandidateWindowUpper,
      inverseSquareSingleReverseAfter128Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `128^{-2}` maps the before-`128` whole window into
the exact post-`128` enclosure. -/
theorem inverseSquareSingleReverseBefore128Window_add_128_term_mem_after128Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore128CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore128CandidateWindowUpper) :
    inverseSquareSingleReverseAfter128CandidateWindowLower ≤
        s + inverseSquareTerm 128 ∧
      s + inverseSquareTerm 128 ≤
        inverseSquareSingleReverseAfter128CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter128CandidateWindowLower ≤
          inverseSquareSingleReverseBefore128CandidateWindowLower +
            inverseSquareTerm 128 := by
      norm_num [inverseSquareSingleReverseAfter128CandidateWindowLower,
        inverseSquareSingleReverseBefore128CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore128CandidateWindowLower +
            inverseSquareTerm 128 ≤
          s + inverseSquareTerm 128 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore128CandidateWindowUpper +
            inverseSquareTerm 128 ≤
          inverseSquareSingleReverseAfter128CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseBefore128CandidateWindowUpper,
        inverseSquareSingleReverseAfter128CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 128 ≤
          inverseSquareSingleReverseBefore128CandidateWindowUpper +
            inverseSquareTerm 128 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `128^{-2}` maps every before-`128` whole-window
start into the post-`128` whole-window suffix state. -/
theorem inverseSquareSingleReverseBefore128Window_round_128_step_mem_after128Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore128CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore128CandidateWindowUpper) :
    inverseSquareSingleReverseAfter128CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 128 ∧
      inverseSquareSingleForwardStep s 128 ≤
        inverseSquareSingleReverseAfter128CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore128Window_add_128_term_mem_after128Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter128CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8421458 - 17, (-6 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter128CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8421458 + 16, (-6 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 128)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 128)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 128)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-`128` form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter128WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter128CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter128CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 127 127 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`128` whole-window suffix certificate implies the before-`128`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_after128Window
    (hsuffix : inverseSquareSingleReverseAfter128WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore128WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter128CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 128 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 128 1 ≤
          inverseSquareSingleReverseAfter128CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore128Window_round_128_step_mem_after128Window
        hlo hhi
  rw [show 128 = 1 + 127 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 128 - 1 = 127 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 128 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `64^{-2}`
boundary step, after the `127^{-2}, ..., 65^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore64CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16646819 - 17) (-6 : ℤ)

/-- Upper endpoint for the whole-window state just before the `64^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore64CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16646819 + 16) (-6 : ℤ)

/-- The concrete before-`64` candidate lies in the before-`64`
whole-window target. -/
theorem inverseSquareSingleReverseBefore64Candidate_mem_before64Window :
    inverseSquareSingleReverseBefore64CandidateWindowLower ≤
        inverseSquareSingleReverseBefore64Candidate ∧
      inverseSquareSingleReverseBefore64Candidate ≤
        inverseSquareSingleReverseBefore64CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore64CandidateWindowLower,
      inverseSquareSingleReverseBefore64CandidateWindowUpper,
      inverseSquareSingleReverseBefore64Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after `n` additions inside the `127^{-2}, ..., 65^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter128BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8421458 - 17) +
      inverseSquareSingleReverseScaledMantissaPrefix 31 127 n) (-6 : ℤ)

/-- Upper endpoint after `n` additions inside the `127^{-2}, ..., 65^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter128BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8421458 + 16) +
      inverseSquareSingleReverseScaledMantissaPrefix 31 127 n) (-6 : ℤ)

theorem inverseSquareSingleReverseAfter128BandWindowLower_zero :
    inverseSquareSingleReverseAfter128BandWindowLower 0 =
      inverseSquareSingleReverseAfter128CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter128BandWindowLower,
    inverseSquareSingleReverseAfter128CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter128BandWindowUpper_zero :
    inverseSquareSingleReverseAfter128BandWindowUpper 0 =
      inverseSquareSingleReverseAfter128CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter128BandWindowUpper,
    inverseSquareSingleReverseAfter128CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter128BandWindowLower_final :
    inverseSquareSingleReverseAfter128BandWindowLower 63 =
      inverseSquareSingleReverseBefore64CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8421458 - 17) +
          inverseSquareSingleReverseScaledMantissaPrefix 31 127 63)
        (-6 : ℤ) =
      inverseSquareSingleReverseBefore64CandidateWindowLower
  rw [inverseSquareSingleReverseAfter128Prefix_127_to_65_eq]
  norm_num [inverseSquareSingleReverseBefore64CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter128BandWindowUpper_final :
    inverseSquareSingleReverseAfter128BandWindowUpper 63 =
      inverseSquareSingleReverseBefore64CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8421458 + 16) +
          inverseSquareSingleReverseScaledMantissaPrefix 31 127 63)
        (-6 : ℤ) =
      inverseSquareSingleReverseBefore64CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter128Prefix_127_to_65_eq]
  norm_num [inverseSquareSingleReverseBefore64CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the sixth whole-window reverse suffix
band. It checks that the already-certified `127^{-2}, ..., 65^{-2}`
increments remain normal for both endpoints of the post-`128` window. -/
def inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificateBool :
    Bool :=
  (List.range 63).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 31 127 n
    let k := 127 - n
    let d := inverseSquareSingleScaledMantissaIncrement 31 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 31 ∧
      2 ^ 31 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8421458 - 17 + p) + d - 1 ∧
      (8421458 + 16 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the sixth whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise endpoint-safety extraction for the sixth whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificate
    {n : ℕ} (hn : n < 63) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 31 127 n
    let k := 127 - n
    let d := inverseSquareSingleScaledMantissaIncrement 31 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 31 ∧
      2 ^ 31 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8421458 - 17 + p) + d - 1 ∧
      (8421458 + 16 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 63,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 31 127 x
        let k := 127 - x
        let d := inverseSquareSingleScaledMantissaIncrement 31 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 31 ∧
          2 ^ 31 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8421458 - 17 + p) + d - 1 ∧
          (8421458 + 16 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the sixth whole-window reverse suffix band.
If the current accumulator is inside the prefix window after `n` additions,
then the next rounded addition stays inside the prefix window after `n+1`
additions. -/
theorem inverseSquareSingleReverseAfter128BandWindow_round_step_mem
    {n : ℕ} (hn : n < 63) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter128BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter128BandWindowUpper n) :
    inverseSquareSingleReverseAfter128BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (127 - n) ∧
      inverseSquareSingleForwardStep start (127 - n) ≤
        inverseSquareSingleReverseAfter128BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 31 127 n
  let k := 127 - n
  let d := inverseSquareSingleScaledMantissaIncrement 31 k
  let mL := (8421458 - 17) + p
  let mU := (8421458 + 16) + p
  let e : ℤ := -6
  have hcert :=
    inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificate
      hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter128BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter128BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 31)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter128BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter128BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter128BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 31)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter128BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter128BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter128BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter128BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter128BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 31)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter128BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8421441 +
              (inverseSquareSingleReverseScaledMantissaPrefix 31 127 n +
                inverseSquareSingleScaledMantissaIncrement 31 (127 - n)))
            (-6 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8421441 +
              (inverseSquareSingleReverseScaledMantissaPrefix 31 127 n +
                inverseSquareSingleScaledMantissaIncrement 31 (127 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter128BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter128BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter128BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter128BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter128BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 31)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter128BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8421474 +
              (inverseSquareSingleReverseScaledMantissaPrefix 31 127 n +
                inverseSquareSingleScaledMantissaIncrement 31 (127 - n)))
            (-6 : ℤ) := by
      have hnat :
          mU + d =
            8421474 +
              (inverseSquareSingleReverseScaledMantissaPrefix 31 127 n +
                inverseSquareSingleScaledMantissaIncrement 31 (127 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter128BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `127^{-2}, ..., 65^{-2}` band:
any start in the post-`128` candidate window remains in the corresponding
prefix window after any certified number of same-exponent additions. -/
theorem inverseSquareSingleReverseAfter128BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter128CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter128CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 63) :
    inverseSquareSingleReverseAfter128BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 127 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 127 n ≤
        inverseSquareSingleReverseAfter128BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter128BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter128BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 63 := by omega
      have hnlt : n < 63 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter128BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window band certificate for the `127^{-2}, ..., 65^{-2}` reverse
suffix chunk: every post-`128` window start lands in the before-`64`
window after the 63 same-exponent additions. -/
def inverseSquareSingleReverseAfter128Band127ToBefore64Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter128CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter128CandidateWindowUpper →
        inverseSquareSingleReverseBefore64CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 127 63 ∧
          inverseSquareSingleReverseAccumulatorFrom start 127 63 ≤
            inverseSquareSingleReverseBefore64CandidateWindowUpper

/-- Closed whole-window band certificate for the `127^{-2}, ..., 65^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter128Band127ToBefore64Window_closed :
    inverseSquareSingleReverseAfter128Band127ToBefore64Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter128BandWindow_prefix_mem
      (start := start) hlo hhi 63 (by norm_num)
  rw [← inverseSquareSingleReverseAfter128BandWindowLower_final,
    ← inverseSquareSingleReverseAfter128BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`128` candidate band lands in the before-`64`
window.  This records that the whole-window band target is centered on the
already-closed concrete chunk certificate. -/
theorem inverseSquareSingleReverseAfter128Candidate_band127_to_before64_mem_before64Window :
    inverseSquareSingleReverseBefore64CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter128Candidate 127 63 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter128Candidate 127 63 ≤
        inverseSquareSingleReverseBefore64CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter128Accumulator_127_to_before64]
  exact inverseSquareSingleReverseBefore64Candidate_mem_before64Window

/-- Remaining suffix certificate after the `127^{-2}, ..., 65^{-2}` band
has placed the state in the before-`64` whole-window target. -/
def inverseSquareSingleReverseBefore64WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore64CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore64CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 64 64 =
          inverseSquareSingleReversePrintedAccumulator

/-- A whole-window certificate for the `127^{-2}, ..., 65^{-2}` band plus a
before-`64` suffix certificate imply the post-`128` suffix certificate. -/
theorem inverseSquareSingleReverseAfter128WindowMapsToPrinted_of_band127_to_before64Window
    (hband : inverseSquareSingleReverseAfter128Band127ToBefore64Window)
    (hsuffix : inverseSquareSingleReverseBefore64WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter128WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 127 = 63 + 64 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 127 - 63 = 64 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 127 63)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`64` whole-window suffix map is supplied, the entire
post-`128` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter128WindowMapsToPrinted_of_before64Window
    (hsuffix : inverseSquareSingleReverseBefore64WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter128WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter128WindowMapsToPrinted_of_band127_to_before64Window
    inverseSquareSingleReverseAfter128Band127ToBefore64Window_closed
    hsuffix

/-- Once the before-`64` whole-window suffix map is supplied, the
before-`128` whole-window suffix map is closed by the rounded boundary step
and certified same-exponent band. -/
theorem inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before64Window
    (hsuffix : inverseSquareSingleReverseBefore64WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore128WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_after128Window
    (inverseSquareSingleReverseAfter128WindowMapsToPrinted_of_before64Window
      hsuffix)

/-- Once the before-`64` whole-window suffix map is supplied, the
before-`256` whole-window suffix map is closed through the before-`128`
boundary and band. -/
theorem inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before64Window
    (hsuffix : inverseSquareSingleReverseBefore64WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore256WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before128Window
    (inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before64Window
      hsuffix)

/-- Once the before-`64` whole-window suffix map is supplied, the
before-`512` whole-window suffix map is closed through the before-`128`
boundary and band. -/
theorem inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before64Window
    (hsuffix : inverseSquareSingleReverseBefore64WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore512WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before128Window
    (inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before64Window
      hsuffix)

/-- Once the before-`64` whole-window suffix map is supplied, the
before-`1024` whole-window suffix map is closed through the before-`128`
boundary and band. -/
theorem inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before64Window
    (hsuffix : inverseSquareSingleReverseBefore64WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore1024WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before128Window
    (inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before64Window
      hsuffix)

/-- Once the before-`64` whole-window suffix map is supplied, the
before-`2048` whole-window suffix map is closed through the before-`128`
boundary and band. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before64Window
    (hsuffix : inverseSquareSingleReverseBefore64WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before128Window
    (inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before64Window
      hsuffix)

/-- Lower endpoint of the whole-window suffix state immediately after the
rounded `64^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter64CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8454482 - 9) (-5 : ℤ)

/-- Upper endpoint of the whole-window suffix state immediately after the
rounded `64^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter64CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8454482 + 8) (-5 : ℤ)

/-- The named after-`64` candidate lies in the post-`64` whole-window
target. -/
theorem inverseSquareSingleReverseAfter64Candidate_mem_after64Window :
    inverseSquareSingleReverseAfter64CandidateWindowLower ≤
        inverseSquareSingleReverseAfter64Candidate ∧
      inverseSquareSingleReverseAfter64Candidate ≤
        inverseSquareSingleReverseAfter64CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter64CandidateWindowLower,
      inverseSquareSingleReverseAfter64CandidateWindowUpper,
      inverseSquareSingleReverseAfter64Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `64^{-2}` maps the before-`64` whole window into
the exact post-`64` enclosure. -/
theorem inverseSquareSingleReverseBefore64Window_add_64_term_mem_after64Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore64CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore64CandidateWindowUpper) :
    inverseSquareSingleReverseAfter64CandidateWindowLower ≤
        s + inverseSquareTerm 64 ∧
      s + inverseSquareTerm 64 ≤
        inverseSquareSingleReverseAfter64CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter64CandidateWindowLower ≤
          inverseSquareSingleReverseBefore64CandidateWindowLower +
            inverseSquareTerm 64 := by
      norm_num [inverseSquareSingleReverseAfter64CandidateWindowLower,
        inverseSquareSingleReverseBefore64CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore64CandidateWindowLower +
            inverseSquareTerm 64 ≤
          s + inverseSquareTerm 64 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore64CandidateWindowUpper +
            inverseSquareTerm 64 ≤
          inverseSquareSingleReverseAfter64CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseBefore64CandidateWindowUpper,
        inverseSquareSingleReverseAfter64CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 64 ≤
          inverseSquareSingleReverseBefore64CandidateWindowUpper +
            inverseSquareTerm 64 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `64^{-2}` maps every before-`64` whole-window start
into the post-`64` whole-window suffix state. -/
theorem inverseSquareSingleReverseBefore64Window_round_64_step_mem_after64Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore64CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore64CandidateWindowUpper) :
    inverseSquareSingleReverseAfter64CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 64 ∧
      inverseSquareSingleForwardStep s 64 ≤
        inverseSquareSingleReverseAfter64CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore64Window_add_64_term_mem_after64Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter64CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8454482 - 9, (-5 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter64CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8454482 + 8, (-5 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 64)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 64)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 64)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-`64` form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter64WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter64CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter64CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 63 63 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`64` whole-window suffix certificate implies the before-`64`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_after64Window
    (hsuffix : inverseSquareSingleReverseAfter64WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore64WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter64CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 64 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 64 1 ≤
          inverseSquareSingleReverseAfter64CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore64Window_round_64_step_mem_after64Window
        hlo hhi
  rw [show 64 = 1 + 63 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 64 - 1 = 63 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 64 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `32^{-2}`
boundary step, after the `63^{-2}, ..., 33^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore32CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16517796 - 9) (-5 : ℤ)

/-- Upper endpoint for the whole-window state just before the `32^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore32CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16517796 + 8) (-5 : ℤ)

/-- The concrete before-`32` candidate lies in the before-`32`
whole-window target. -/
theorem inverseSquareSingleReverseBefore32Candidate_mem_before32Window :
    inverseSquareSingleReverseBefore32CandidateWindowLower ≤
        inverseSquareSingleReverseBefore32Candidate ∧
      inverseSquareSingleReverseBefore32Candidate ≤
        inverseSquareSingleReverseBefore32CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore32CandidateWindowLower,
      inverseSquareSingleReverseBefore32CandidateWindowUpper,
      inverseSquareSingleReverseBefore32Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after `n` additions inside the `63^{-2}, ..., 33^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter64BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8454482 - 9) +
      inverseSquareSingleReverseScaledMantissaPrefix 30 63 n) (-5 : ℤ)

/-- Upper endpoint after `n` additions inside the `63^{-2}, ..., 33^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter64BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8454482 + 8) +
      inverseSquareSingleReverseScaledMantissaPrefix 30 63 n) (-5 : ℤ)

theorem inverseSquareSingleReverseAfter64BandWindowLower_zero :
    inverseSquareSingleReverseAfter64BandWindowLower 0 =
      inverseSquareSingleReverseAfter64CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter64BandWindowLower,
    inverseSquareSingleReverseAfter64CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter64BandWindowUpper_zero :
    inverseSquareSingleReverseAfter64BandWindowUpper 0 =
      inverseSquareSingleReverseAfter64CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter64BandWindowUpper,
    inverseSquareSingleReverseAfter64CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter64BandWindowLower_final :
    inverseSquareSingleReverseAfter64BandWindowLower 31 =
      inverseSquareSingleReverseBefore32CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8454482 - 9) +
          inverseSquareSingleReverseScaledMantissaPrefix 30 63 31)
        (-5 : ℤ) =
      inverseSquareSingleReverseBefore32CandidateWindowLower
  rw [inverseSquareSingleReverseAfter64Prefix_63_to_33_eq]
  norm_num [inverseSquareSingleReverseBefore32CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter64BandWindowUpper_final :
    inverseSquareSingleReverseAfter64BandWindowUpper 31 =
      inverseSquareSingleReverseBefore32CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8454482 + 8) +
          inverseSquareSingleReverseScaledMantissaPrefix 30 63 31)
        (-5 : ℤ) =
      inverseSquareSingleReverseBefore32CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter64Prefix_63_to_33_eq]
  norm_num [inverseSquareSingleReverseBefore32CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the seventh whole-window reverse suffix
band. It checks that the already-certified `63^{-2}, ..., 33^{-2}`
increments remain normal for both endpoints of the post-`64` window. -/
def inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificateBool :
    Bool :=
  (List.range 31).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 30 63 n
    let k := 63 - n
    let d := inverseSquareSingleScaledMantissaIncrement 30 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 30 ∧
      2 ^ 30 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8454482 - 9 + p) + d - 1 ∧
      (8454482 + 8 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the seventh whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise endpoint-safety extraction for the seventh whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificate
    {n : ℕ} (hn : n < 31) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 30 63 n
    let k := 63 - n
    let d := inverseSquareSingleScaledMantissaIncrement 30 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 30 ∧
      2 ^ 30 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8454482 - 9 + p) + d - 1 ∧
      (8454482 + 8 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 31,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 30 63 x
        let k := 63 - x
        let d := inverseSquareSingleScaledMantissaIncrement 30 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 30 ∧
          2 ^ 30 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8454482 - 9 + p) + d - 1 ∧
          (8454482 + 8 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the seventh whole-window reverse suffix band.
If the current accumulator is inside the prefix window after `n` additions,
then the next rounded addition stays inside the prefix window after `n+1`
additions. -/
theorem inverseSquareSingleReverseAfter64BandWindow_round_step_mem
    {n : ℕ} (hn : n < 31) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter64BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter64BandWindowUpper n) :
    inverseSquareSingleReverseAfter64BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (63 - n) ∧
      inverseSquareSingleForwardStep start (63 - n) ≤
        inverseSquareSingleReverseAfter64BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 30 63 n
  let k := 63 - n
  let d := inverseSquareSingleScaledMantissaIncrement 30 k
  let mL := (8454482 - 9) + p
  let mU := (8454482 + 8) + p
  let e : ℤ := -5
  have hcert :=
    inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificate
      hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter64BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter64BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 30)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter64BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter64BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter64BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 30)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter64BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter64BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter64BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter64BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter64BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 30)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter64BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8454473 +
              (inverseSquareSingleReverseScaledMantissaPrefix 30 63 n +
                inverseSquareSingleScaledMantissaIncrement 30 (63 - n)))
            (-5 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8454473 +
              (inverseSquareSingleReverseScaledMantissaPrefix 30 63 n +
                inverseSquareSingleScaledMantissaIncrement 30 (63 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter64BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter64BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter64BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter64BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter64BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 30)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter64BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8454490 +
              (inverseSquareSingleReverseScaledMantissaPrefix 30 63 n +
                inverseSquareSingleScaledMantissaIncrement 30 (63 - n)))
            (-5 : ℤ) := by
      have hnat :
          mU + d =
            8454490 +
              (inverseSquareSingleReverseScaledMantissaPrefix 30 63 n +
                inverseSquareSingleScaledMantissaIncrement 30 (63 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter64BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `63^{-2}, ..., 33^{-2}` band:
any start in the post-`64` candidate window remains in the corresponding
prefix window after any certified number of same-exponent additions. -/
theorem inverseSquareSingleReverseAfter64BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter64CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter64CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 31) :
    inverseSquareSingleReverseAfter64BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 63 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 63 n ≤
        inverseSquareSingleReverseAfter64BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter64BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter64BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 31 := by omega
      have hnlt : n < 31 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter64BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window band certificate for the `63^{-2}, ..., 33^{-2}` reverse
suffix chunk: every post-`64` window start lands in the before-`32`
window after the 31 same-exponent additions. -/
def inverseSquareSingleReverseAfter64Band63ToBefore32Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter64CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter64CandidateWindowUpper →
        inverseSquareSingleReverseBefore32CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 63 31 ∧
          inverseSquareSingleReverseAccumulatorFrom start 63 31 ≤
            inverseSquareSingleReverseBefore32CandidateWindowUpper

/-- Closed whole-window band certificate for the `63^{-2}, ..., 33^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter64Band63ToBefore32Window_closed :
    inverseSquareSingleReverseAfter64Band63ToBefore32Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter64BandWindow_prefix_mem
      (start := start) hlo hhi 31 (by norm_num)
  rw [← inverseSquareSingleReverseAfter64BandWindowLower_final,
    ← inverseSquareSingleReverseAfter64BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`64` candidate band lands in the before-`32` window.
This records that the whole-window band target is centered on the
already-closed concrete chunk certificate. -/
theorem inverseSquareSingleReverseAfter64Candidate_band63_to_before32_mem_before32Window :
    inverseSquareSingleReverseBefore32CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter64Candidate 63 31 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter64Candidate 63 31 ≤
        inverseSquareSingleReverseBefore32CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter64Accumulator_63_to_before32]
  exact inverseSquareSingleReverseBefore32Candidate_mem_before32Window

/-- Remaining suffix certificate after the `63^{-2}, ..., 33^{-2}` band has
placed the state in the before-`32` whole-window target. -/
def inverseSquareSingleReverseBefore32WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore32CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore32CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 32 32 =
          inverseSquareSingleReversePrintedAccumulator

/-- A whole-window certificate for the `63^{-2}, ..., 33^{-2}` band plus a
before-`32` suffix certificate imply the post-`64` suffix certificate. -/
theorem inverseSquareSingleReverseAfter64WindowMapsToPrinted_of_band63_to_before32Window
    (hband : inverseSquareSingleReverseAfter64Band63ToBefore32Window)
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter64WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 63 = 31 + 32 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 63 - 31 = 32 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 63 31)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`32` whole-window suffix map is supplied, the entire
post-`64` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter64WindowMapsToPrinted_of_before32Window
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter64WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter64WindowMapsToPrinted_of_band63_to_before32Window
    inverseSquareSingleReverseAfter64Band63ToBefore32Window_closed
    hsuffix

/-- Once the before-`32` whole-window suffix map is supplied, the before-`64`
whole-window suffix map is closed by the rounded boundary step and certified
same-exponent band. -/
theorem inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore64WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_after64Window
    (inverseSquareSingleReverseAfter64WindowMapsToPrinted_of_before32Window
      hsuffix)

/-- Once the before-`32` whole-window suffix map is supplied, the before-`128`
whole-window suffix map is closed through the before-`64` boundary and band. -/
theorem inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before32Window
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore128WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before64Window
    (inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window
      hsuffix)

/-- Once the before-`32` whole-window suffix map is supplied, the before-`256`
whole-window suffix map is closed through the before-`64` boundary and band. -/
theorem inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before32Window
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore256WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before64Window
    (inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window
      hsuffix)

/-- Once the before-`32` whole-window suffix map is supplied, the before-`512`
whole-window suffix map is closed through the before-`64` boundary and band. -/
theorem inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before32Window
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore512WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before64Window
    (inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window
      hsuffix)

/-- Once the before-`32` whole-window suffix map is supplied, the before-`1024`
whole-window suffix map is closed through the before-`64` boundary and band. -/
theorem inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before32Window
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore1024WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before64Window
    (inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window
      hsuffix)

/-- Once the before-`32` whole-window suffix map is supplied, the before-`2048`
whole-window suffix map is closed through the before-`64` boundary and band. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before32Window
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before64Window
    (inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window
      hsuffix)

/-- Lower endpoint of the whole-window suffix state immediately after the
rounded `32^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter32CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8521042 - 5) (-4 : ℤ)

/-- Upper endpoint of the whole-window suffix state immediately after the
rounded `32^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter32CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8521042 + 4) (-4 : ℤ)

/-- The named after-`32` candidate lies in the post-`32` whole-window target. -/
theorem inverseSquareSingleReverseAfter32Candidate_mem_after32Window :
    inverseSquareSingleReverseAfter32CandidateWindowLower ≤
        inverseSquareSingleReverseAfter32Candidate ∧
      inverseSquareSingleReverseAfter32Candidate ≤
        inverseSquareSingleReverseAfter32CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter32CandidateWindowLower,
      inverseSquareSingleReverseAfter32CandidateWindowUpper,
      inverseSquareSingleReverseAfter32Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `32^{-2}` maps the before-`32` whole window into the
exact post-`32` enclosure. -/
theorem inverseSquareSingleReverseBefore32Window_add_32_term_mem_after32Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore32CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore32CandidateWindowUpper) :
    inverseSquareSingleReverseAfter32CandidateWindowLower ≤
        s + inverseSquareTerm 32 ∧
      s + inverseSquareTerm 32 ≤
        inverseSquareSingleReverseAfter32CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter32CandidateWindowLower ≤
          inverseSquareSingleReverseBefore32CandidateWindowLower +
            inverseSquareTerm 32 := by
      norm_num [inverseSquareSingleReverseAfter32CandidateWindowLower,
        inverseSquareSingleReverseBefore32CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore32CandidateWindowLower +
            inverseSquareTerm 32 ≤
          s + inverseSquareTerm 32 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore32CandidateWindowUpper +
            inverseSquareTerm 32 ≤
          inverseSquareSingleReverseAfter32CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseBefore32CandidateWindowUpper,
        inverseSquareSingleReverseAfter32CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 32 ≤
          inverseSquareSingleReverseBefore32CandidateWindowUpper +
            inverseSquareTerm 32 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `32^{-2}` maps every before-`32` whole-window start
into the post-`32` whole-window suffix state. -/
theorem inverseSquareSingleReverseBefore32Window_round_32_step_mem_after32Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore32CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore32CandidateWindowUpper) :
    inverseSquareSingleReverseAfter32CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 32 ∧
      inverseSquareSingleForwardStep s 32 ≤
        inverseSquareSingleReverseAfter32CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore32Window_add_32_term_mem_after32Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter32CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8521042 - 5, (-4 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter32CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8521042 + 4, (-4 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 32)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 32)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 32)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-`32` form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter32WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter32CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter32CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 31 31 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`32` whole-window suffix certificate implies the before-`32`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_after32Window
    (hsuffix : inverseSquareSingleReverseAfter32WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore32WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter32CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 32 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 32 1 ≤
          inverseSquareSingleReverseAfter32CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore32Window_round_32_step_mem_after32Window
        hlo hhi
  rw [show 32 = 1 + 31 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 32 - 1 = 31 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 32 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `16^{-2}`
boundary step, after the `31^{-2}, ..., 17^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore16CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16263839 - 5) (-4 : ℤ)

/-- Upper endpoint for the whole-window state just before the `16^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore16CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (16263839 + 4) (-4 : ℤ)

/-- The concrete before-`16` candidate lies in the before-`16`
whole-window target. -/
theorem inverseSquareSingleReverseBefore16Candidate_mem_before16Window :
    inverseSquareSingleReverseBefore16CandidateWindowLower ≤
        inverseSquareSingleReverseBefore16Candidate ∧
      inverseSquareSingleReverseBefore16Candidate ≤
        inverseSquareSingleReverseBefore16CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore16CandidateWindowLower,
      inverseSquareSingleReverseBefore16CandidateWindowUpper,
      inverseSquareSingleReverseBefore16Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after `n` additions inside the `31^{-2}, ..., 17^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter32BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8521042 - 5) +
      inverseSquareSingleReverseScaledMantissaPrefix 29 31 n) (-4 : ℤ)

/-- Upper endpoint after `n` additions inside the `31^{-2}, ..., 17^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter32BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8521042 + 4) +
      inverseSquareSingleReverseScaledMantissaPrefix 29 31 n) (-4 : ℤ)

theorem inverseSquareSingleReverseAfter32BandWindowLower_zero :
    inverseSquareSingleReverseAfter32BandWindowLower 0 =
      inverseSquareSingleReverseAfter32CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter32BandWindowLower,
    inverseSquareSingleReverseAfter32CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter32BandWindowUpper_zero :
    inverseSquareSingleReverseAfter32BandWindowUpper 0 =
      inverseSquareSingleReverseAfter32CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter32BandWindowUpper,
    inverseSquareSingleReverseAfter32CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter32BandWindowLower_final :
    inverseSquareSingleReverseAfter32BandWindowLower 15 =
      inverseSquareSingleReverseBefore16CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8521042 - 5) +
          inverseSquareSingleReverseScaledMantissaPrefix 29 31 15)
        (-4 : ℤ) =
      inverseSquareSingleReverseBefore16CandidateWindowLower
  rw [inverseSquareSingleReverseAfter32Prefix_31_to_17_eq]
  norm_num [inverseSquareSingleReverseBefore16CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter32BandWindowUpper_final :
    inverseSquareSingleReverseAfter32BandWindowUpper 15 =
      inverseSquareSingleReverseBefore16CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8521042 + 4) +
          inverseSquareSingleReverseScaledMantissaPrefix 29 31 15)
        (-4 : ℤ) =
      inverseSquareSingleReverseBefore16CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter32Prefix_31_to_17_eq]
  norm_num [inverseSquareSingleReverseBefore16CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the eighth whole-window reverse suffix
band. It checks that the already-certified `31^{-2}, ..., 17^{-2}`
increments remain normal for both endpoints of the post-`32` window. -/
def inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificateBool :
    Bool :=
  (List.range 15).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 29 31 n
    let k := 31 - n
    let d := inverseSquareSingleScaledMantissaIncrement 29 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 29 ∧
      2 ^ 29 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8521042 - 5 + p) + d - 1 ∧
      (8521042 + 4 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the eighth whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise endpoint-safety extraction for the eighth whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificate
    {n : ℕ} (hn : n < 15) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 29 31 n
    let k := 31 - n
    let d := inverseSquareSingleScaledMantissaIncrement 29 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 29 ∧
      2 ^ 29 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8521042 - 5 + p) + d - 1 ∧
      (8521042 + 4 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 15,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 29 31 x
        let k := 31 - x
        let d := inverseSquareSingleScaledMantissaIncrement 29 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 29 ∧
          2 ^ 29 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8521042 - 5 + p) + d - 1 ∧
          (8521042 + 4 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the eighth whole-window reverse suffix band.
If the current accumulator is inside the prefix window after `n` additions,
then the next rounded addition stays inside the prefix window after `n+1`
additions. -/
theorem inverseSquareSingleReverseAfter32BandWindow_round_step_mem
    {n : ℕ} (hn : n < 15) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter32BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter32BandWindowUpper n) :
    inverseSquareSingleReverseAfter32BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (31 - n) ∧
      inverseSquareSingleForwardStep start (31 - n) ≤
        inverseSquareSingleReverseAfter32BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 29 31 n
  let k := 31 - n
  let d := inverseSquareSingleScaledMantissaIncrement 29 k
  let mL := (8521042 - 5) + p
  let mU := (8521042 + 4) + p
  let e : ℤ := -4
  have hcert :=
    inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificate hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter32BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter32BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 29)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter32BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter32BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter32BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 29)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter32BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter32BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter32BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter32BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter32BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 29)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter32BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8521037 +
              (inverseSquareSingleReverseScaledMantissaPrefix 29 31 n +
                inverseSquareSingleScaledMantissaIncrement 29 (31 - n)))
            (-4 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8521037 +
              (inverseSquareSingleReverseScaledMantissaPrefix 29 31 n +
                inverseSquareSingleScaledMantissaIncrement 29 (31 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter32BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter32BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter32BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter32BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter32BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 29)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter32BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8521046 +
              (inverseSquareSingleReverseScaledMantissaPrefix 29 31 n +
                inverseSquareSingleScaledMantissaIncrement 29 (31 - n)))
            (-4 : ℤ) := by
      have hnat :
          mU + d =
            8521046 +
              (inverseSquareSingleReverseScaledMantissaPrefix 29 31 n +
                inverseSquareSingleScaledMantissaIncrement 29 (31 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter32BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `31^{-2}, ..., 17^{-2}` band:
any start in the post-`32` candidate window remains in the corresponding
prefix window after any certified number of same-exponent additions. -/
theorem inverseSquareSingleReverseAfter32BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter32CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter32CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 15) :
    inverseSquareSingleReverseAfter32BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 31 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 31 n ≤
        inverseSquareSingleReverseAfter32BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter32BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter32BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 15 := by omega
      have hnlt : n < 15 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter32BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window band certificate for the `31^{-2}, ..., 17^{-2}` reverse
suffix chunk: every post-`32` window start lands in the before-`16`
window after the 15 same-exponent additions. -/
def inverseSquareSingleReverseAfter32Band31ToBefore16Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter32CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter32CandidateWindowUpper →
        inverseSquareSingleReverseBefore16CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 31 15 ∧
          inverseSquareSingleReverseAccumulatorFrom start 31 15 ≤
            inverseSquareSingleReverseBefore16CandidateWindowUpper

/-- Closed whole-window band certificate for the `31^{-2}, ..., 17^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter32Band31ToBefore16Window_closed :
    inverseSquareSingleReverseAfter32Band31ToBefore16Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter32BandWindow_prefix_mem
      (start := start) hlo hhi 15 (by norm_num)
  rw [← inverseSquareSingleReverseAfter32BandWindowLower_final,
    ← inverseSquareSingleReverseAfter32BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`32` candidate band lands in the before-`16` window.
This records that the whole-window band target is centered on the
already-closed concrete chunk certificate. -/
theorem inverseSquareSingleReverseAfter32Candidate_band31_to_before16_mem_before16Window :
    inverseSquareSingleReverseBefore16CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter32Candidate 31 15 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter32Candidate 31 15 ≤
        inverseSquareSingleReverseBefore16CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter32Accumulator_31_to_before16]
  exact inverseSquareSingleReverseBefore16Candidate_mem_before16Window

/-- Remaining suffix certificate after the `31^{-2}, ..., 17^{-2}` band has
placed the state in the before-`16` whole-window target. -/
def inverseSquareSingleReverseBefore16WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore16CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore16CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 16 16 =
          inverseSquareSingleReversePrintedAccumulator

/-- A whole-window certificate for the `31^{-2}, ..., 17^{-2}` band plus a
before-`16` suffix certificate imply the post-`32` suffix certificate. -/
theorem inverseSquareSingleReverseAfter32WindowMapsToPrinted_of_band31_to_before16Window
    (hband : inverseSquareSingleReverseAfter32Band31ToBefore16Window)
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter32WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 31 = 15 + 16 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 31 - 15 = 16 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 31 15)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`16` whole-window suffix map is supplied, the entire
post-`32` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter32WindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter32WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter32WindowMapsToPrinted_of_band31_to_before16Window
    inverseSquareSingleReverseAfter32Band31ToBefore16Window_closed
    hsuffix

/-- Once the before-`16` whole-window suffix map is supplied, the before-`32`
whole-window suffix map is closed by the rounded boundary step and certified
same-exponent band. -/
theorem inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore32WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_after32Window
    (inverseSquareSingleReverseAfter32WindowMapsToPrinted_of_before16Window
      hsuffix)

/-- Once the before-`16` whole-window suffix map is supplied, the before-`64`
whole-window suffix map is closed through the before-`32` boundary and band. -/
theorem inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore64WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window
    (inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window
      hsuffix)

/-- Once the before-`16` whole-window suffix map is supplied, the before-`128`
whole-window suffix map is closed through the before-`32` boundary and band. -/
theorem inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore128WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before32Window
    (inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window
      hsuffix)

/-- Once the before-`16` whole-window suffix map is supplied, the before-`256`
whole-window suffix map is closed through the before-`32` boundary and band. -/
theorem inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore256WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before32Window
    (inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window
      hsuffix)

/-- Once the before-`16` whole-window suffix map is supplied, the before-`512`
whole-window suffix map is closed through the before-`32` boundary and band. -/
theorem inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore512WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before32Window
    (inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window
      hsuffix)

/-- Once the before-`16` whole-window suffix map is supplied, the before-`1024`
whole-window suffix map is closed through the before-`32` boundary and band. -/
theorem inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore1024WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before32Window
    (inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window
      hsuffix)

/-- Once the before-`16` whole-window suffix map is supplied, the before-`2048`
whole-window suffix map is closed through the before-`32` boundary and band. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before32Window
    (inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window
      hsuffix)

/-- Lower endpoint of the whole-window suffix state immediately after the
rounded `16^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter16CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8656208 - 3) (-3 : ℤ)

/-- Upper endpoint of the whole-window suffix state immediately after the
rounded `16^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter16CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8656208 + 2) (-3 : ℤ)

/-- The named after-`16` candidate lies in the post-`16` whole-window target. -/
theorem inverseSquareSingleReverseAfter16Candidate_mem_after16Window :
    inverseSquareSingleReverseAfter16CandidateWindowLower ≤
        inverseSquareSingleReverseAfter16Candidate ∧
      inverseSquareSingleReverseAfter16Candidate ≤
        inverseSquareSingleReverseAfter16CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter16CandidateWindowLower,
      inverseSquareSingleReverseAfter16CandidateWindowUpper,
      inverseSquareSingleReverseAfter16Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `16^{-2}` maps the before-`16` whole window into the
exact post-`16` enclosure. -/
theorem inverseSquareSingleReverseBefore16Window_add_16_term_mem_after16Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore16CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore16CandidateWindowUpper) :
    inverseSquareSingleReverseAfter16CandidateWindowLower ≤
        s + inverseSquareTerm 16 ∧
      s + inverseSquareTerm 16 ≤
        inverseSquareSingleReverseAfter16CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter16CandidateWindowLower ≤
          inverseSquareSingleReverseBefore16CandidateWindowLower +
            inverseSquareTerm 16 := by
      norm_num [inverseSquareSingleReverseAfter16CandidateWindowLower,
        inverseSquareSingleReverseBefore16CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore16CandidateWindowLower +
            inverseSquareTerm 16 ≤
          s + inverseSquareTerm 16 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore16CandidateWindowUpper +
            inverseSquareTerm 16 ≤
          inverseSquareSingleReverseAfter16CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseBefore16CandidateWindowUpper,
        inverseSquareSingleReverseAfter16CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 16 ≤
          inverseSquareSingleReverseBefore16CandidateWindowUpper +
            inverseSquareTerm 16 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `16^{-2}` maps every before-`16` whole-window start
into the post-`16` whole-window suffix state. -/
theorem inverseSquareSingleReverseBefore16Window_round_16_step_mem_after16Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore16CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore16CandidateWindowUpper) :
    inverseSquareSingleReverseAfter16CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 16 ∧
      inverseSquareSingleForwardStep s 16 ≤
        inverseSquareSingleReverseAfter16CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore16Window_add_16_term_mem_after16Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter16CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8656208 - 3, (-3 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter16CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8656208 + 2, (-3 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 16)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 16)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 16)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-`16` form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter16WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter16CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter16CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 15 15 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`16` whole-window suffix certificate implies the before-`16`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_after16Window
    (hsuffix : inverseSquareSingleReverseAfter16WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore16WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter16CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 16 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 16 1 ≤
          inverseSquareSingleReverseAfter16CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore16Window_round_16_step_mem_after16Window
        hlo hhi
  rw [show 16 = 1 + 15 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 16 - 1 = 15 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 16 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `8^{-2}`
boundary step, after the `15^{-2}, ..., 9^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore8CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (15772194 - 3) (-3 : ℤ)

/-- Upper endpoint for the whole-window state just before the `8^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore8CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (15772194 + 2) (-3 : ℤ)

/-- The concrete before-`8` candidate lies in the before-`8`
whole-window target. -/
theorem inverseSquareSingleReverseBefore8Candidate_mem_before8Window :
    inverseSquareSingleReverseBefore8CandidateWindowLower ≤
        inverseSquareSingleReverseBefore8Candidate ∧
      inverseSquareSingleReverseBefore8Candidate ≤
        inverseSquareSingleReverseBefore8CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore8CandidateWindowLower,
      inverseSquareSingleReverseBefore8CandidateWindowUpper,
      inverseSquareSingleReverseBefore8Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after `n` additions inside the `15^{-2}, ..., 9^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter16BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8656208 - 3) +
      inverseSquareSingleReverseScaledMantissaPrefix 28 15 n) (-3 : ℤ)

/-- Upper endpoint after `n` additions inside the `15^{-2}, ..., 9^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter16BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8656208 + 2) +
      inverseSquareSingleReverseScaledMantissaPrefix 28 15 n) (-3 : ℤ)

theorem inverseSquareSingleReverseAfter16BandWindowLower_zero :
    inverseSquareSingleReverseAfter16BandWindowLower 0 =
      inverseSquareSingleReverseAfter16CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter16BandWindowLower,
    inverseSquareSingleReverseAfter16CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter16BandWindowUpper_zero :
    inverseSquareSingleReverseAfter16BandWindowUpper 0 =
      inverseSquareSingleReverseAfter16CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter16BandWindowUpper,
    inverseSquareSingleReverseAfter16CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter16BandWindowLower_final :
    inverseSquareSingleReverseAfter16BandWindowLower 7 =
      inverseSquareSingleReverseBefore8CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8656208 - 3) +
          inverseSquareSingleReverseScaledMantissaPrefix 28 15 7)
        (-3 : ℤ) =
      inverseSquareSingleReverseBefore8CandidateWindowLower
  rw [inverseSquareSingleReverseAfter16Prefix_15_to_9_eq]
  norm_num [inverseSquareSingleReverseBefore8CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter16BandWindowUpper_final :
    inverseSquareSingleReverseAfter16BandWindowUpper 7 =
      inverseSquareSingleReverseBefore8CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8656208 + 2) +
          inverseSquareSingleReverseScaledMantissaPrefix 28 15 7)
        (-3 : ℤ) =
      inverseSquareSingleReverseBefore8CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter16Prefix_15_to_9_eq]
  norm_num [inverseSquareSingleReverseBefore8CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the ninth whole-window reverse suffix
band. It checks that the already-certified `15^{-2}, ..., 9^{-2}`
increments remain normal for both endpoints of the post-`16` window. -/
def inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificateBool :
    Bool :=
  (List.range 7).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 28 15 n
    let k := 15 - n
    let d := inverseSquareSingleScaledMantissaIncrement 28 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 28 ∧
      2 ^ 28 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8656208 - 3 + p) + d - 1 ∧
      (8656208 + 2 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the ninth whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise endpoint-safety extraction for the ninth whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificate
    {n : ℕ} (hn : n < 7) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 28 15 n
    let k := 15 - n
    let d := inverseSquareSingleScaledMantissaIncrement 28 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 28 ∧
      2 ^ 28 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8656208 - 3 + p) + d - 1 ∧
      (8656208 + 2 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 7,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 28 15 x
        let k := 15 - x
        let d := inverseSquareSingleScaledMantissaIncrement 28 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 28 ∧
          2 ^ 28 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8656208 - 3 + p) + d - 1 ∧
          (8656208 + 2 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the ninth whole-window reverse suffix band.
If the current accumulator is inside the prefix window after `n` additions,
then the next rounded addition stays inside the prefix window after `n+1`
additions. -/
theorem inverseSquareSingleReverseAfter16BandWindow_round_step_mem
    {n : ℕ} (hn : n < 7) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter16BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter16BandWindowUpper n) :
    inverseSquareSingleReverseAfter16BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (15 - n) ∧
      inverseSquareSingleForwardStep start (15 - n) ≤
        inverseSquareSingleReverseAfter16BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 28 15 n
  let k := 15 - n
  let d := inverseSquareSingleScaledMantissaIncrement 28 k
  let mL := (8656208 - 3) + p
  let mU := (8656208 + 2) + p
  let e : ℤ := -3
  have hcert :=
    inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificate hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter16BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter16BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 28)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter16BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter16BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter16BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 28)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter16BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter16BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter16BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter16BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter16BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 28)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter16BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8656205 +
              (inverseSquareSingleReverseScaledMantissaPrefix 28 15 n +
                inverseSquareSingleScaledMantissaIncrement 28 (15 - n)))
            (-3 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8656205 +
              (inverseSquareSingleReverseScaledMantissaPrefix 28 15 n +
                inverseSquareSingleScaledMantissaIncrement 28 (15 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter16BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter16BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter16BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter16BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter16BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 28)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter16BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8656210 +
              (inverseSquareSingleReverseScaledMantissaPrefix 28 15 n +
                inverseSquareSingleScaledMantissaIncrement 28 (15 - n)))
            (-3 : ℤ) := by
      have hnat :
          mU + d =
            8656210 +
              (inverseSquareSingleReverseScaledMantissaPrefix 28 15 n +
                inverseSquareSingleScaledMantissaIncrement 28 (15 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter16BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `15^{-2}, ..., 9^{-2}` band:
any start in the post-`16` candidate window remains in the corresponding
prefix window after any certified number of same-exponent additions. -/
theorem inverseSquareSingleReverseAfter16BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter16CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter16CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 7) :
    inverseSquareSingleReverseAfter16BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 15 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 15 n ≤
        inverseSquareSingleReverseAfter16BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter16BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter16BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 7 := by omega
      have hnlt : n < 7 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter16BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window band certificate for the `15^{-2}, ..., 9^{-2}` reverse
suffix chunk: every post-`16` window start lands in the before-`8`
window after the seven same-exponent additions. -/
def inverseSquareSingleReverseAfter16Band15ToBefore8Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter16CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter16CandidateWindowUpper →
        inverseSquareSingleReverseBefore8CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 15 7 ∧
          inverseSquareSingleReverseAccumulatorFrom start 15 7 ≤
            inverseSquareSingleReverseBefore8CandidateWindowUpper

/-- Closed whole-window band certificate for the `15^{-2}, ..., 9^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter16Band15ToBefore8Window_closed :
    inverseSquareSingleReverseAfter16Band15ToBefore8Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter16BandWindow_prefix_mem
      (start := start) hlo hhi 7 (by norm_num)
  rw [← inverseSquareSingleReverseAfter16BandWindowLower_final,
    ← inverseSquareSingleReverseAfter16BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`16` candidate band lands in the before-`8` window.
This records that the whole-window band target is centered on the
already-closed concrete chunk certificate. -/
theorem inverseSquareSingleReverseAfter16Candidate_band15_to_before8_mem_before8Window :
    inverseSquareSingleReverseBefore8CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter16Candidate 15 7 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter16Candidate 15 7 ≤
        inverseSquareSingleReverseBefore8CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter16Accumulator_15_to_before8]
  exact inverseSquareSingleReverseBefore8Candidate_mem_before8Window

/-- Remaining suffix certificate after the `15^{-2}, ..., 9^{-2}` band has
placed the state in the before-`8` whole-window target. -/
def inverseSquareSingleReverseBefore8WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore8CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore8CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 8 8 =
          inverseSquareSingleReversePrintedAccumulator

/-- A whole-window certificate for the `15^{-2}, ..., 9^{-2}` band plus a
before-`8` suffix certificate imply the post-`16` suffix certificate. -/
theorem inverseSquareSingleReverseAfter16WindowMapsToPrinted_of_band15_to_before8Window
    (hband : inverseSquareSingleReverseAfter16Band15ToBefore8Window)
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter16WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 15 = 7 + 8 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 15 - 7 = 8 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 15 7)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`8` whole-window suffix map is supplied, the entire
post-`16` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter16WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter16WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter16WindowMapsToPrinted_of_band15_to_before8Window
    inverseSquareSingleReverseAfter16Band15ToBefore8Window_closed
    hsuffix

/-- Once the before-`8` whole-window suffix map is supplied, the before-`16`
whole-window suffix map is closed by the rounded boundary step and certified
same-exponent band. -/
theorem inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore16WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_after16Window
    (inverseSquareSingleReverseAfter16WindowMapsToPrinted_of_before8Window
      hsuffix)

/-- Once the before-`8` whole-window suffix map is supplied, the before-`32`
whole-window suffix map is closed through the before-`16` boundary and band. -/
theorem inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore32WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window
    (inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window
      hsuffix)

/-- Once the before-`8` whole-window suffix map is supplied, the before-`64`
whole-window suffix map is closed through the before-`16` boundary and band. -/
theorem inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore64WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before16Window
    (inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window
      hsuffix)

/-- Once the before-`8` whole-window suffix map is supplied, the before-`128`
whole-window suffix map is closed through the before-`16` boundary and band. -/
theorem inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore128WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before16Window
    (inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window
      hsuffix)

/-- Once the before-`8` whole-window suffix map is supplied, the before-`256`
whole-window suffix map is closed through the before-`16` boundary and band. -/
theorem inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore256WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before16Window
    (inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window
      hsuffix)

/-- Once the before-`8` whole-window suffix map is supplied, the before-`512`
whole-window suffix map is closed through the before-`16` boundary and band. -/
theorem inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore512WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before16Window
    (inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window
      hsuffix)

/-- Once the before-`8` whole-window suffix map is supplied, the before-`1024`
whole-window suffix map is closed through the before-`16` boundary and band. -/
theorem inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore1024WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before16Window
    (inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window
      hsuffix)

/-- Once the before-`8` whole-window suffix map is supplied, the before-`2048`
whole-window suffix map is closed through the before-`16` boundary and band. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before16Window
    (inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window
      hsuffix)

/-- Lower endpoint of the whole-window suffix state immediately after the
rounded `8^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter8CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8934673 - 2) (-2 : ℤ)

/-- Upper endpoint of the whole-window suffix state immediately after the
rounded `8^{-2}` boundary step. -/
noncomputable def inverseSquareSingleReverseAfter8CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (8934673 + 1) (-2 : ℤ)

/-- The named after-`8` candidate lies in the post-`8` whole-window target. -/
theorem inverseSquareSingleReverseAfter8Candidate_mem_after8Window :
    inverseSquareSingleReverseAfter8CandidateWindowLower ≤
        inverseSquareSingleReverseAfter8Candidate ∧
      inverseSquareSingleReverseAfter8Candidate ≤
        inverseSquareSingleReverseAfter8CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseAfter8CandidateWindowLower,
      inverseSquareSingleReverseAfter8CandidateWindowUpper,
      inverseSquareSingleReverseAfter8Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Exact addition by `8^{-2}` maps the before-`8` whole window into the exact
post-`8` enclosure. -/
theorem inverseSquareSingleReverseBefore8Window_add_8_term_mem_after8Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore8CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore8CandidateWindowUpper) :
    inverseSquareSingleReverseAfter8CandidateWindowLower ≤
        s + inverseSquareTerm 8 ∧
      s + inverseSquareTerm 8 ≤
        inverseSquareSingleReverseAfter8CandidateWindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter8CandidateWindowLower ≤
          inverseSquareSingleReverseBefore8CandidateWindowLower +
            inverseSquareTerm 8 := by
      norm_num [inverseSquareSingleReverseAfter8CandidateWindowLower,
        inverseSquareSingleReverseBefore8CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore8CandidateWindowLower +
            inverseSquareTerm 8 ≤
          s + inverseSquareTerm 8 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore8CandidateWindowUpper +
            inverseSquareTerm 8 ≤
          inverseSquareSingleReverseAfter8CandidateWindowUpper := by
      norm_num [inverseSquareSingleReverseBefore8CandidateWindowUpper,
        inverseSquareSingleReverseAfter8CandidateWindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 8 ≤
          inverseSquareSingleReverseBefore8CandidateWindowUpper +
            inverseSquareTerm 8 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `8^{-2}` maps every before-`8` whole-window start into
the post-`8` whole-window suffix state. -/
theorem inverseSquareSingleReverseBefore8Window_round_8_step_mem_after8Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore8CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore8CandidateWindowUpper) :
    inverseSquareSingleReverseAfter8CandidateWindowLower ≤
        inverseSquareSingleForwardStep s 8 ∧
      inverseSquareSingleForwardStep s 8 ≤
        inverseSquareSingleReverseAfter8CandidateWindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore8Window_add_8_term_mem_after8Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter8CandidateWindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8934673 - 2, (-2 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter8CandidateWindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8934673 + 1, (-2 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 8)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 8)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 8)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Post-`8` form of the remaining whole-window suffix certificate. -/
def inverseSquareSingleReverseAfter8WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter8CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter8CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 7 7 =
          inverseSquareSingleReversePrintedAccumulator

/-- The post-`8` whole-window suffix certificate implies the before-`8`
whole-window suffix certificate. -/
theorem inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_after8Window
    (hsuffix : inverseSquareSingleReverseAfter8WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore8WindowMapsToPrinted := by
  intro start hlo hhi
  have hfirstBounds :
      inverseSquareSingleReverseAfter8CandidateWindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 8 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 8 1 ≤
          inverseSquareSingleReverseAfter8CandidateWindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore8Window_round_8_step_mem_after8Window
        hlo hhi
  rw [show 8 = 1 + 7 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 8 - 1 = 7 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 8 1)
    hfirstBounds.1 hfirstBounds.2

/-- Lower endpoint for the whole-window state just before the `4^{-2}`
boundary step, after the `7^{-2}, 6^{-2}, 5^{-2}` band. -/
noncomputable def inverseSquareSingleReverseBefore4CandidateWindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (14852732 - 2) (-2 : ℤ)

/-- Upper endpoint for the whole-window state just before the `4^{-2}`
boundary step. -/
noncomputable def inverseSquareSingleReverseBefore4CandidateWindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    (14852732 + 1) (-2 : ℤ)

/-- The concrete before-`4` candidate lies in the before-`4`
whole-window target. -/
theorem inverseSquareSingleReverseBefore4Candidate_mem_before4Window :
    inverseSquareSingleReverseBefore4CandidateWindowLower ≤
        inverseSquareSingleReverseBefore4Candidate ∧
      inverseSquareSingleReverseBefore4Candidate ≤
        inverseSquareSingleReverseBefore4CandidateWindowUpper := by
  constructor <;>
    norm_num [inverseSquareSingleReverseBefore4CandidateWindowLower,
      inverseSquareSingleReverseBefore4CandidateWindowUpper,
      inverseSquareSingleReverseBefore4Candidate,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]

/-- Lower endpoint after the before-`4` whole-window state has absorbed
`4^{-2}`. -/
noncomputable def inverseSquareSingleReverseAfter4WindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    9523517 (-1 : ℤ)

/-- A conservative upper endpoint after the before-`4` whole-window state has
absorbed `4^{-2}`.  The endpoint is one ulp above the concrete candidate; this
keeps the first final step an ordinary interval-rounding proof. -/
noncomputable def inverseSquareSingleReverseAfter4WindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    9523519 (-1 : ℤ)

/-- Lower endpoint after the following `3^{-2}` addition in the final
whole-window suffix. -/
noncomputable def inverseSquareSingleReverseAfter3WindowLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    13251787 (-1 : ℤ)

/-- Upper endpoint after the following `3^{-2}` addition in the final
whole-window suffix. -/
noncomputable def inverseSquareSingleReverseAfter3WindowUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    13251789 (-1 : ℤ)

/-- Exact addition by `4^{-2}` maps the before-`4` whole window into the
post-`4` enclosure. -/
theorem inverseSquareSingleReverseBefore4Window_add_4_term_mem_after4Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore4CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore4CandidateWindowUpper) :
    inverseSquareSingleReverseAfter4WindowLower ≤
        s + inverseSquareTerm 4 ∧
      s + inverseSquareTerm 4 ≤
        inverseSquareSingleReverseAfter4WindowUpper := by
  constructor
  · have hwindow :
        inverseSquareSingleReverseAfter4WindowLower ≤
          inverseSquareSingleReverseBefore4CandidateWindowLower +
            inverseSquareTerm 4 := by
      norm_num [inverseSquareSingleReverseAfter4WindowLower,
        inverseSquareSingleReverseBefore4CandidateWindowLower,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        inverseSquareSingleReverseBefore4CandidateWindowLower +
            inverseSquareTerm 4 ≤
          s + inverseSquareTerm 4 := by
      linarith
    exact le_trans hwindow hstep
  · have hwindow :
        inverseSquareSingleReverseBefore4CandidateWindowUpper +
            inverseSquareTerm 4 ≤
          inverseSquareSingleReverseAfter4WindowUpper := by
      norm_num [inverseSquareSingleReverseBefore4CandidateWindowUpper,
        inverseSquareSingleReverseAfter4WindowUpper,
        inverseSquareTerm,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hstep :
        s + inverseSquareTerm 4 ≤
          inverseSquareSingleReverseBefore4CandidateWindowUpper +
            inverseSquareTerm 4 := by
      linarith
    exact le_trans hstep hwindow

/-- Rounded addition by `4^{-2}` maps every before-`4` whole-window start into
the post-`4` whole-window enclosure. -/
theorem inverseSquareSingleReverseBefore4Window_round_4_step_mem_after4Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseBefore4CandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseBefore4CandidateWindowUpper) :
    inverseSquareSingleReverseAfter4WindowLower ≤
        inverseSquareSingleForwardStep s 4 ∧
      inverseSquareSingleForwardStep s 4 ≤
        inverseSquareSingleReverseAfter4WindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexact :=
    inverseSquareSingleReverseBefore4Window_add_4_term_mem_after4Window
      hlo hhi
  have hlowerFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter4WindowLower := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 9523517, (-1 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hupperFinite :
      fmt.finiteSystem inverseSquareSingleReverseAfter4WindowUpper := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 9523519, (-1 : ℤ), ?_, ?_, rfl⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
  have hround :
      fmt.nearestRoundingToFinite
        (s + inverseSquareTerm 4)
        (fmt.finiteRoundToEven (s + inverseSquareTerm 4)) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite
      (s + inverseSquareTerm 4)
  have hbounds :=
    FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints
      hround hlowerFinite hupperFinite hexact.1 hexact.2
  simpa [inverseSquareSingleForwardStep, FloatingPointFormat.finiteRoundToEvenOp,
    BasicOp.exact, fmt] using hbounds

/-- Rounded addition by `3^{-2}` maps the post-`4` whole-window enclosure into
the post-`3` whole-window enclosure. -/
theorem inverseSquareSingleReverseAfter4Window_round_3_step_mem_after3Window
    {s : ℝ}
    (hlo : inverseSquareSingleReverseAfter4WindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseAfter4WindowUpper) :
    inverseSquareSingleReverseAfter3WindowLower ≤
        inverseSquareSingleForwardStep s 3 ∧
      inverseSquareSingleForwardStep s 3 ≤
        inverseSquareSingleReverseAfter3WindowUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let mL : ℕ := 9523517
  let mU : ℕ := 9523519
  let d : ℕ := 3728270
  let k : ℕ := 3
  let e : ℤ := -1
  have hkpos : 0 < k := by norm_num [k]
  have hdpos : 0 < d := by norm_num [d]
  have hleft : (2 * d - 1) * k ^ 2 < 2 ^ 26 := by
    norm_num [d, k]
  have hright : 2 ^ 26 < (2 * d + 1) * k ^ 2 := by
    norm_num [d, k]
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange, mL, d]
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange, mL, d]
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange, mU, d]
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange, mU, d]
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := s + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter4WindowLower +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter4WindowLower,
      mL, d, k, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 26)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter4WindowLower +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter4WindowUpper +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter4WindowUpper,
      mU, d, k, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 26)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter4WindowUpper +
          inverseSquareTerm k := by
    simp [x]
    linarith
  have htargetL_eq :
      targetL = inverseSquareSingleReverseAfter3WindowLower := by
    norm_num [targetL, inverseSquareSingleReverseAfter3WindowLower,
      mL, d, e, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have htargetU_eq :
      targetU = inverseSquareSingleReverseAfter3WindowUpper := by
    norm_num [targetU, inverseSquareSingleReverseAfter3WindowUpper,
      mU, d, e, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter4WindowLower +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter4WindowLower +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter4WindowLower +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter4WindowLower,
            mL, d, k, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 26)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter4WindowLower,
                mL, d, k, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        inverseSquareSingleReverseAfter3WindowLower ≤
          fmt.finiteRoundToEven x := by
      simpa [htargetL_eq] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter4WindowUpper +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter4WindowUpper +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter4WindowUpper +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter4WindowUpper,
            mU, d, k, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 26)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter4WindowUpper,
                mU, d, k, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          inverseSquareSingleReverseAfter3WindowUpper := by
      simpa [htargetU_eq] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      x, k, fmt] using hle'

/-- The whole post-`3` final window collapses to the after-`2` candidate under
the `2^{-2}` rounded addition. -/
theorem inverseSquareSingleReverseAfter3Window_round_2_step_eq_after2
    {s : ℝ}
    (hlo : inverseSquareSingleReverseAfter3WindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseAfter3WindowUpper) :
    inverseSquareSingleForwardStep s 2 =
      inverseSquareSingleReverseAfter2Candidate := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let pred : ℝ := fmt.normalizedValue false 10820197 (0 : ℤ)
  let target : ℝ := fmt.normalizedValue false 10820198 (0 : ℤ)
  let succ : ℝ := fmt.normalizedValue false 10820199 (0 : ℤ)
  let x : ℝ := s + inverseSquareTerm 2
  have hmpred : fmt.normalizedMantissa 10820197 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmtarget : fmt.normalizedMantissa 10820198 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmsucc : fmt.normalizedMantissa 10820199 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hexp : fmt.exponentInRange (0 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hpredSystem : fmt.normalizedSystem pred :=
    ⟨false, 10820197, (0 : ℤ), hmpred, hexp, rfl⟩
  have htargetSystem : fmt.normalizedSystem target :=
    ⟨false, 10820198, (0 : ℤ), hmtarget, hexp, rfl⟩
  have hsuccSystem : fmt.normalizedSystem succ :=
    ⟨false, 10820199, (0 : ℤ), hmsucc, hexp, rfl⟩
  have hadjLeft : fmt.realOrderAdjacentNormalized pred target := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, 10820197, (0 : ℤ), hmpred, hmtarget,
      Or.inl ⟨rfl, rfl⟩⟩
  have hadjRight : fmt.realOrderAdjacentNormalized target succ := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, 10820198, (0 : ℤ), hmtarget, hmsucc,
      Or.inl ⟨rfl, rfl⟩⟩
  have hpred_pos : 0 < pred := by
    simpa [pred, fmt] using
      fmt.normalizedValue_false_pos (m := 10820197) (e := (0 : ℤ)) hmpred
  have hsucc_pos : 0 < succ := by
    simpa [succ, fmt] using
      fmt.normalizedValue_false_pos (m := 10820199) (e := (0 : ℤ)) hmsucc
  have hpred_lt_x : pred < x := by
    have hbase :
        pred <
          inverseSquareSingleReverseAfter3WindowLower +
            inverseSquareTerm 2 := by
      norm_num [pred, inverseSquareSingleReverseAfter3WindowLower,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hle :
        inverseSquareSingleReverseAfter3WindowLower +
            inverseSquareTerm 2 ≤ x := by
      simp [x]
      linarith
    exact lt_of_lt_of_le hbase hle
  have hx_lt_succ : x < succ := by
    have hbase :
        inverseSquareSingleReverseAfter3WindowUpper +
            inverseSquareTerm 2 < succ := by
      norm_num [succ, inverseSquareSingleReverseAfter3WindowUpper,
        inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hle :
        x ≤ inverseSquareSingleReverseAfter3WindowUpper +
            inverseSquareTerm 2 := by
      simp [x]
      linarith
    exact lt_of_le_of_lt hle hbase
  have hxpos : 0 < x := lt_trans hpred_pos hpred_lt_x
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg (le_of_lt hxpos)]
    constructor
    · have hpred_min : fmt.minNormalMagnitude ≤ pred := by
        simpa [FloatingPointFormat.minNormalMagnitude, abs_of_pos hpred_pos] using
          fmt.normalizedSystem_abs_lower_bound hpredSystem
      exact le_trans hpred_min (le_of_lt hpred_lt_x)
    · have hsucc_max : succ ≤ fmt.maxFiniteMagnitude := by
        simpa [FloatingPointFormat.maxFiniteMagnitude, abs_of_pos hsucc_pos] using
          fmt.normalizedSystem_abs_le_maxFinite_bound hsuccSystem
      exact le_trans (le_of_lt hx_lt_succ) hsucc_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have htarget_eq :
      target = inverseSquareSingleReverseAfter2Candidate := by
    norm_num [target, inverseSquareSingleReverseAfter2Candidate,
      fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  by_cases hleftSide : x ≤ target
  · have hbetween : pred ≤ x ∧ x ≤ target :=
      ⟨le_of_lt hpred_lt_x, hleftSide⟩
    have hleftRepr :
        ∃ negative eLeft,
          fmt.normalizedMantissa 10820197 ∧
            pred = fmt.normalizedValue negative 10820197 eLeft :=
      ⟨false, (0 : ℤ), hmpred, rfl⟩
    have hnearest :
        fmt.finiteRoundToEven x =
          FloatingPointFormat.nearestAdjacentRoundToEven x pred target 10820197 :=
      fmt.sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between
        hpolicy hadjLeft hleftRepr hbetween
    have hmid_le_x : (pred + target) / 2 ≤ x := by
      have hmid :
          (pred + target) / 2 =
            inverseSquareSingleReverseAfter3WindowLower +
              inverseSquareTerm 2 := by
        norm_num [pred, target, inverseSquareSingleReverseAfter3WindowLower,
          inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      rw [hmid]
      simp [x]
      linarith
    have hnotLeft : ¬ |x - pred| < |x - target| := by
      have hxpred_nonneg : 0 ≤ x - pred := by linarith
      have hxt_nonpos : x - target ≤ 0 := by linarith
      rw [abs_of_nonneg hxpred_nonneg, abs_of_nonpos hxt_nonpos]
      linarith
    have hselector :
        FloatingPointFormat.nearestAdjacentRoundToEven x pred target 10820197 =
          target := by
      unfold FloatingPointFormat.nearestAdjacentRoundToEven
      by_cases hright : |x - target| < |x - pred|
      · simp [hnotLeft, hright]
      · have hodd : ¬ FloatingPointFormat.evenMantissa 10820197 := by
          norm_num [FloatingPointFormat.evenMantissa]
        simp [hnotLeft, hright, hodd]
    have hround : fmt.finiteRoundToEven x = target := by
      simpa [hselector] using hnearest
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      x, target, htarget_eq, fmt] using hround
  · have htarget_lt_x : target < x := lt_of_not_ge hleftSide
    have hbetween : target ≤ x ∧ x ≤ succ :=
      ⟨le_of_lt htarget_lt_x, le_of_lt hx_lt_succ⟩
    have hleftRepr :
        ∃ negative eLeft,
          fmt.normalizedMantissa 10820198 ∧
            target = fmt.normalizedValue negative 10820198 eLeft :=
      ⟨false, (0 : ℤ), hmtarget, rfl⟩
    have hnearest :
        fmt.finiteRoundToEven x =
          FloatingPointFormat.nearestAdjacentRoundToEven x target succ 10820198 :=
      fmt.sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between
        hpolicy hadjRight hleftRepr hbetween
    have hx_le_mid : x ≤ (target + succ) / 2 := by
      have hmid :
          inverseSquareSingleReverseAfter3WindowUpper +
              inverseSquareTerm 2 =
            (target + succ) / 2 := by
        norm_num [target, succ, inverseSquareSingleReverseAfter3WindowUpper,
          inverseSquareTerm, fmt, FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      rw [← hmid]
      simp [x]
      linarith
    have hnotRight : ¬ |x - succ| < |x - target| := by
      have hxt_nonneg : 0 ≤ x - target := by linarith
      have hxs_nonpos : x - succ ≤ 0 := by linarith
      rw [abs_of_nonpos hxs_nonpos, abs_of_nonneg hxt_nonneg]
      linarith
    have hselector :
        FloatingPointFormat.nearestAdjacentRoundToEven x target succ 10820198 =
          target := by
      unfold FloatingPointFormat.nearestAdjacentRoundToEven
      by_cases hleft : |x - target| < |x - succ|
      · simp [hleft]
      · have heven : FloatingPointFormat.evenMantissa 10820198 := by
          norm_num [FloatingPointFormat.evenMantissa]
        simp [hleft, hnotRight, heven]
    have hround : fmt.finiteRoundToEven x = target := by
      simpa [hselector] using hnearest
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      x, target, htarget_eq, fmt] using hround

/-- Lower endpoint after `n` additions inside the `7^{-2}, 6^{-2}, 5^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter8BandWindowLower
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8934673 - 2) +
      inverseSquareSingleReverseScaledMantissaPrefix 27 7 n) (-2 : ℤ)

/-- Upper endpoint after `n` additions inside the `7^{-2}, 6^{-2}, 5^{-2}`
whole-window band. -/
noncomputable def inverseSquareSingleReverseAfter8BandWindowUpper
    (n : ℕ) : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false
    ((8934673 + 1) +
      inverseSquareSingleReverseScaledMantissaPrefix 27 7 n) (-2 : ℤ)

theorem inverseSquareSingleReverseAfter8BandWindowLower_zero :
    inverseSquareSingleReverseAfter8BandWindowLower 0 =
      inverseSquareSingleReverseAfter8CandidateWindowLower := by
  norm_num [inverseSquareSingleReverseAfter8BandWindowLower,
    inverseSquareSingleReverseAfter8CandidateWindowLower,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter8BandWindowUpper_zero :
    inverseSquareSingleReverseAfter8BandWindowUpper 0 =
      inverseSquareSingleReverseAfter8CandidateWindowUpper := by
  norm_num [inverseSquareSingleReverseAfter8BandWindowUpper,
    inverseSquareSingleReverseAfter8CandidateWindowUpper,
    inverseSquareSingleReverseScaledMantissaPrefix]

theorem inverseSquareSingleReverseAfter8BandWindowLower_final :
    inverseSquareSingleReverseAfter8BandWindowLower 3 =
      inverseSquareSingleReverseBefore4CandidateWindowLower := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8934673 - 2) +
          inverseSquareSingleReverseScaledMantissaPrefix 27 7 3)
        (-2 : ℤ) =
      inverseSquareSingleReverseBefore4CandidateWindowLower
  rw [inverseSquareSingleReverseAfter8Prefix_7_to_5_eq]
  norm_num [inverseSquareSingleReverseBefore4CandidateWindowLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

theorem inverseSquareSingleReverseAfter8BandWindowUpper_final :
    inverseSquareSingleReverseAfter8BandWindowUpper 3 =
      inverseSquareSingleReverseBefore4CandidateWindowUpper := by
  change
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        ((8934673 + 1) +
          inverseSquareSingleReverseScaledMantissaPrefix 27 7 3)
        (-2 : ℤ) =
      inverseSquareSingleReverseBefore4CandidateWindowUpper
  rw [inverseSquareSingleReverseAfter8Prefix_7_to_5_eq]
  norm_num [inverseSquareSingleReverseBefore4CandidateWindowUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR,
    zpow_neg]

/-- Endpoint-safety certificate for the tenth whole-window reverse suffix
band. It checks that the `7^{-2}, 6^{-2}, 5^{-2}` increments remain normal for
both endpoints of the post-`8` window. -/
def inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificateBool :
    Bool :=
  (List.range 3).all (fun n =>
    let p := inverseSquareSingleReverseScaledMantissaPrefix 27 7 n
    let k := 7 - n
    let d := inverseSquareSingleScaledMantissaIncrement 27 k
    decide (0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 27 ∧
      2 ^ 27 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8934673 - 2 + p) + d - 1 ∧
      (8934673 + 1 + p) + d + 1 < 16777216))

/-- Kernel-checked endpoint-safety certificate for the tenth whole-window
reverse suffix band. -/
theorem inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificateBool_eq_true :
    inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificateBool =
      true := by
  set_option maxRecDepth 10000 in
  decide

/-- Pointwise endpoint-safety extraction for the tenth whole-window reverse
suffix band. -/
theorem inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificate
    {n : ℕ} (hn : n < 3) :
    let p := inverseSquareSingleReverseScaledMantissaPrefix 27 7 n
    let k := 7 - n
    let d := inverseSquareSingleScaledMantissaIncrement 27 k
    0 < k ∧ 0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 27 ∧
      2 ^ 27 < (2 * d + 1) * k ^ 2 ∧
      8388608 ≤ (8934673 - 2 + p) + d - 1 ∧
      (8934673 + 1 + p) + d + 1 < 16777216 := by
  have hall :
      ∀ x < 3,
        let p := inverseSquareSingleReverseScaledMantissaPrefix 27 7 x
        let k := 7 - x
        let d := inverseSquareSingleScaledMantissaIncrement 27 k
        0 < k ∧ 0 < d ∧
          (2 * d - 1) * k ^ 2 < 2 ^ 27 ∧
          2 ^ 27 < (2 * d + 1) * k ^ 2 ∧
          8388608 ≤ (8934673 - 2 + p) + d - 1 ∧
          (8934673 + 1 + p) + d + 1 < 16777216 := by
    simpa [inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificateBool] using
      inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificateBool_eq_true
  simpa using hall n hn

/-- One arbitrary-start step of the tenth whole-window reverse suffix band. -/
theorem inverseSquareSingleReverseAfter8BandWindow_round_step_mem
    {n : ℕ} (hn : n < 3) {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter8BandWindowLower n ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter8BandWindowUpper n) :
    inverseSquareSingleReverseAfter8BandWindowLower (n + 1) ≤
        inverseSquareSingleForwardStep start (7 - n) ∧
      inverseSquareSingleForwardStep start (7 - n) ≤
        inverseSquareSingleReverseAfter8BandWindowUpper (n + 1) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let p := inverseSquareSingleReverseScaledMantissaPrefix 27 7 n
  let k := 7 - n
  let d := inverseSquareSingleScaledMantissaIncrement 27 k
  let mL := (8934673 - 2) + p
  let mU := (8934673 + 1) + p
  let e : ℤ := -2
  have hcert :=
    inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificate hn
  rcases hcert with ⟨hkpos, hdpos, hleft, hright, hmin, hmax⟩
  have hmin' : 8388608 ≤ mL + d - 1 := by
    simpa [mL, p, k, d] using hmin
  have hmax' : mU + d + 1 < 16777216 := by
    simpa [mU, p, k, d] using hmax
  have hexp : fmt.exponentInRange e := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange, e]
  have hmpredL : fmt.normalizedMantissa (mL + d - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetL : fmt.normalizedMantissa (mL + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmtargetU : fmt.normalizedMantissa (mU + d) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  have hmsuccU : fmt.normalizedMantissa (mU + d + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange] at hmin' hmax' ⊢
    omega
  let predL : ℝ := fmt.normalizedValue false (mL + d - 1) e
  let targetL : ℝ := fmt.normalizedValue false (mL + d) e
  let targetU : ℝ := fmt.normalizedValue false (mU + d) e
  let succU : ℝ := fmt.normalizedValue false (mU + d + 1) e
  let x : ℝ := start + inverseSquareTerm k
  have hround :
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hpredLSystem : fmt.normalizedSystem predL :=
    ⟨false, mL + d - 1, e, hmpredL, hexp, rfl⟩
  have htargetLSystem : fmt.normalizedSystem targetL :=
    ⟨false, mL + d, e, hmtargetL, hexp, rfl⟩
  have htargetUSystem : fmt.normalizedSystem targetU :=
    ⟨false, mU + d, e, hmtargetU, hexp, rfl⟩
  have hpredL_pos : 0 < predL := by
    simpa [predL, e, fmt] using
      fmt.normalizedValue_false_pos (m := mL + d - 1) (e := e) hmpredL
  have htargetU_pos : 0 < targetU := by
    simpa [targetU, e, fmt] using
      fmt.normalizedValue_false_pos (m := mU + d) (e := e) hmtargetU
  have hadjL : fmt.realOrderAdjacentNormalized predL targetL := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    refine ⟨false, mL + d - 1, e, hmpredL, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ mL + d)] using hmtargetL
    · simp [targetL, e, Nat.sub_add_cancel (by omega : 1 ≤ mL + d)]
  have hadjU : fmt.realOrderAdjacentNormalized targetU succU := by
    refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
    exact ⟨false, mU + d, e, hmtargetU, hmsuccU, Or.inl ⟨rfl, rfl⟩⟩
  have hpredL_lt_base :
      predL <
        inverseSquareSingleReverseAfter8BandWindowLower n +
          inverseSquareTerm k := by
    simpa [predL, inverseSquareSingleReverseAfter8BandWindowLower,
      mL, p, k, d, e, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound_at_scale
        (m := mL) (d := d) (k := k) (q := 27)
        hdpos hkpos hleft
  have hbaseL_le_x :
      inverseSquareSingleReverseAfter8BandWindowLower n +
          inverseSquareTerm k ≤ x := by
    simp [x]
    linarith
  have hx_lt_succU_base :
      inverseSquareSingleReverseAfter8BandWindowUpper n +
          inverseSquareTerm k < succU := by
    simpa [succU, inverseSquareSingleReverseAfter8BandWindowUpper,
      mU, p, k, d, e, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound_at_scale
        (m := mU) (d := d) (k := k) (q := 27)
        hkpos hright
  have hx_le_baseU :
      x ≤
        inverseSquareSingleReverseAfter8BandWindowUpper n +
          inverseSquareTerm k := by
    simp [x]
    linarith
  constructor
  · have hxpred : predL < x :=
      lt_of_lt_of_le hpredL_lt_base hbaseL_le_x
    have hcase :
        targetL ≤ x ∨ |x - targetL| < |x - predL| := by
      by_cases htarget : targetL ≤ x
      · exact Or.inl htarget
      · have hxlt : x < targetL := lt_of_not_ge htarget
        have hbase_lt_target :
            inverseSquareSingleReverseAfter8BandWindowLower n +
                inverseSquareTerm k < targetL :=
          lt_of_le_of_lt hbaseL_le_x hxlt
        have hbase_closer :
            |(inverseSquareSingleReverseAfter8BandWindowLower n +
                  inverseSquareTerm k) - targetL| <
              |(inverseSquareSingleReverseAfter8BandWindowLower n +
                  inverseSquareTerm k) - predL| := by
          simpa [targetL, predL, inverseSquareSingleReverseAfter8BandWindowLower,
            mL, p, k, d, e, fmt] using
            inverseSquareSingle_right_closer_to_target_of_scaled_left_bound_at_scale
              (m := mL) (d := d) (k := k) (q := 27)
              hdpos hkpos hleft
              (by simpa [targetL, inverseSquareSingleReverseAfter8BandWindowLower,
                mL, p, k, d, e, fmt] using hbase_lt_target)
        exact Or.inr
          (abs_sub_right_lt_abs_sub_left_of_le_of_right_closer
            hpredL_lt_base hbaseL_le_x hxlt hbase_closer)
    have hge :=
      fmt.nearestRoundingToFinite_ge_of_adjacent_midpoint
        hround hpredLSystem htargetLSystem hadjL hpredL_pos hxpred hcase
    have hge' :
        fmt.normalizedValue false
            (8934671 +
              (inverseSquareSingleReverseScaledMantissaPrefix 27 7 n +
                inverseSquareSingleScaledMantissaIncrement 27 (7 - n)))
            (-2 : ℤ) ≤
          fmt.finiteRoundToEven x := by
      have hnat :
          mL + d =
            8934671 +
              (inverseSquareSingleReverseScaledMantissaPrefix 27 7 n +
                inverseSquareSingleScaledMantissaIncrement 27 (7 - n)) := by
        simp [mL, p, d, k]
        omega
      simpa [targetL, e, fmt, hnat] using hge
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter8BandWindowLower,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hge'
  · have hxsucc : x < succU :=
      lt_of_le_of_lt hx_le_baseU hx_lt_succU_base
    have hcase :
        x ≤ targetU ∨ |x - targetU| < |x - succU| := by
      by_cases htarget : x ≤ targetU
      · exact Or.inl htarget
      · have htarget_lt_x : targetU < x := lt_of_not_ge htarget
        have htarget_lt_base :
            targetU <
              inverseSquareSingleReverseAfter8BandWindowUpper n +
                inverseSquareTerm k :=
          lt_of_lt_of_le htarget_lt_x hx_le_baseU
        have hbase_closer :
            |(inverseSquareSingleReverseAfter8BandWindowUpper n +
                  inverseSquareTerm k) - targetU| <
              |(inverseSquareSingleReverseAfter8BandWindowUpper n +
                  inverseSquareTerm k) - succU| := by
          simpa [targetU, succU, inverseSquareSingleReverseAfter8BandWindowUpper,
            mU, p, k, d, e, fmt] using
            inverseSquareSingle_left_closer_to_target_of_scaled_right_bound_at_scale
              (m := mU) (d := d) (k := k) (q := 27)
              hkpos hright
              (by simpa [targetU, inverseSquareSingleReverseAfter8BandWindowUpper,
                mU, p, k, d, e, fmt] using htarget_lt_base)
        exact Or.inr
          (abs_sub_left_lt_abs_sub_right_of_le_of_left_closer
            htarget_lt_x hx_le_baseU hx_lt_succU_base hbase_closer)
    have hle :=
      fmt.nearestRoundingToFinite_le_of_adjacent_midpoint
        hround htargetUSystem hadjU htargetU_pos hxsucc hcase
    have hle' :
        fmt.finiteRoundToEven x ≤
          fmt.normalizedValue false
            (8934674 +
              (inverseSquareSingleReverseScaledMantissaPrefix 27 7 n +
                inverseSquareSingleScaledMantissaIncrement 27 (7 - n)))
            (-2 : ℤ) := by
      have hnat :
          mU + d =
            8934674 +
              (inverseSquareSingleReverseScaledMantissaPrefix 27 7 n +
                inverseSquareSingleScaledMantissaIncrement 27 (7 - n)) := by
        simp [mU, p, d, k]
        omega
      simpa [targetU, e, fmt, hnat] using hle
    simpa [inverseSquareSingleForwardStep,
      FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSingleReverseAfter8BandWindowUpper,
      inverseSquareSingleReverseScaledMantissaPrefix_succ,
      x, k, fmt] using hle'

/-- Prefix induction for the whole-window `7^{-2}, 6^{-2}, 5^{-2}` band. -/
theorem inverseSquareSingleReverseAfter8BandWindow_prefix_mem
    {start : ℝ}
    (hlo : inverseSquareSingleReverseAfter8CandidateWindowLower ≤ start)
    (hhi : start ≤ inverseSquareSingleReverseAfter8CandidateWindowUpper)
    (n : ℕ) (hn : n ≤ 3) :
    inverseSquareSingleReverseAfter8BandWindowLower n ≤
        inverseSquareSingleReverseAccumulatorFrom start 7 n ∧
      inverseSquareSingleReverseAccumulatorFrom start 7 n ≤
        inverseSquareSingleReverseAfter8BandWindowUpper n := by
  induction n with
  | zero =>
      constructor
      · simpa [inverseSquareSingleReverseAfter8BandWindowLower_zero] using hlo
      · simpa [inverseSquareSingleReverseAfter8BandWindowUpper_zero] using hhi
  | succ n ih =>
      have hnle : n ≤ 3 := by omega
      have hnlt : n < 3 := by omega
      have ihb := ih hnle
      simpa [inverseSquareSingleReverseAccumulatorFrom] using
        inverseSquareSingleReverseAfter8BandWindow_round_step_mem
          (n := n) hnlt ihb.1 ihb.2

/-- Whole-window band certificate for the `7^{-2}, 6^{-2}, 5^{-2}` reverse
suffix chunk: every post-`8` window start lands in the before-`4`
window after the three same-exponent additions. -/
def inverseSquareSingleReverseAfter8Band7ToBefore4Window : Prop :=
  ∀ start,
    inverseSquareSingleReverseAfter8CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseAfter8CandidateWindowUpper →
        inverseSquareSingleReverseBefore4CandidateWindowLower ≤
            inverseSquareSingleReverseAccumulatorFrom start 7 3 ∧
          inverseSquareSingleReverseAccumulatorFrom start 7 3 ≤
            inverseSquareSingleReverseBefore4CandidateWindowUpper

/-- Closed whole-window band certificate for the `7^{-2}, 6^{-2}, 5^{-2}`
reverse suffix chunk. -/
theorem inverseSquareSingleReverseAfter8Band7ToBefore4Window_closed :
    inverseSquareSingleReverseAfter8Band7ToBefore4Window := by
  intro start hlo hhi
  have hprefix :=
    inverseSquareSingleReverseAfter8BandWindow_prefix_mem
      (start := start) hlo hhi 3 (by norm_num)
  rw [← inverseSquareSingleReverseAfter8BandWindowLower_final,
    ← inverseSquareSingleReverseAfter8BandWindowUpper_final]
  exact hprefix

/-- The concrete after-`8` candidate band lands in the before-`4` window. -/
theorem inverseSquareSingleReverseAfter8Candidate_band7_to_before4_mem_before4Window :
    inverseSquareSingleReverseBefore4CandidateWindowLower ≤
        inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter8Candidate 7 3 ∧
      inverseSquareSingleReverseAccumulatorFrom
          inverseSquareSingleReverseAfter8Candidate 7 3 ≤
        inverseSquareSingleReverseBefore4CandidateWindowUpper := by
  rw [inverseSquareSingleReverseAfter8Accumulator_7_to_before4]
  exact inverseSquareSingleReverseBefore4Candidate_mem_before4Window

/-- Remaining suffix certificate after the `7^{-2}, 6^{-2}, 5^{-2}` band has
placed the state in the before-`4` whole-window target. -/
def inverseSquareSingleReverseBefore4WindowMapsToPrinted : Prop :=
  ∀ start,
    inverseSquareSingleReverseBefore4CandidateWindowLower ≤ start →
      start ≤ inverseSquareSingleReverseBefore4CandidateWindowUpper →
        inverseSquareSingleReverseAccumulatorFrom start 4 4 =
          inverseSquareSingleReversePrintedAccumulator

/-- Closed whole-window certificate for the final four low-index reverse
additions. -/
theorem inverseSquareSingleReverseBefore4WindowMapsToPrinted_closed :
    inverseSquareSingleReverseBefore4WindowMapsToPrinted := by
  intro start hlo hhi
  have h4Bounds :
      inverseSquareSingleReverseAfter4WindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom start 4 1 ∧
        inverseSquareSingleReverseAccumulatorFrom start 4 1 ≤
          inverseSquareSingleReverseAfter4WindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseBefore4Window_round_4_step_mem_after4Window
        hlo hhi
  have h3Bounds :
      inverseSquareSingleReverseAfter3WindowLower ≤
          inverseSquareSingleReverseAccumulatorFrom
            (inverseSquareSingleReverseAccumulatorFrom start 4 1) 3 1 ∧
        inverseSquareSingleReverseAccumulatorFrom
            (inverseSquareSingleReverseAccumulatorFrom start 4 1) 3 1 ≤
          inverseSquareSingleReverseAfter3WindowUpper := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseAfter4Window_round_3_step_mem_after3Window
        h4Bounds.1 h4Bounds.2
  have h2 :
      inverseSquareSingleReverseAccumulatorFrom
          (inverseSquareSingleReverseAccumulatorFrom
            (inverseSquareSingleReverseAccumulatorFrom start 4 1) 3 1) 2 1 =
        inverseSquareSingleReverseAfter2Candidate := by
    simpa [inverseSquareSingleReverseAccumulatorFrom] using
      inverseSquareSingleReverseAfter3Window_round_2_step_eq_after2
        h3Bounds.1 h3Bounds.2
  rw [show 4 = 1 + 3 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 4 - 1 = 3 by norm_num]
  rw [show 3 = 1 + 2 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 3 - 1 = 2 by norm_num]
  rw [show 2 = 1 + 1 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [h2]
  rw [show 2 - 1 = 1 by norm_num]
  change
    inverseSquareSingleReverseAccumulatorFrom
        inverseSquareSingleReverseAfter2Candidate 1 1 =
      inverseSquareSingleReversePrintedAccumulator
  change
    inverseSquareSingleForwardStep
        inverseSquareSingleReverseAfter2Candidate (1 - 0) =
      inverseSquareSingleReversePrintedAccumulator
  simpa using inverseSquareSingleReverseAfter2_add_1_term_rounds_to_printed

/-- A whole-window certificate for the `7^{-2}, 6^{-2}, 5^{-2}` band plus a
before-`4` suffix certificate imply the post-`8` suffix certificate. -/
theorem inverseSquareSingleReverseAfter8WindowMapsToPrinted_of_band7_to_before4Window
    (hband : inverseSquareSingleReverseAfter8Band7ToBefore4Window)
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter8WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 7 = 3 + 4 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 7 - 3 = 4 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 7 3)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`4` whole-window suffix map is supplied, the entire
post-`8` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter8WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter8WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter8WindowMapsToPrinted_of_band7_to_before4Window
    inverseSquareSingleReverseAfter8Band7ToBefore4Window_closed
    hsuffix

/-- Once the before-`4` whole-window suffix map is supplied, the before-`8`
whole-window suffix map is closed by the rounded boundary step and certified
same-exponent band. -/
theorem inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore8WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_after8Window
    (inverseSquareSingleReverseAfter8WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- Once the before-`4` whole-window suffix map is supplied, the before-`16`
whole-window suffix map is closed through the before-`8` boundary and band. -/
theorem inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore16WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window
    (inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- Once the before-`4` whole-window suffix map is supplied, the before-`32`
whole-window suffix map is closed through the before-`8` boundary and band. -/
theorem inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore32WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before8Window
    (inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- Once the before-`4` whole-window suffix map is supplied, the before-`64`
whole-window suffix map is closed through the before-`8` boundary and band. -/
theorem inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore64WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before8Window
    (inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- Once the before-`4` whole-window suffix map is supplied, the before-`128`
whole-window suffix map is closed through the before-`8` boundary and band. -/
theorem inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore128WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before8Window
    (inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- Once the before-`4` whole-window suffix map is supplied, the before-`256`
whole-window suffix map is closed through the before-`8` boundary and band. -/
theorem inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore256WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before8Window
    (inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- Once the before-`4` whole-window suffix map is supplied, the before-`512`
whole-window suffix map is closed through the before-`8` boundary and band. -/
theorem inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore512WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before8Window
    (inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- Once the before-`4` whole-window suffix map is supplied, the before-`1024`
whole-window suffix map is closed through the before-`8` boundary and band. -/
theorem inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore1024WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before8Window
    (inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- Once the before-`4` whole-window suffix map is supplied, the before-`2048`
whole-window suffix map is closed through the before-`8` boundary and band. -/
theorem inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseBefore2048WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before8Window
    (inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- A whole-window certificate for the `4094^{-2}, ..., 2049^{-2}` band plus a
before-`2048` suffix certificate imply the post-`4095` suffix certificate. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_band4094_to_before2048Window
    (hband : inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window)
    (hsuffix : inverseSquareSingleReverseBefore2048WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted := by
  intro start hlo hhi
  have hbandBounds := hband start hlo hhi
  rw [show 4094 = 2046 + 2048 by norm_num]
  rw [inverseSquareSingleReverseAccumulatorFrom_add]
  rw [show 4094 - 2046 = 2048 by norm_num]
  exact hsuffix
    (inverseSquareSingleReverseAccumulatorFrom start 4094 2046)
    hbandBounds.1 hbandBounds.2

/-- Once the before-`2048` whole-window suffix map is supplied, the entire
post-`4095` suffix map is closed by the certified same-exponent band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (hsuffix : inverseSquareSingleReverseBefore2048WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_band4094_to_before2048Window
    inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window_closed
    hsuffix

/-- Once the before-`1024` whole-window suffix map is supplied, the post-`4095`
suffix map is closed through the certified before-`2048` boundary and
post-`2048` same-exponent band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before1024Window
    (hsuffix : inverseSquareSingleReverseBefore1024WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before1024Window
      hsuffix)

/-- Once the before-`512` whole-window suffix map is supplied, the post-`4095`
suffix map is closed through the certified before-`1024` boundary and band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before512Window
    (hsuffix : inverseSquareSingleReverseBefore512WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before512Window
      hsuffix)

/-- Once the before-`256` whole-window suffix map is supplied, the post-`4095`
suffix map is closed through the certified before-`512` boundary and band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before256Window
    (hsuffix : inverseSquareSingleReverseBefore256WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before256Window
      hsuffix)

/-- Once the before-`128` whole-window suffix map is supplied, the post-`4095`
suffix map is closed through the certified before-`256` boundary and band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before128Window
    (hsuffix : inverseSquareSingleReverseBefore128WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before128Window
      hsuffix)

/-- Once the before-`64` whole-window suffix map is supplied, the post-`4095`
suffix map is closed through the certified before-`128` boundary and band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before64Window
    (hsuffix : inverseSquareSingleReverseBefore64WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before64Window
      hsuffix)

/-- Once the before-`32` whole-window suffix map is supplied, the post-`4095`
suffix map is closed through the certified before-`64` boundary and band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before32Window
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before32Window
      hsuffix)

/-- Once the before-`16` whole-window suffix map is supplied, the post-`4095`
suffix map is closed through the certified before-`32` boundary and band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before16Window
      hsuffix)

/-- Once the before-`8` whole-window suffix map is supplied, the post-`4095`
suffix map is closed through the certified before-`16` boundary and band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before8Window
      hsuffix)

/-- Once the before-`4` whole-window suffix map is supplied, the post-`4095`
suffix map is closed through the certified before-`8` boundary and band. -/
theorem inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseAfter4095WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window
    (inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before4Window
      hsuffix)

/-- Archived optional repository-model certificate-composition theorem for the
reverse-order run.  This shrinks the suffix obligation from the whole refined
suffix-start window to the concrete 1024-ulp high-prefix candidate window; the
historical Fortran output remains an empirical ledger row. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidateWindow_certificates
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow)
    (hsuffix : inverseSquareSingleReverseCandidateWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator := by
  rw [inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096]
  exact hsuffix
    inverseSquareSingleReverseTenPowNineHighPrefixState
    hprefix.1 hprefix.2

/-- Exact-prefix variant of the candidate-window route. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact_candidateWindow
    (hprefix :
      inverseSquareSingleReverseTenPowNineHighPrefixState =
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096))
    (hsuffix : inverseSquareSingleReverseCandidateWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidateWindow_certificates
    (inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_eq_exact
      hprefix)
    hsuffix

/-- Candidate-equality variant of the candidate-window route. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_candidateWindow
    (hprefix : inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate)
    (hsuffix : inverseSquareSingleReverseCandidateWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidateWindow_certificates
    (inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_eq_candidate
      hprefix)
    hsuffix

/-- Candidate-window suffix reduction all the way to the before-`1024`
whole-window suffix map. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before1024Window
    (hsuffix : inverseSquareSingleReverseBefore1024WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
      (inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before1024Window
        hsuffix))

/-- Candidate-window suffix reduction all the way to the before-`512`
whole-window suffix map. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before512Window
    (hsuffix : inverseSquareSingleReverseBefore512WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
      (inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before512Window
        hsuffix))

/-- Candidate-window suffix reduction all the way to the before-`256`
whole-window suffix map. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before256Window
    (hsuffix : inverseSquareSingleReverseBefore256WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
      (inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before256Window
        hsuffix))

/-- Candidate-window suffix reduction all the way to the before-`128`
whole-window suffix map. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before128Window
    (hsuffix : inverseSquareSingleReverseBefore128WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
      (inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before128Window
        hsuffix))

/-- Candidate-window suffix reduction all the way to the before-`64`
whole-window suffix map. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before64Window
    (hsuffix : inverseSquareSingleReverseBefore64WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
      (inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before64Window
        hsuffix))

/-- Candidate-window suffix reduction all the way to the before-`32`
whole-window suffix map. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before32Window
    (hsuffix : inverseSquareSingleReverseBefore32WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
      (inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before32Window
        hsuffix))

/-- Candidate-window suffix reduction all the way to the before-`16`
whole-window suffix map. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before16Window
    (hsuffix : inverseSquareSingleReverseBefore16WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
      (inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before16Window
        hsuffix))

/-- Candidate-window suffix reduction all the way to the before-`8`
whole-window suffix map. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before8Window
    (hsuffix : inverseSquareSingleReverseBefore8WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
      (inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before8Window
        hsuffix))

/-- Candidate-window suffix reduction all the way to the before-`4`
whole-window suffix map. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before4Window
    (hsuffix : inverseSquareSingleReverseBefore4WindowMapsToPrinted) :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window
    (inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window
      (inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before4Window
        hsuffix))

/-- The post-`8` whole-window suffix map is closed by the final before-`4`
whole-window certificate. -/
theorem inverseSquareSingleReverseAfter8WindowMapsToPrinted_closed :
    inverseSquareSingleReverseAfter8WindowMapsToPrinted :=
  inverseSquareSingleReverseAfter8WindowMapsToPrinted_of_before4Window
    inverseSquareSingleReverseBefore4WindowMapsToPrinted_closed

/-- The before-`8` whole-window suffix map is closed by the final before-`4`
whole-window certificate. -/
theorem inverseSquareSingleReverseBefore8WindowMapsToPrinted_closed :
    inverseSquareSingleReverseBefore8WindowMapsToPrinted :=
  inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window
    inverseSquareSingleReverseBefore4WindowMapsToPrinted_closed

/-- Closed candidate-window suffix map for the archived optional repository
model, not an active historical-output target. -/
theorem inverseSquareSingleReverseCandidateWindowMapsToPrinted_closed :
    inverseSquareSingleReverseCandidateWindowMapsToPrinted :=
  inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before4Window
    inverseSquareSingleReverseBefore4WindowMapsToPrinted_closed

/-- If the rounded high prefix is in the concrete candidate window, the archived
optional repository-model suffix route is now closed. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed
    (hwin : inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidateWindow_certificates
    hwin inverseSquareSingleReverseCandidateWindowMapsToPrinted_closed

/-- Archived optional conditional route through the before-`8192` finite-cell
bridge: once the rounded earlier block is proved to satisfy its strict
start-window guard, the closed final-binade map and closed low-index suffix map
yield the repository-model accumulator with Higham's displayed reverse decimal. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_before8192StartWindowCellGuard_closed
    (hguard :
      inverseSquareSingleReverseTenPowNineHighPrefixBefore8192StartWindowCellGuard) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed
    (inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_before8192StartWindowCellGuard
      hguard)

/-- Archived optional absolute-error route for the repository model: a single
candidate-window margin certificate for the rounded high prefix now implies the
repository-model accumulator with Higham's displayed reverse decimal. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_candidateWindowMarginShiftedLowerBound_closed
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed
    (inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_le_candidateWindowMarginShiftedLowerBound
      herr)

/-- Archived optional named-target version of the closed D1 route: if the
repository-model replay is explicitly reopened, the single high-prefix
candidate-window margin target is enough to obtain the displayed reverse
accumulator in that explicit model. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowMarginTarget_closed
    (htarget :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_candidateWindowMarginShiftedLowerBound_closed
    htarget

/-- Archived optional finite-cell route for the repository-model reverse run:
proving the rounded high-prefix state lies strictly inside the
predecessor/successor cell around the candidate window implies the displayed
reverse accumulator in that explicit model. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowCellGuard_closed
    (hguard :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed
    (inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuard
      hguard)

/-- Archived optional strict finite-cell margin route for the repository-model
reverse run: proving the larger strict predecessor/successor-cell absolute-error
target for the rounded high prefix implies the displayed reverse accumulator in
that explicit model. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_cellGuardMarginTarget_closed
    (htarget :
      inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowCellGuard_closed
    (inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_cellGuardMarginTarget
      htarget)

/-- Archived optional standard-envelope route for the repository model: a sharp
bound on the accumulated high-prefix standard-model envelope against the
candidate-window margin now implies the repository-model accumulator with
Higham's displayed reverse decimal. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_stdErrorEnvelope_le_candidateWindowMargin_closed
    (henv :
      inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope
          (10 ^ 9 - 4096) ≤
        inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed
    (inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_le_candidateWindowMargin
      henv)

/-- Archived optional strict-cell standard-envelope route for the repository
model: a sharp envelope bound against the larger predecessor/successor-cell
margin now implies the repository-model accumulator with Higham's displayed
reverse decimal. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_stdErrorEnvelope_lt_cellGuardMargin_closed
    (henv :
      inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope
          (10 ^ 9 - 4096) <
        inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed
    (inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_lt_cellGuardMargin
      henv)

/-- Any state in the 1024-ulp candidate window is within the shifted explicit
margin of the exact high-prefix mass. -/
theorem inverseSquareSingleReverseHighPrefixCandidateWindow_abs_error_le_shiftedMarginLowerBound
    {s : ℝ}
    (hlo : inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤ s)
    (hhi : s ≤ inverseSquareSingleReverseHighPrefixCandidateWindowUpper) :
    |s - inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
      inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound := by
  have hElo :
      inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
    change
      1 / ((4097 : ℝ) - (4096 : ℝ) / 8193) -
          1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (4096 : ℝ) / 8193)) ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)
    exact inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193
  have hEhi :
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
    change
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
        1 / ((4097 : ℝ) - (1 : ℝ) / 2) -
          1 / ((((10 ^ 9 + 1 : ℕ) : ℝ) - (1 : ℝ) / 2))
    exact inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope
  have hleftA :
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint -
          inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
          inverseSquareSingleReverseSuffixStartLower := by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLower,
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
      inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
      inverseSquareSingleReverseSuffixStartLower,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hleftB :
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint -
          inverseSquareSingleReverseHighPrefixCandidateWindowLower ≤
        inverseSquareSingleReverseSuffixStartUpperTight -
          inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowLower,
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
      inverseSquareSingleReverseSuffixStartUpperTight,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hrightA :
      inverseSquareSingleReverseHighPrefixCandidateWindowUpper -
          inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint ≤
        inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
          inverseSquareSingleReverseSuffixStartLower := by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
      inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
      inverseSquareSingleReverseSuffixStartLower,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hrightB :
      inverseSquareSingleReverseHighPrefixCandidateWindowUpper -
          inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint ≤
        inverseSquareSingleReverseSuffixStartUpperTight -
          inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
    norm_num [inverseSquareSingleReverseHighPrefixCandidateWindowUpper,
      inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint,
      inverseSquareSingleReverseHighPrefixHalfUpperEndpoint,
      inverseSquareSingleReverseSuffixStartUpperTight,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  rw [abs_le]
  constructor
  · unfold inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound
    have hleA :
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) - s ≤
          inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
            inverseSquareSingleReverseSuffixStartLower := by
      linarith
    have hleB :
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) - s ≤
          inverseSquareSingleReverseSuffixStartUpperTight -
            inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
      linarith
    have hlemin :
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) - s ≤
          min (inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
              inverseSquareSingleReverseSuffixStartLower)
            (inverseSquareSingleReverseSuffixStartUpperTight -
              inverseSquareSingleReverseHighPrefixHalfUpperEndpoint) :=
      le_min hleA hleB
    linarith
  · unfold inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound
    have hleA :
        s - inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
          inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint -
            inverseSquareSingleReverseSuffixStartLower := by
      linarith
    have hleB :
        s - inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) ≤
          inverseSquareSingleReverseSuffixStartUpperTight -
            inverseSquareSingleReverseHighPrefixHalfUpperEndpoint := by
      linarith
    exact le_min hleA hleB

/-- Candidate-window form of the rounded high-prefix error certificate. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefix_abs_error_le_shiftedMarginLowerBound_of_mem_candidateWindow
    (hwin : inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow) :
    |inverseSquareSingleReverseTenPowNineHighPrefixState -
      inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
      inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound :=
  inverseSquareSingleReverseHighPrefixCandidateWindow_abs_error_le_shiftedMarginLowerBound
    hwin.1 hwin.2

/-- Error-radius form of the high-prefix bridge: it is enough to bound the
rounded high-prefix state within the explicit tight-window margin around the
exact high-prefix mass.  This replaces the too-strong equality target by the
natural interval certificate needed by the refined suffix route. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
        inverseSquareSingleReverseHighPrefixTightWindowMargin) :
    inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow := by
  have hmargin_le_lower :
      inverseSquareSingleReverseHighPrefixTightWindowMargin ≤
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) -
          inverseSquareSingleReverseSuffixStartLower := by
    unfold inverseSquareSingleReverseHighPrefixTightWindowMargin
    exact min_le_left _ _
  have hmargin_le_upper :
      inverseSquareSingleReverseHighPrefixTightWindowMargin ≤
        inverseSquareSingleReverseSuffixStartUpperTight -
          inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) := by
    unfold inverseSquareSingleReverseHighPrefixTightWindowMargin
    exact min_le_right _ _
  have hbounds := abs_le.mp herr
  constructor
  · have hstate_ge :
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) -
            inverseSquareSingleReverseHighPrefixTightWindowMargin ≤
          inverseSquareSingleReverseTenPowNineHighPrefixState := by
      linarith [hbounds.1]
    linarith [hmargin_le_lower, hstate_ge]
  · have hstate_le :
        inverseSquareSingleReverseTenPowNineHighPrefixState ≤
          inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096) +
            inverseSquareSingleReverseHighPrefixTightWindowMargin := by
      linarith [hbounds.2]
    linarith [hmargin_le_upper, hstate_le]

/-- Fully explicit lower-bound variant of
`inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin`:
it is enough to prove the rounded high-prefix state is within the rational
telescoping slack lower bound. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_marginLowerBound
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
        inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound) :
    inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin
    (le_trans herr
      inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_le_margin)

/-- Sharper shifted-bound variant of
`inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin`.
The remaining rounded-prefix error may target the stronger shifted rational
slack, which is large enough to contain the concrete high-prefix candidate. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_shiftedMarginLowerBound
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
        inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound) :
    inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin
    (le_trans herr
      inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound_le_margin)

/-- Candidate-window variant of the refined high-prefix bridge. -/
theorem inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_mem_candidateWindow
    (hwin : inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow) :
    inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow :=
  inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_shiftedMarginLowerBound
    (inverseSquareSingleReverseTenPowNineHighPrefix_abs_error_le_shiftedMarginLowerBound_of_mem_candidateWindow
      hwin)

/-- Archived optional repository-model transfer theorem: after reducing the
rounded high-index prefix to the exact high-index prefix, the whole `10^9` run
equals the displayed reverse accumulator in that explicit model whenever the
ordinary final-suffix window certificate is available. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact
    (hprefix :
      inverseSquareSingleReverseTenPowNineHighPrefixState =
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096))
    (hsuffix : inverseSquareSingleReverseSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_window_certificates
    (inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_exact
      hprefix)
    hsuffix

/-- Tighter-window transfer theorem for the same archived optional
repository-model route. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact_tight
    (hprefix :
      inverseSquareSingleReverseTenPowNineHighPrefixState =
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096))
    (hsuffix : inverseSquareSingleReverseTightSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates
    (inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_eq_exact
      hprefix)
    hsuffix

/-- Error-radius transfer theorem for the archived optional repository-model
route: if the rounded high-index prefix is within the explicit refined-window
margin of the exact high-prefix mass, then the final `4096`-term tight-window
suffix certificate implies the displayed reverse accumulator in that explicit
model. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_margin
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
        inverseSquareSingleReverseHighPrefixTightWindowMargin)
    (hsuffix : inverseSquareSingleReverseTightSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates
    (inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin
      herr)
    hsuffix

/-- Fully explicit lower-bound transfer theorem for the archived optional
repository-model route: an absolute-error bound by the rational telescoping
slack lower bound, together with the tight suffix-window map, implies the
displayed reverse accumulator in that explicit model. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_marginLowerBound
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
        inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound)
    (hsuffix : inverseSquareSingleReverseTightSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates
    (inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_marginLowerBound
      herr)
    hsuffix

/-- Shifted explicit lower-bound transfer theorem for the archived optional
repository-model route: an absolute-error bound by the stronger shifted
rational slack, together with the tight suffix-window map, implies the displayed
reverse accumulator in that explicit model. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_shiftedMarginLowerBound
    (herr :
      |inverseSquareSingleReverseTenPowNineHighPrefixState -
        inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
        inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound)
    (hsuffix : inverseSquareSingleReverseTightSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates
    (inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_shiftedMarginLowerBound
      herr)
    hsuffix

/-- Candidate-window transfer theorem for the archived optional repository-model
route: once the rounded high-prefix state is placed inside the concrete
1024-ulp candidate window, the remaining final step is the existing tight
suffix-window map. -/
theorem inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow
    (hwin : inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow)
    (hsuffix : inverseSquareSingleReverseTightSuffixWindowMapsToPrinted) :
    inverseSquareSingleReverseAccumulator (10 ^ 9) =
      inverseSquareSingleReversePrintedAccumulator :=
  inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates
    (inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_mem_candidateWindow
      hwin)
    hsuffix

/-- Integer mantissa increment for the early forward-summation prefix at term
`k`.  In the exponent-`1` binary32 slice this is nearest-integer rounding of
`2^23 / k^2`, written as an integer expression so the long prefix can be
certified by computation rather than by thousands of separate lemmas. -/
def inverseSquareSingleEarlyMantissaIncrement (k : ℕ) : ℕ :=
  (2 ^ 24 + k ^ 2) / (2 * k ^ 2)

/-- Sum of the early-prefix mantissa increments for terms `2, ..., n+1`. -/
def inverseSquareSingleEarlyMantissaPrefix : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      inverseSquareSingleEarlyMantissaPrefix n +
        inverseSquareSingleEarlyMantissaIncrement (n + 2)

@[simp] theorem inverseSquareSingleEarlyMantissaPrefix_zero :
    inverseSquareSingleEarlyMantissaPrefix 0 = 0 := rfl

@[simp] theorem inverseSquareSingleEarlyMantissaPrefix_succ (n : ℕ) :
    inverseSquareSingleEarlyMantissaPrefix (n + 1) =
      inverseSquareSingleEarlyMantissaPrefix n +
        inverseSquareSingleEarlyMantissaIncrement (n + 2) := rfl

/-- Computed certificate for the early-prefix mantissa increment sum through
`k = 2896`.  This is a checked arithmetic certificate, not a hand-written
enumeration of the prefix. -/
theorem inverseSquareSingleEarlyMantissaPrefix_2895_eq :
    inverseSquareSingleEarlyMantissaPrefix 2895 = 5407148 := by
  set_option maxRecDepth 20000 in
  decide

/-- Adding the certified early-prefix mantissa increment sum to the exact
`k = 1` accumulator gives the pre-window mantissa used by the 2897--4096
plateau proof. -/
theorem inverseSquareSingleEarlyMantissaPrefix_2895_add_base_eq_preWindow :
    8388608 + inverseSquareSingleEarlyMantissaPrefix 2895 = 13795756 := by
  set_option maxRecDepth 20000 in
  decide

/-- Boolean certificate that every early mantissa increment is strictly within
one half-ulp of the exact scaled inverse-square term, and that the resulting
mantissa remains safely inside the IEEE-single normal mantissa range. -/
def inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool : Bool :=
  (List.range 2895).all (fun n =>
    let k := n + 2
    let d := inverseSquareSingleEarlyMantissaIncrement k
    decide (0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 24 ∧
      2 ^ 24 < (2 * d + 1) * k ^ 2 ∧
      8388608 + inverseSquareSingleEarlyMantissaPrefix (n + 1) + 1 ≤
        FloatingPointFormat.ieeeSingleFormat.maxNormalMantissa))

/-- Kernel-checked bounded certificate for the early mantissa increments. -/
theorem inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool_eq_true :
    inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool = true := by
  set_option maxRecDepth 40000 in
  decide

/-- Pointwise extraction of the early mantissa-increment certificate.  For each
term `k = n + 2`, the integer increment `d` lies within strict half-ulp
nearest-rounding bounds for `2^23/k^2`, and the next mantissa stays normal. -/
theorem inverseSquareSingleEarlyMantissaIncrementNearestCertificate
    {n : ℕ} (hn : n < 2895) :
    let k := n + 2
    let d := inverseSquareSingleEarlyMantissaIncrement k
    0 < d ∧
      (2 * d - 1) * k ^ 2 < 2 ^ 24 ∧
      2 ^ 24 < (2 * d + 1) * k ^ 2 ∧
      8388608 + inverseSquareSingleEarlyMantissaPrefix (n + 1) + 1 ≤
        FloatingPointFormat.ieeeSingleFormat.maxNormalMantissa := by
  have hmem : n ∈ List.range 2895 := by
    simpa [List.mem_range] using hn
  have hbool :=
    (List.all_eq_true.mp
      inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool_eq_true)
      n hmem
  exact of_decide_eq_true hbool

/-- Left bracket arithmetic for early nearest-mantissa rounding.  If the
scaled inverse-square term is above the predecessor half-cell, then the exact
sum is strictly to the right of the predecessor mantissa. -/
theorem inverseSquareSingle_pred_lt_add_of_scaled_left_bound
    {m d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hleft : (2 * d - 1) * k ^ 2 < 2 ^ 24) :
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d - 1) (1 : ℤ) <
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
        inverseSquareTerm k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hkRpos : (0 : ℝ) < (k : ℝ)^2 := by positivity
  have hcertR : (((2 * d - 1) * k ^ 2 : ℕ) : ℝ) < ((2 ^ 24 : ℕ) : ℝ) := by
    exact_mod_cast hleft
  have hdcast : ((2 * d - 1 : ℕ) : ℝ) = 2 * (d : ℝ) - 1 := by
    have hsub : 1 ≤ 2 * d := by omega
    rw [Nat.cast_sub hsub]
    norm_num
  have hmdcast : ((m + d - 1 : ℕ) : ℝ) = (m : ℝ) + (d : ℝ) - 1 := by
    have hsub : 1 ≤ m + d := by omega
    rw [Nat.cast_sub hsub]
    norm_num
  have hcertR2 : (2 * (d : ℝ) - 1) * (k : ℝ)^2 < (16777216 : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow, hdcast] using hcertR
  norm_num [FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg, inverseSquareTerm, hmdcast]
  field_simp [hkR]
  nlinarith [hcertR2, hkRpos]

/-- Right bracket arithmetic for early nearest-mantissa rounding.  If the
scaled inverse-square term is below the successor half-cell, then the exact sum
is strictly to the left of the successor mantissa. -/
theorem inverseSquareSingle_add_lt_succ_of_scaled_right_bound
    {m d k : ℕ} (hk : 0 < k)
    (hright : 2 ^ 24 < (2 * d + 1) * k ^ 2) :
    FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
        inverseSquareTerm k <
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d + 1) (1 : ℤ) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hkRpos : (0 : ℝ) < (k : ℝ)^2 := by positivity
  have hcertR : (((2 ^ 24 : ℕ) : ℝ) < (((2 * d + 1) * k ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hright
  have hcertR2 : (16777216 : ℝ) < (2 * (d : ℝ) + 1) * (k : ℝ)^2 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hcertR
  norm_num [FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg, inverseSquareTerm]
  field_simp [hkR]
  nlinarith [hcertR2, hkRpos]

/-- In the left bracket, the exact sum is strictly closer to the certified
target mantissa than to its predecessor. -/
theorem inverseSquareSingle_right_closer_to_target_of_scaled_left_bound
    {m d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hleft : (2 * d - 1) * k ^ 2 < 2 ^ 24)
    (hx_lt_target :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k <
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d) (1 : ℤ)) :
    |(FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d) (1 : ℤ)| <
      |(FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d - 1) (1 : ℤ)| := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hkRpos : (0 : ℝ) < (k : ℝ)^2 := by positivity
  have hcertR : (((2 * d - 1) * k ^ 2 : ℕ) : ℝ) < ((2 ^ 24 : ℕ) : ℝ) := by
    exact_mod_cast hleft
  have hdcast : ((2 * d - 1 : ℕ) : ℝ) = 2 * (d : ℝ) - 1 := by
    have hsub : 1 ≤ 2 * d := by omega
    rw [Nat.cast_sub hsub]
    norm_num
  have hmdcast : ((m + d - 1 : ℕ) : ℝ) = (m : ℝ) + (d : ℝ) - 1 := by
    have hsub : 1 ≤ m + d := by omega
    rw [Nat.cast_sub hsub]
    norm_num
  have hcertR2 : (2 * (d : ℝ) - 1) * (k : ℝ)^2 < (16777216 : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow, hdcast] using hcertR
  have hpred_lt_x :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d - 1) (1 : ℤ) <
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k :=
    inverseSquareSingle_pred_lt_add_of_scaled_left_bound hd hk hleft
  have hxb_nonpos :
      (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d) (1 : ℤ) ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hx_lt_target)
  have hxa_nonneg :
      0 ≤ (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d - 1) (1 : ℤ) :=
    sub_nonneg.mpr (le_of_lt hpred_lt_x)
  rw [abs_of_nonpos hxb_nonpos, abs_of_nonneg hxa_nonneg]
  norm_num [FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg, inverseSquareTerm, hmdcast]
  field_simp [hkR]
  nlinarith [hcertR2, hkRpos]

/-- In the right bracket, the exact sum is strictly closer to the certified
target mantissa than to its successor. -/
theorem inverseSquareSingle_left_closer_to_target_of_scaled_right_bound
    {m d k : ℕ} (hk : 0 < k)
    (hright : 2 ^ 24 < (2 * d + 1) * k ^ 2)
    (htarget_lt_x :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d) (1 : ℤ) <
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k) :
    |(FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d) (1 : ℤ)| <
      |(FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d + 1) (1 : ℤ)| := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hkRpos : (0 : ℝ) < (k : ℝ)^2 := by positivity
  have hcertR : (((2 ^ 24 : ℕ) : ℝ) < (((2 * d + 1) * k ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hright
  have hcertR2 : (16777216 : ℝ) < (2 * (d : ℝ) + 1) * (k : ℝ)^2 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hcertR
  have hx_lt_succ :
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k <
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d + 1) (1 : ℤ) :=
    inverseSquareSingle_add_lt_succ_of_scaled_right_bound hk hright
  have hxb_nonneg :
      0 ≤ (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d) (1 : ℤ) :=
    sub_nonneg.mpr (le_of_lt htarget_lt_x)
  have hxc_nonpos :
      (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ) +
          inverseSquareTerm k) -
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d + 1) (1 : ℤ) ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hx_lt_succ)
  rw [abs_of_nonneg hxb_nonneg, abs_of_nonpos hxc_nonpos]
  norm_num [FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg, inverseSquareTerm]
  field_simp [hkR]
  nlinarith [hcertR2, hkRpos]

/-- Source-rounding bridge for the early prefix.  If the scaled inverse-square
term lies strictly inside the half-ulp cell around mantissa increment `d`, and
the predecessor/target/successor mantissas are normal, then finite
round-to-even addition returns the target mantissa. -/
theorem inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds
    {m d k : ℕ}
    (hd : 0 < d) (hk : 0 < k)
    (hleft : (2 * d - 1) * k ^ 2 < 2 ^ 24)
    (hright : 2 ^ 24 < (2 * d + 1) * k ^ 2)
    (hmpred : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d - 1))
    (hmtarget : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d))
    (hmsucc : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d + 1)) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ))
        (inverseSquareTerm k) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + d) (1 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let x : ℝ := fmt.normalizedValue false m (1 : ℤ) + inverseSquareTerm k
  let y : ℝ := fmt.normalizedValue false (m + d) (1 : ℤ)
  let pred : ℝ := fmt.normalizedValue false (m + d - 1) (1 : ℤ)
  let succ : ℝ := fmt.normalizedValue false (m + d + 1) (1 : ℤ)
  have hexp : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hpredSystem : fmt.normalizedSystem pred := by
    exact ⟨false, m + d - 1, (1 : ℤ), hmpred, hexp, rfl⟩
  have hySystem : fmt.normalizedSystem y := by
    exact ⟨false, m + d, (1 : ℤ), hmtarget, hexp, rfl⟩
  have hsuccSystem : fmt.normalizedSystem succ := by
    exact ⟨false, m + d + 1, (1 : ℤ), hmsucc, hexp, rfl⟩
  have hpred_lt_x : pred < x := by
    simpa [pred, x, fmt] using
      inverseSquareSingle_pred_lt_add_of_scaled_left_bound
        (m := m) (d := d) (k := k) hd hk hleft
  have hx_lt_succ : x < succ := by
    simpa [succ, x, fmt] using
      inverseSquareSingle_add_lt_succ_of_scaled_right_bound
        (m := m) (d := d) (k := k) hk hright
  have hpred_pos : 0 < pred := by
    simpa [pred, fmt] using
      fmt.normalizedValue_false_pos (m := m + d - 1) (e := (1 : ℤ)) hmpred
  have hsucc_pos : 0 < succ := by
    simpa [succ, fmt] using
      fmt.normalizedValue_false_pos (m := m + d + 1) (e := (1 : ℤ)) hmsucc
  have hxpos : 0 < x := lt_trans hpred_pos hpred_lt_x
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg (le_of_lt hxpos)]
    constructor
    · have hmin_le_pred : fmt.minNormalMagnitude ≤ pred := by
        simpa [FloatingPointFormat.minNormalMagnitude, abs_of_pos hpred_pos] using
          fmt.normalizedSystem_abs_lower_bound hpredSystem
      exact le_trans hmin_le_pred (le_of_lt hpred_lt_x)
    · have hsucc_le_max : succ ≤ fmt.maxFiniteMagnitude := by
        simpa [FloatingPointFormat.maxFiniteMagnitude, abs_of_pos hsucc_pos] using
          fmt.normalizedSystem_abs_le_maxFinite_bound hsuccSystem
      exact le_trans (le_of_lt hx_lt_succ) hsucc_le_max
  by_cases hxy : x = y
  · have hyfinite : fmt.finiteSystem y := Or.inr (Or.inl hySystem)
    have hround : fmt.finiteRoundToEven x = y := by
      rw [hxy]
      exact fmt.finiteRoundToEven_eq_self_of_finiteSystem hyfinite
    simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact, x, y, fmt] using hround
  · have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
      fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
    rcases lt_or_gt_of_ne hxy with hx_lt_y | hy_lt_x
    · have hadj : fmt.realOrderAdjacentNormalized pred y := by
        refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
        refine ⟨false, m + d - 1, (1 : ℤ), hmpred, ?_, Or.inl ⟨rfl, ?_⟩⟩
        · simpa [Nat.sub_add_cancel (by omega : 1 ≤ m + d)] using hmtarget
        · simp [y, Nat.sub_add_cancel (by omega : 1 ≤ m + d)]
      have hrightCloser : |x - y| < |x - pred| := by
        simpa [x, y, pred, fmt] using
          inverseSquareSingle_right_closer_to_target_of_scaled_left_bound
            (m := m) (d := d) (k := k) hd hk hleft (by simpa [x, y, fmt] using hx_lt_y)
      have hround : fmt.finiteRoundToEven x = y :=
        fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
          hpolicy hadj ⟨hpred_lt_x, hx_lt_y⟩ hrightCloser
      simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact, x, y, fmt] using hround
    · have hadj : fmt.realOrderAdjacentNormalized y succ := by
        refine fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized ?_
        exact ⟨false, m + d, (1 : ℤ), hmtarget, hmsucc, Or.inl ⟨rfl, rfl⟩⟩
      have hleftCloser : |x - y| < |x - succ| := by
        simpa [x, y, succ, fmt] using
          inverseSquareSingle_left_closer_to_target_of_scaled_right_bound
            (m := m) (d := d) (k := k) hk hright (by simpa [x, y, fmt] using hy_lt_x)
      have hround : fmt.finiteRoundToEven x = y :=
        fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
          hpolicy hadj ⟨hy_lt_x, hx_lt_succ⟩ hleftCloser
      simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact, x, y, fmt] using hround

/-- The actual forward accumulator after the first term is exactly one in the
binary32 model. -/
theorem inverseSquareSingleForwardAccumulator_one_eq_one :
    inverseSquareSingleForwardAccumulator 1 =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8388608 (1 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hone_finite : fmt.finiteSystem (1 : ℝ) := by
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 8388608, (1 : ℤ), ?hm, ?he, ?hval⟩
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    · norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, zpow_neg]
      rfl
  calc
    inverseSquareSingleForwardAccumulator 1 =
        FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp
          BasicOp.add 0 (inverseSquareTerm 1) := by
      simp [inverseSquareSingleForwardAccumulator,
        inverseSquareSingleForwardAccumulatorFrom, inverseSquareSingleForwardStep]
    _ = (1 : ℝ) := by
      simpa [fmt, inverseSquareTerm, BasicOp.exact] using
        (fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem hone_finite)
    _ = FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8388608 (1 : ℤ) := by
      norm_num [FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
        FloatingPointFormat.betaR, zpow_neg]
      rfl

/-- Uniform local rounding rule that remains to close the early prefix:
starting from the exponent-`1` binary32 accumulator whose mantissa is the base
mantissa plus the certified prefix sum through `n`, adding term `n+2` advances
the mantissa by the corresponding integer increment. -/
noncomputable def inverseSquareSingleEarlyMantissaIncrementRule : Prop :=
  ∀ n, n < 2895 →
    inverseSquareSingleForwardStep
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
          (8388608 + inverseSquareSingleEarlyMantissaPrefix n) (1 : ℤ))
        (n + 2) =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false
        (8388608 + inverseSquareSingleEarlyMantissaPrefix (n + 1)) (1 : ℤ)

/-- The uniform early-prefix rounding rule is closed by the bounded
nearest-increment certificate and the source-rounding bridge. -/
theorem inverseSquareSingleEarlyMantissaIncrementRule_closed :
    inverseSquareSingleEarlyMantissaIncrementRule := by
  intro n hn
  let k := n + 2
  let p := inverseSquareSingleEarlyMantissaPrefix n
  let d := inverseSquareSingleEarlyMantissaIncrement k
  let m := 8388608 + p
  have hcert := inverseSquareSingleEarlyMantissaIncrementNearestCertificate hn
  have hd : 0 < d := by
    simpa [k, d] using hcert.1
  have hleft : (2 * d - 1) * k ^ 2 < 2 ^ 24 := by
    simpa [k, d] using hcert.2.1
  have hright : 2 ^ 24 < (2 * d + 1) * k ^ 2 := by
    simpa [k, d] using hcert.2.2.1
  have hmax : m + d + 1 ≤ FloatingPointFormat.ieeeSingleFormat.maxNormalMantissa := by
    simpa [m, p, d, k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      hcert.2.2.2
  have hk : 0 < k := by omega
  have hmaxNat : m + d + 1 ≤ 16777215 := by
    simpa [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.maxNormalMantissa] using hmax
  have hpredNorm :
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d - 1) := by
    constructor
    · norm_num [FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMantissa, m]
      omega
    · norm_num [FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.mantissaInRange]
      omega
  have htargetNorm :
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d) := by
    constructor
    · norm_num [FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMantissa, m]
      omega
    · norm_num [FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.mantissaInRange]
      omega
  have hsuccNorm :
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + d + 1) := by
    constructor
    · norm_num [FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMantissa, m]
      omega
    · norm_num [FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.mantissaInRange]
      omega
  have hround :=
    inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds
      (m := m) (d := d) (k := k) hd hk hleft hright
      hpredNorm htargetNorm hsuccNorm
  simpa [inverseSquareSingleForwardStep, m, p, d, k, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using hround

/-- Conditional early-prefix bridge.  Once the uniform local increment rule is
proved for terms `2, ..., 2896`, the actual left-to-right accumulator reaches
the pre-window value used by the already-proved 2897--4096 plateau theorem. -/
theorem inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart_of_early_mantissa_increment_rule
    (hrule : inverseSquareSingleEarlyMantissaIncrementRule) :
    inverseSquareSingleForwardAccumulator 2896 =
      inverseSquareSinglePrePlateauWindowStartAccumulator := by
  have htrace :
      ∀ n, n ≤ 2895 →
        inverseSquareSingleForwardAccumulatorFrom
            (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
              8388608 (1 : ℤ)) 2 n =
          FloatingPointFormat.ieeeSingleFormat.normalizedValue false
            (8388608 + inverseSquareSingleEarlyMantissaPrefix n) (1 : ℤ) := by
    intro n hn
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hnlt : n < 2895 := by omega
        have hprev := ih (by omega)
        calc
          inverseSquareSingleForwardAccumulatorFrom
              (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
                8388608 (1 : ℤ)) 2 (n + 1) =
            inverseSquareSingleForwardStep
              (inverseSquareSingleForwardAccumulatorFrom
                (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
                  8388608 (1 : ℤ)) 2 n) (2 + n) := rfl
          _ =
            inverseSquareSingleForwardStep
              (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
                (8388608 + inverseSquareSingleEarlyMantissaPrefix n) (1 : ℤ))
              (n + 2) := by
            rw [hprev]
            congr 1
            omega
          _ =
            FloatingPointFormat.ieeeSingleFormat.normalizedValue false
              (8388608 + inverseSquareSingleEarlyMantissaPrefix (n + 1))
              (1 : ℤ) :=
            hrule n hnlt
  calc
    inverseSquareSingleForwardAccumulator 2896 =
        inverseSquareSingleForwardAccumulatorFrom
          (inverseSquareSingleForwardAccumulator 1) (1 + 1) 2895 := by
      rw [show 2896 = 1 + 2895 by omega]
      rw [inverseSquareSingleForwardAccumulator_add]
    _ =
        inverseSquareSingleForwardAccumulatorFrom
          (FloatingPointFormat.ieeeSingleFormat.normalizedValue false
            8388608 (1 : ℤ)) 2 2895 := by
      rw [inverseSquareSingleForwardAccumulator_one_eq_one]
    _ =
        FloatingPointFormat.ieeeSingleFormat.normalizedValue false
          (8388608 + inverseSquareSingleEarlyMantissaPrefix 2895) (1 : ℤ) :=
      htrace 2895 (by omega)
    _ = inverseSquareSinglePrePlateauWindowStartAccumulator := by
      rw [inverseSquareSingleEarlyMantissaPrefix_2895_add_base_eq_preWindow]
      rfl

/-- The actual early forward prefix reaches the pre-window accumulator after
the `k = 2896` term. -/
theorem inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart :
    inverseSquareSingleForwardAccumulator 2896 =
      inverseSquareSinglePrePlateauWindowStartAccumulator :=
  inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart_of_early_mantissa_increment_rule
    inverseSquareSingleEarlyMantissaIncrementRule_closed

/-- The range-index successor theorem specialized to a normal adjacent
binary32 pair at exponent `1`.  The finite-range side conditions are derived
from normalized-system bounds, leaving only normalized mantissas and the
`2897 <= k < 4096` index range visible. -/
theorem inverseSquareSingleForwardStep_normalizedValue_succ_of_index_range
    {m k : ℕ}
    (hm : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa m)
    (hmnext : FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m + 1))
    (hklo : 2897 ≤ k) (hkhi : k < 4096) :
    inverseSquareSingleForwardStep
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m (1 : ℤ)) k =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m + 1) (1 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hexp : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  have hleftSystem : fmt.normalizedSystem (fmt.normalizedValue false m (1 : ℤ)) :=
    ⟨false, m, (1 : ℤ), hm, hexp, rfl⟩
  have hnextSystem :
      fmt.normalizedSystem (fmt.normalizedValue false (m + 1) (1 : ℤ)) :=
    ⟨false, m + 1, (1 : ℤ), hmnext, hexp, rfl⟩
  have hleft_pos : 0 < fmt.normalizedValue false m (1 : ℤ) :=
    fmt.normalizedValue_false_pos hm
  have hnext_pos : 0 < fmt.normalizedValue false (m + 1) (1 : ℤ) :=
    fmt.normalizedValue_false_pos hmnext
  have hmin_le_left :
      fmt.minNormalMagnitude ≤ fmt.normalizedValue false m (1 : ℤ) := by
    simpa [FloatingPointFormat.minNormalMagnitude, abs_of_pos hleft_pos] using
      fmt.normalizedSystem_abs_lower_bound hleftSystem
  have hnext_le_max :
      fmt.normalizedValue false (m + 1) (1 : ℤ) ≤ fmt.maxFiniteMagnitude := by
    simpa [FloatingPointFormat.maxFiniteMagnitude, abs_of_pos hnext_pos] using
      fmt.normalizedSystem_abs_le_maxFinite_bound hnextSystem
  simpa [inverseSquareSingleForwardStep, fmt] using
    inverseSquareSingle_add_term_rounds_to_next_of_index_range
      hm hmnext hmin_le_left hnext_le_max hklo hkhi

/-- Generic operation-trace bridge for a whole pre-plateau index window.  If
the term indices stay in `2897 <= k < 4096` and the displayed mantissas remain
adjacent normalized binary32 mantissas, then the rounded accumulator advances
one ulp per step.  This is the induction surface for the repository's explicit
binary32 prefix model, not a replay of the under-specified historical Fortran
environment. -/
theorem inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window
    {m0 k0 n : ℕ}
    (hm : ∀ j, j < n →
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m0 + j))
    (hmnext : ∀ j, j < n →
      FloatingPointFormat.ieeeSingleFormat.normalizedMantissa (m0 + j + 1))
    (hklo : ∀ j, j < n → 2897 ≤ k0 + j)
    (hkhi : ∀ j, j < n → k0 + j < 4096) :
    inverseSquareSingleForwardAccumulatorFrom
        (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m0 (1 : ℤ))
        k0 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m0 + n) (1 : ℤ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hprefix :=
        ih
          (fun j hj => hm j (Nat.lt_trans hj (Nat.lt_succ_self n)))
          (fun j hj => hmnext j (Nat.lt_trans hj (Nat.lt_succ_self n)))
          (fun j hj => hklo j (Nat.lt_trans hj (Nat.lt_succ_self n)))
          (fun j hj => hkhi j (Nat.lt_trans hj (Nat.lt_succ_self n)))
      have hstep :=
        inverseSquareSingleForwardStep_normalizedValue_succ_of_index_range
          (hm n (Nat.lt_succ_self n))
          (hmnext n (Nat.lt_succ_self n))
          (hklo n (Nat.lt_succ_self n))
          (hkhi n (Nat.lt_succ_self n))
      calc
        inverseSquareSingleForwardAccumulatorFrom
            (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m0 (1 : ℤ))
            k0 (n + 1) =
          inverseSquareSingleForwardStep
            (inverseSquareSingleForwardAccumulatorFrom
              (FloatingPointFormat.ieeeSingleFormat.normalizedValue false m0 (1 : ℤ))
              k0 n) (k0 + n) := rfl
        _ =
          inverseSquareSingleForwardStep
            (FloatingPointFormat.ieeeSingleFormat.normalizedValue false (m0 + n) (1 : ℤ))
            (k0 + n) := by rw [hprefix]
        _ = FloatingPointFormat.ieeeSingleFormat.normalizedValue false
            (m0 + (n + 1)) (1 : ℤ) := by
          simpa [Nat.add_assoc] using hstep

/-- Starting six ulps below Higham §1.12.3's printed plateau, the forward
single-precision trace for the five terms `4091^{-2}` through `4095^{-2}`
reaches the immediately preceding binary32 accumulator.  This composes the
range successor theorem by induction instead of relying on five independent
operation-trace proofs. -/
theorem inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_five_eq_prePlateau :
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSingleSixBeforePlateauAccumulator 4091 5 =
      inverseSquareSinglePrePlateauAccumulator := by
  have htrace :=
    inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window
      (m0 := 13796950) (k0 := 4091) (n := 5)
      (hm := by
        intro j hj
        constructor
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.minNormalMantissa]
          omega
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.mantissaInRange]
          omega)
      (hmnext := by
        intro j hj
        constructor
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.minNormalMantissa]
          omega
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.mantissaInRange]
          omega)
      (hklo := by
        intro j hj
        omega)
      (hkhi := by
        intro j hj
        omega)
  simpa [inverseSquareSingleSixBeforePlateauAccumulator,
    inverseSquareSinglePrePlateauAccumulator] using htrace

/-- Continuing one more term, the same forward trace reaches the displayed
single-precision plateau exactly at the `4096^{-2}` midpoint step. -/
theorem inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_six_eq_plateau :
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSingleSixBeforePlateauAccumulator 4091 6 =
      inverseSquareSinglePlateauAccumulator := by
  calc
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSingleSixBeforePlateauAccumulator 4091 6 =
      inverseSquareSingleForwardStep
        (inverseSquareSingleForwardAccumulatorFrom
          inverseSquareSingleSixBeforePlateauAccumulator 4091 5) (4091 + 5) := rfl
    _ = inverseSquareSingleForwardStep
        inverseSquareSinglePrePlateauAccumulator 4096 := by
      rw [inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_five_eq_prePlateau]
    _ = inverseSquareSinglePlateauAccumulator := by
      simpa [inverseSquareSingleForwardStep] using
        inverseSquareSinglePrePlateau_add_4096_term_rounds_to_plateau

/-- Intermediate-value form of the local `4091, ..., 4095` predecessor tail.
For any prefix of those five rounded additions, the accumulator advances one
mantissa per term from the six-before-plateau value. -/
theorem inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_of_le_5
    {n : ℕ} (hn : n ≤ 5) :
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSingleSixBeforePlateauAccumulator 4091 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (13796950 + n) (1 : ℤ) := by
  have htrace :=
    inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window
      (m0 := 13796950) (k0 := 4091) (n := n)
      (hm := by
        intro j hj
        constructor
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.minNormalMantissa]
          omega
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.mantissaInRange]
          omega)
      (hmnext := by
        intro j hj
        constructor
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.minNormalMantissa]
          omega
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.mantissaInRange]
          omega)
      (hklo := by
        intro j hj
        omega)
      (hkhi := by
        intro j hj
        omega)
  rw [inverseSquareSingleSixBeforePlateauAccumulator]
  exact htrace

/-- Intermediate-value form of the 2897--4090 pre-plateau window.  For every
prefix length within that window, starting from the pre-window accumulator
advances exactly one mantissa per term.  This is the reusable spine for a future
first-stagnation trace: the only missing input is that the early repository-model
prefix reaches the pre-window accumulator after `k = 2896`. -/
theorem inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_of_le_1194
    {n : ℕ} (hn : n ≤ 1194) :
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSinglePrePlateauWindowStartAccumulator 2897 n =
      FloatingPointFormat.ieeeSingleFormat.normalizedValue false (13795756 + n) (1 : ℤ) := by
  have htrace :=
    inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window
      (m0 := 13795756) (k0 := 2897) (n := n)
      (hm := by
        intro j hj
        constructor
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.minNormalMantissa]
          omega
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.mantissaInRange]
          omega)
      (hmnext := by
        intro j hj
        constructor
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.minNormalMantissa]
          omega
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.mantissaInRange]
          omega)
      (hklo := by
        intro j hj
        omega)
      (hkhi := by
        intro j hj
        omega)
  rw [inverseSquareSinglePrePlateauWindowStartAccumulator]
  exact htrace

/-- The whole strict-pre-plateau range window in Higham §1.12.3 is now
formalized by a single induction theorem.  Starting from the binary32 value
with mantissa `13795756` at the end of the early prefix, the 1194 rounded
additions `k = 2897, ..., 4090` advance one ulp per term and land six ulps
below the displayed plateau. -/
theorem inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1194_eq_sixBeforePlateau :
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSinglePrePlateauWindowStartAccumulator 2897 1194 =
      inverseSquareSingleSixBeforePlateauAccumulator := by
  have htrace :=
    inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window
      (m0 := 13795756) (k0 := 2897) (n := 1194)
      (hm := by
        intro j hj
        constructor
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.minNormalMantissa]
          omega
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.mantissaInRange]
          omega)
      (hmnext := by
        intro j hj
        constructor
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.minNormalMantissa]
          omega
        · norm_num [FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.mantissaInRange]
          omega)
      (hklo := by
        intro j hj
        omega)
      (hkhi := by
        intro j hj
        omega)
  rw [inverseSquareSinglePrePlateauWindowStartAccumulator,
    inverseSquareSingleSixBeforePlateauAccumulator]
  have hmant : 13795756 + 1194 = 13796950 := by norm_num
  rw [← hmant]
  exact htrace

/-- Throughout the proved 2897--4095 pre-plateau window, the running
accumulator remains strictly below the displayed plateau.  This is the
non-enumerative no-stagnation half of the first-stagnation trace, conditional
only on starting this window at the pre-window accumulator. -/
theorem inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_lt_plateau_of_lt_1200
    {n : ℕ} (hn : n < 1200) :
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSinglePrePlateauWindowStartAccumulator 2897 n <
      inverseSquareSinglePlateauAccumulator := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  by_cases hpre : n ≤ 1194
  · rw [inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_of_le_1194 hpre,
      inverseSquareSinglePlateauAccumulator]
    exact (fmt.normalizedValue_sameExponent_lt_iff_false
      (13795756 + n) 13796956 (1 : ℤ)).2 (by omega)
  · have hge : 1194 ≤ n := by omega
    have hdecomp : n = 1194 + (n - 1194) := by omega
    have htail_le : n - 1194 ≤ 5 := by omega
    calc
      inverseSquareSingleForwardAccumulatorFrom
          inverseSquareSinglePrePlateauWindowStartAccumulator 2897 n =
        inverseSquareSingleForwardAccumulatorFrom
          inverseSquareSinglePrePlateauWindowStartAccumulator 2897
          (1194 + (n - 1194)) := by
        exact congrArg
          (fun q => inverseSquareSingleForwardAccumulatorFrom
            inverseSquareSinglePrePlateauWindowStartAccumulator 2897 q)
          hdecomp
      _ =
        inverseSquareSingleForwardAccumulatorFrom
          (inverseSquareSingleForwardAccumulatorFrom
            inverseSquareSinglePrePlateauWindowStartAccumulator 2897 1194)
          (2897 + 1194) (n - 1194) := by
        rw [inverseSquareSingleForwardAccumulatorFrom_add]
      _ =
        inverseSquareSingleForwardAccumulatorFrom
          inverseSquareSingleSixBeforePlateauAccumulator 4091 (n - 1194) := by
        rw [inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1194_eq_sixBeforePlateau]
      _ = FloatingPointFormat.ieeeSingleFormat.normalizedValue false
          (13796950 + (n - 1194)) (1 : ℤ) := by
        rw [inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_of_le_5 htail_le]
      _ < inverseSquareSinglePlateauAccumulator := by
        rw [inverseSquareSinglePlateauAccumulator]
        exact (fmt.normalizedValue_sameExponent_lt_iff_false
          (13796950 + (n - 1194)) 13796956 (1 : ℤ)).2 (by omega)

/-- One more predecessor step in the local §1.12.3 forward summation trace:
adding `4091^{-2}` to the binary32 accumulator six ulps below the displayed
plateau is strictly closer to the next binary32 value than to the current
accumulator, so nearest/even rounds to the five-before-plateau accumulator.
This does not derive that the full forward loop reaches the six-before-plateau
accumulator at `k = 4090`; it closes the concrete `k = 4091` successor step once
that accumulator is available. -/
theorem inverseSquareSingleSixBeforePlateau_add_4091_term_rounds_to_fiveBeforePlateau :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        inverseSquareSingleSixBeforePlateauAccumulator (inverseSquareTerm 4091) =
      inverseSquareSingleFiveBeforePlateauAccumulator := by
  apply inverseSquareSingle_add_term_rounds_to_next_of_half_ulp_lt
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.betaR,
      zpow_neg]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR,
      zpow_neg]
    change (13796951 : ℝ) / 8388608 ≤
      340282346638528859811704183484516925440
    norm_num
  · norm_num [inverseSquareTerm]
  · norm_num [inverseSquareTerm]
  · norm_num [inverseSquareTerm]

/-- One more predecessor step in the local §1.12.3 forward summation trace:
adding `4092^{-2}` to the binary32 accumulator five ulps below the displayed
plateau is strictly closer to the next binary32 value than to the current
accumulator, so nearest/even rounds to the four-before-plateau accumulator.
This does not derive that the full forward loop reaches the five-before-plateau
accumulator at `k = 4091`; it closes the concrete `k = 4092` successor step once
that accumulator is available. -/
theorem inverseSquareSingleFiveBeforePlateau_add_4092_term_rounds_to_fourBeforePlateau :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        inverseSquareSingleFiveBeforePlateauAccumulator (inverseSquareTerm 4092) =
      inverseSquareSingleFourBeforePlateauAccumulator := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 13796951
  let a : ℝ := fmt.normalizedValue false m 1
  let b : ℝ := fmt.normalizedValue false (m + 1) 1
  let term : ℝ := inverseSquareTerm 4092
  let x : ℝ := a + term
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hb_sub : b - a = 1 / (2 : ℝ) ^ 23 := by
    norm_num [a, b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hterm_pos : 0 < term := by
    norm_num [term, inverseSquareTerm]
  have hterm_lt_spacing : term < 1 / (2 : ℝ) ^ 23 := by
    norm_num [term, inverseSquareTerm]
  have hhalf_lt_term : 1 / (2 : ℝ) ^ 24 < term := by
    norm_num [term, inverseSquareTerm]
  have hstrict : a < x ∧ x < b := by
    constructor
    · simp [x]
      exact hterm_pos
    · have : a + term < b := by
        nlinarith [hb_sub, hterm_lt_spacing]
      simpa [x] using this
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      have ha_pos : 0 < a := by
        norm_num [a, m, fmt, FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      positivity
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have ha_large : fmt.minNormalMagnitude ≤ a := by
        norm_num [a, m, fmt, FloatingPointFormat.minNormalMagnitude,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      have ha_le_x : a ≤ x := le_of_lt hstrict.1
      exact le_trans ha_large ha_le_x
    · have hx_lt : x < b := hstrict.2
      have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
        calc
          b = (13796952 : ℝ) / 8388608 := by
            norm_num [b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedValue,
              FloatingPointFormat.signValue,
              FloatingPointFormat.betaR,
              zpow_neg]
          _ ≤ 340282346638528859811704183484516925440 := by
            norm_num
          _ = fmt.maxFiniteMagnitude := by
            norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.betaR,
              zpow_neg]
            rfl
      exact le_trans (le_of_lt hx_lt) hb_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    have hxa : x - a = term := by
      simp [x]
    have hxb : x - b = term - (1 / (2 : ℝ) ^ 23) := by
      calc
        x - b = a + term - b := by simp [x]
        _ = term - (b - a) := by ring
        _ = term - (1 / (2 : ℝ) ^ 23) := by rw [hb_sub]
    have hspacing_twice : 1 / (2 : ℝ) ^ 23 = 2 * (1 / (2 : ℝ) ^ 24) := by
      norm_num
    have hright : (1 / (2 : ℝ) ^ 23) - term < term := by
      nlinarith
    have hneg : term - (1 / (2 : ℝ) ^ 23) < 0 := by
      nlinarith [hterm_lt_spacing]
    calc
      |x - b| = (1 / (2 : ℝ) ^ 23) - term := by
        rw [hxb, abs_of_neg hneg]
        ring
      _ < term := hright
      _ = |x - a| := by rw [hxa, abs_of_pos hterm_pos]
  have hround :
      fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
    inverseSquareSingleFiveBeforePlateauAccumulator,
    inverseSquareSingleFourBeforePlateauAccumulator, inverseSquareTerm, term, x, a, b, fmt, m]
    using hround

/-- One more predecessor step in the local §1.12.3 forward summation trace:
adding `4093^{-2}` to the binary32 accumulator four ulps below the displayed
plateau is strictly closer to the next binary32 value than to the current
accumulator, so nearest/even rounds to the three-before-plateau accumulator.
This does not derive that the full forward loop reaches the four-before-plateau
accumulator at `k = 4092`; it closes the concrete `k = 4093` successor step once
that accumulator is available. -/
theorem inverseSquareSingleFourBeforePlateau_add_4093_term_rounds_to_threeBeforePlateau :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        inverseSquareSingleFourBeforePlateauAccumulator (inverseSquareTerm 4093) =
      inverseSquareSingleThreeBeforePlateauAccumulator := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 13796952
  let a : ℝ := fmt.normalizedValue false m 1
  let b : ℝ := fmt.normalizedValue false (m + 1) 1
  let term : ℝ := inverseSquareTerm 4093
  let x : ℝ := a + term
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hb_sub : b - a = 1 / (2 : ℝ) ^ 23 := by
    norm_num [a, b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hterm_pos : 0 < term := by
    norm_num [term, inverseSquareTerm]
  have hterm_lt_spacing : term < 1 / (2 : ℝ) ^ 23 := by
    norm_num [term, inverseSquareTerm]
  have hhalf_lt_term : 1 / (2 : ℝ) ^ 24 < term := by
    norm_num [term, inverseSquareTerm]
  have hstrict : a < x ∧ x < b := by
    constructor
    · simp [x]
      exact hterm_pos
    · have : a + term < b := by
        nlinarith [hb_sub, hterm_lt_spacing]
      simpa [x] using this
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      have ha_pos : 0 < a := by
        norm_num [a, m, fmt, FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      positivity
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have ha_large : fmt.minNormalMagnitude ≤ a := by
        norm_num [a, m, fmt, FloatingPointFormat.minNormalMagnitude,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      have ha_le_x : a ≤ x := le_of_lt hstrict.1
      exact le_trans ha_large ha_le_x
    · have hx_lt : x < b := hstrict.2
      have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
        calc
          b = (13796953 : ℝ) / 8388608 := by
            norm_num [b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedValue,
              FloatingPointFormat.signValue,
              FloatingPointFormat.betaR,
              zpow_neg]
          _ ≤ 340282346638528859811704183484516925440 := by
            norm_num
          _ = fmt.maxFiniteMagnitude := by
            norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.betaR,
              zpow_neg]
            rfl
      exact le_trans (le_of_lt hx_lt) hb_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    have hxa : x - a = term := by
      simp [x]
    have hxb : x - b = term - (1 / (2 : ℝ) ^ 23) := by
      calc
        x - b = a + term - b := by simp [x]
        _ = term - (b - a) := by ring
        _ = term - (1 / (2 : ℝ) ^ 23) := by rw [hb_sub]
    have hspacing_twice : 1 / (2 : ℝ) ^ 23 = 2 * (1 / (2 : ℝ) ^ 24) := by
      norm_num
    have hright : (1 / (2 : ℝ) ^ 23) - term < term := by
      nlinarith
    have hneg : term - (1 / (2 : ℝ) ^ 23) < 0 := by
      nlinarith [hterm_lt_spacing]
    calc
      |x - b| = (1 / (2 : ℝ) ^ 23) - term := by
        rw [hxb, abs_of_neg hneg]
        ring
      _ < term := hright
      _ = |x - a| := by rw [hxa, abs_of_pos hterm_pos]
  have hround :
      fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
    inverseSquareSingleFourBeforePlateauAccumulator,
    inverseSquareSingleThreeBeforePlateauAccumulator, inverseSquareTerm, term, x, a, b, fmt, m]
    using hround

/-- One more predecessor step in the local §1.12.3 forward summation trace:
adding `4094^{-2}` to the binary32 accumulator three ulps below the displayed
plateau is strictly closer to the next binary32 value than to the current
accumulator, so nearest/even rounds to the two-before-plateau accumulator. This
does not derive that the full forward loop reaches the three-before-plateau
accumulator at `k = 4093`; it closes the concrete `k = 4094` successor step once
that accumulator is available. -/
theorem inverseSquareSingleThreeBeforePlateau_add_4094_term_rounds_to_twoBeforePlateau :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        inverseSquareSingleThreeBeforePlateauAccumulator (inverseSquareTerm 4094) =
      inverseSquareSingleTwoBeforePlateauAccumulator := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 13796953
  let a : ℝ := fmt.normalizedValue false m 1
  let b : ℝ := fmt.normalizedValue false (m + 1) 1
  let term : ℝ := inverseSquareTerm 4094
  let x : ℝ := a + term
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hb_sub : b - a = 1 / (2 : ℝ) ^ 23 := by
    norm_num [a, b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hterm_pos : 0 < term := by
    norm_num [term, inverseSquareTerm]
  have hterm_lt_spacing : term < 1 / (2 : ℝ) ^ 23 := by
    norm_num [term, inverseSquareTerm]
  have hhalf_lt_term : 1 / (2 : ℝ) ^ 24 < term := by
    norm_num [term, inverseSquareTerm]
  have hstrict : a < x ∧ x < b := by
    constructor
    · simp [x]
      exact hterm_pos
    · have : a + term < b := by
        nlinarith [hb_sub, hterm_lt_spacing]
      simpa [x] using this
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      have ha_pos : 0 < a := by
        norm_num [a, m, fmt, FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      positivity
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have ha_large : fmt.minNormalMagnitude ≤ a := by
        norm_num [a, m, fmt, FloatingPointFormat.minNormalMagnitude,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      have ha_le_x : a ≤ x := le_of_lt hstrict.1
      exact le_trans ha_large ha_le_x
    · have hx_lt : x < b := hstrict.2
      have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
        calc
          b = (13796954 : ℝ) / 8388608 := by
            norm_num [b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedValue,
              FloatingPointFormat.signValue,
              FloatingPointFormat.betaR,
              zpow_neg]
          _ ≤ 340282346638528859811704183484516925440 := by
            norm_num
          _ = fmt.maxFiniteMagnitude := by
            norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.betaR,
              zpow_neg]
            rfl
      exact le_trans (le_of_lt hx_lt) hb_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    have hxa : x - a = term := by
      simp [x]
    have hxb : x - b = term - (1 / (2 : ℝ) ^ 23) := by
      calc
        x - b = a + term - b := by simp [x]
        _ = term - (b - a) := by ring
        _ = term - (1 / (2 : ℝ) ^ 23) := by rw [hb_sub]
    have hspacing_twice : 1 / (2 : ℝ) ^ 23 = 2 * (1 / (2 : ℝ) ^ 24) := by
      norm_num
    have hright : (1 / (2 : ℝ) ^ 23) - term < term := by
      nlinarith
    have hneg : term - (1 / (2 : ℝ) ^ 23) < 0 := by
      nlinarith [hterm_lt_spacing]
    calc
      |x - b| = (1 / (2 : ℝ) ^ 23) - term := by
        rw [hxb, abs_of_neg hneg]
        ring
      _ < term := hright
      _ = |x - a| := by rw [hxa, abs_of_pos hterm_pos]
  have hround :
      fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
    inverseSquareSingleThreeBeforePlateauAccumulator,
    inverseSquareSingleTwoBeforePlateauAccumulator, inverseSquareTerm, term, x, a, b, fmt, m]
    using hround

/-- One step earlier in the local §1.12.3 forward summation trace: adding
`4095^{-2}` to the binary32 accumulator two ulps below the displayed plateau is
strictly closer to the next binary32 value than to the current accumulator, so
nearest/even rounds to the pre-plateau accumulator. This does not derive that
the full forward loop reaches the two-before-plateau accumulator at `k = 4094`;
it closes the concrete `k = 4095` successor step once that accumulator is
available. -/
theorem inverseSquareSingleTwoBeforePlateau_add_4095_term_rounds_to_prePlateau :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        inverseSquareSingleTwoBeforePlateauAccumulator (inverseSquareTerm 4095) =
      inverseSquareSinglePrePlateauAccumulator := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let m : ℕ := 13796954
  let a : ℝ := fmt.normalizedValue false m 1
  let b : ℝ := fmt.normalizedValue false (m + 1) 1
  let term : ℝ := inverseSquareTerm 4095
  let x : ℝ := a + term
  have hm : fmt.normalizedMantissa m := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.mantissaInRange]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hb_sub : b - a = 1 / (2 : ℝ) ^ 23 := by
    norm_num [a, b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR,
      zpow_neg]
  have hterm_pos : 0 < term := by
    norm_num [term, inverseSquareTerm]
  have hterm_lt_spacing : term < 1 / (2 : ℝ) ^ 23 := by
    norm_num [term, inverseSquareTerm]
  have hhalf_lt_term : 1 / (2 : ℝ) ^ 24 < term := by
    norm_num [term, inverseSquareTerm]
  have hstrict : a < x ∧ x < b := by
    constructor
    · simp [x]
      exact hterm_pos
    · have : a + term < b := by
        nlinarith [hb_sub, hterm_lt_spacing]
      simpa [x] using this
  have hxrange : fmt.finiteNormalRange x := by
    have hxnonneg : 0 ≤ x := by
      have ha_pos : 0 < a := by
        norm_num [a, m, fmt, FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      positivity
    rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
    constructor
    · have ha_large : fmt.minNormalMagnitude ≤ a := by
        norm_num [a, m, fmt, FloatingPointFormat.minNormalMagnitude,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue,
          FloatingPointFormat.betaR,
          zpow_neg]
      have ha_le_x : a ≤ x := le_of_lt hstrict.1
      exact le_trans ha_large ha_le_x
    · have hx_lt : x < b := hstrict.2
      have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
        calc
          b = (13796955 : ℝ) / 8388608 := by
            norm_num [b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedValue,
              FloatingPointFormat.signValue,
              FloatingPointFormat.betaR,
              zpow_neg]
          _ ≤ 340282346638528859811704183484516925440 := by
            norm_num
          _ = fmt.maxFiniteMagnitude := by
            norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.betaR,
              zpow_neg]
            rfl
      exact le_trans (le_of_lt hx_lt) hb_le_max
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    have hxa : x - a = term := by
      simp [x]
    have hxb : x - b = term - (1 / (2 : ℝ) ^ 23) := by
      calc
        x - b = a + term - b := by simp [x]
        _ = term - (b - a) := by ring
        _ = term - (1 / (2 : ℝ) ^ 23) := by rw [hb_sub]
    have hspacing_twice : 1 / (2 : ℝ) ^ 23 = 2 * (1 / (2 : ℝ) ^ 24) := by
      norm_num
    have hright : (1 / (2 : ℝ) ^ 23) - term < term := by
      nlinarith
    have hneg : term - (1 / (2 : ℝ) ^ 23) < 0 := by
      nlinarith [hterm_lt_spacing]
    calc
      |x - b| = (1 / (2 : ℝ) ^ 23) - term := by
        rw [hxb, abs_of_neg hneg]
        ring
      _ < term := hright
      _ = |x - a| := by rw [hxa, abs_of_pos hterm_pos]
  have hround :
      fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
    inverseSquareSingleTwoBeforePlateauAccumulator,
    inverseSquareSinglePrePlateauAccumulator, inverseSquareTerm, term, x, a, b, fmt, m]
    using hround

/-- At the concrete §1.12.3 single-precision plateau accumulator, every
positive term no larger than `2^{-24}` rounds away under binary32 nearest/even
addition.  The equality case is the displayed midpoint tie; smaller positive
terms are strictly closer to the plateau value than to the next binary32 value. -/
theorem inverseSquareSinglePlateau_add_positive_term_le_two_pow_neg_24_rounds_to_self
    {t : ℝ}
    (htpos : 0 < t)
    (htle : t ≤ 1 / (2 : ℝ) ^ 24) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        inverseSquareSinglePlateauAccumulator t =
      inverseSquareSinglePlateauAccumulator := by
  by_cases ht_eq : t = 1 / (2 : ℝ) ^ 24
  · simpa [ht_eq, inverseSquareTerm_4096_eq_two_pow_neg_24] using
      inverseSquareSinglePlateau_add_4096_term_rounds_to_self
  · let fmt := FloatingPointFormat.ieeeSingleFormat
    let m : ℕ := 13796956
    let a : ℝ := fmt.normalizedValue false m 1
    let b : ℝ := fmt.normalizedValue false (m + 1) 1
    let x : ℝ := a + t
    have hlt : t < 1 / (2 : ℝ) ^ 24 := lt_of_le_of_ne htle ht_eq
    have hm : fmt.normalizedMantissa m := by
      norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    have hmnext : fmt.normalizedMantissa (m + 1) := by
      norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.mantissaInRange]
    have hadj : fmt.realOrderAdjacentNormalized a b :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨false, m, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
    have hb_sub : b - a = 1 / (2 : ℝ) ^ 23 := by
      norm_num [a, b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.betaR,
        zpow_neg]
    have hlt_spacing : t < 1 / (2 : ℝ) ^ 23 := by
      have hhalf : 1 / (2 : ℝ) ^ 24 < 1 / (2 : ℝ) ^ 23 := by
        norm_num
      exact lt_trans hlt hhalf
    have hstrict : a < x ∧ x < b := by
      constructor
      · simp [x]
        exact htpos
      · have : a + t < b := by
          nlinarith [hb_sub, hlt_spacing]
        simpa [x] using this
    have hxrange : fmt.finiteNormalRange x := by
      have hxnonneg : 0 ≤ x := by
        have ha_pos : 0 < a := by
          norm_num [a, m, fmt, FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue,
            FloatingPointFormat.signValue,
            FloatingPointFormat.betaR,
            zpow_neg]
        positivity
      rw [FloatingPointFormat.finiteNormalRange, abs_of_nonneg hxnonneg]
      constructor
      · have ha_large : fmt.minNormalMagnitude ≤ a := by
          norm_num [a, m, fmt, FloatingPointFormat.minNormalMagnitude,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.normalizedValue,
            FloatingPointFormat.signValue,
            FloatingPointFormat.betaR,
            zpow_neg]
        have ha_le_x : a ≤ x := le_of_lt hstrict.1
        exact le_trans ha_large ha_le_x
      · have hx_lt : x < b := hstrict.2
        have hb_le_max : b ≤ fmt.maxFiniteMagnitude := by
          calc
            b = (13796957 : ℝ) / 8388608 := by
              norm_num [b, m, fmt, FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue,
                FloatingPointFormat.betaR,
                zpow_neg]
            _ ≤ 340282346638528859811704183484516925440 := by
              norm_num
            _ = fmt.maxFiniteMagnitude := by
              norm_num [fmt, FloatingPointFormat.maxFiniteMagnitude,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.betaR,
                zpow_neg]
              rfl
        exact le_trans (le_of_lt hx_lt) hb_le_max
    have hpolicy :
        fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
      fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
    have hleftCloser : |x - a| < |x - b| := by
      have hxa : x - a = t := by
        simp [x]
      have hxb : x - b = t - (1 / (2 : ℝ) ^ 23) := by
        calc
          x - b = a + t - b := by simp [x]
          _ = t - (b - a) := by ring
          _ = t - (1 / (2 : ℝ) ^ 23) := by rw [hb_sub]
      have hspacing_twice : 1 / (2 : ℝ) ^ 23 = 2 * (1 / (2 : ℝ) ^ 24) := by
        norm_num
      have ht_left : t < (1 / (2 : ℝ) ^ 23) - t := by
        nlinarith
      have hneg : t - (1 / (2 : ℝ) ^ 23) < 0 := by
        nlinarith [hlt_spacing]
      calc
        |x - a| = t := by rw [hxa, abs_of_pos htpos]
        _ < (1 / (2 : ℝ) ^ 23) - t := ht_left
        _ = |x - b| := by
          rw [hxb, abs_of_neg hneg]
          ring
    have hround :
        fmt.finiteRoundToEven x = a :=
      fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy hadj hstrict hleftCloser
    simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
      inverseSquareSinglePlateauAccumulator, x, a, fmt, m] using hround

/-- Once Higham §1.12.3's concrete single-precision running sum has reached the
displayed plateau value, adding any later inverse-square term `1/k^2` with
`k >= 4096` leaves the accumulator unchanged.  This proves the local tail
stagnation mechanism; by itself it does not derive that the repository-model
loop first reaches this plateau at `k = 4096`. -/
theorem inverseSquareSinglePlateau_add_term_rounds_to_self_of_ge_4096
    {k : ℕ} (hk : 4096 ≤ k) :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
        inverseSquareSinglePlateauAccumulator (inverseSquareTerm k) =
      inverseSquareSinglePlateauAccumulator := by
  have hk_pos : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 4096) hk
  exact
    inverseSquareSinglePlateau_add_positive_term_le_two_pow_neg_24_rounds_to_self
      (inverseSquareTerm_pos_of_pos hk_pos)
      (inverseSquareTerm_le_two_pow_neg_24_of_ge hk)

/-- After the six-before-plateau accumulator is available at the end of the
`k = 4090` prefix, the tail starting at `k = 4091` reaches the plateau after
six rounded additions and remains there for any further inverse-square terms. -/
theorem inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_six_add_eq_plateau
    (r : ℕ) :
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSingleSixBeforePlateauAccumulator 4091 (6 + r) =
      inverseSquareSinglePlateauAccumulator := by
  induction r with
  | zero =>
      simpa using
        inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_six_eq_plateau
  | succ r ih =>
      rw [show 6 + (r + 1) = (6 + r) + 1 by omega]
      rw [inverseSquareSingleForwardAccumulatorFrom_succ, ih]
      have hge : 4096 ≤ 4091 + (6 + r) := by omega
      simpa [inverseSquareSingleForwardStep] using
        inverseSquareSinglePlateau_add_term_rounds_to_self_of_ge_4096 hge

/-- Combining the 1194-step range window with the six-step plateau entry:
if the early forward prefix has reached the pre-window binary32 accumulator at
the end of `k = 2896`, then the next 1200 rounded additions, starting at
`k = 2897`, enter the plateau and all later inverse-square terms leave it
unchanged. -/
theorem inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1200_add_eq_plateau
    (r : ℕ) :
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSinglePrePlateauWindowStartAccumulator 2897 (1200 + r) =
      inverseSquareSinglePlateauAccumulator := by
  calc
    inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSinglePrePlateauWindowStartAccumulator 2897 (1200 + r) =
      inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSinglePrePlateauWindowStartAccumulator 2897 (1194 + (6 + r)) := by
        congr 1
        omega
    _ =
      inverseSquareSingleForwardAccumulatorFrom
        (inverseSquareSingleForwardAccumulatorFrom
          inverseSquareSinglePrePlateauWindowStartAccumulator 2897 1194)
        (2897 + 1194) (6 + r) := by
        rw [inverseSquareSingleForwardAccumulatorFrom_add]
    _ =
      inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSingleSixBeforePlateauAccumulator 4091 (6 + r) := by
        rw [inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1194_eq_sixBeforePlateau]
    _ = inverseSquareSinglePlateauAccumulator :=
        inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_six_add_eq_plateau r

/-- Conditional full-loop plateau theorem for Higham §1.12.3's actual
left-to-right accumulator.  Once the remaining early-prefix trace proves that
the `k = 1, ..., 2896` rounded loop lands at the pre-window accumulator, the
existing non-enumerative window proof gives the plateau after `k = 4096` and
all later terms. -/
theorem inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_2896_eq_prePlateauWindowStart
    (hprefix :
      inverseSquareSingleForwardAccumulator 2896 =
        inverseSquareSinglePrePlateauWindowStartAccumulator)
    (r : ℕ) :
    inverseSquareSingleForwardAccumulator (4096 + r) =
      inverseSquareSinglePlateauAccumulator := by
  calc
    inverseSquareSingleForwardAccumulator (4096 + r) =
      inverseSquareSingleForwardAccumulator (2896 + (1200 + r)) := by
        congr 1
        omega
    _ =
      inverseSquareSingleForwardAccumulatorFrom
        (inverseSquareSingleForwardAccumulator 2896) (1 + 2896) (1200 + r) := by
        rw [inverseSquareSingleForwardAccumulator_add]
    _ =
      inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSinglePrePlateauWindowStartAccumulator 2897 (1200 + r) := by
        rw [hprefix]
    _ = inverseSquareSinglePlateauAccumulator :=
      inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1200_add_eq_plateau r

/-- Conditional no-plateau theorem for the already-closed part of the actual
left-to-right accumulator.  Assuming the early prefix reaches the pre-window
accumulator after `k = 2896`, every later prefix through `k = 4095` is still
strictly below the plateau; the next theorem shows `k = 4096` reaches it. -/
theorem inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_2896_eq_prePlateauWindowStart
    (hprefix :
      inverseSquareSingleForwardAccumulator 2896 =
        inverseSquareSinglePrePlateauWindowStartAccumulator)
    {r : ℕ} (hr : r < 1200) :
    inverseSquareSingleForwardAccumulator (2896 + r) <
      inverseSquareSinglePlateauAccumulator := by
  calc
    inverseSquareSingleForwardAccumulator (2896 + r) =
      inverseSquareSingleForwardAccumulatorFrom
        (inverseSquareSingleForwardAccumulator 2896) (1 + 2896) r := by
        rw [inverseSquareSingleForwardAccumulator_add]
    _ =
      inverseSquareSingleForwardAccumulatorFrom
        inverseSquareSinglePrePlateauWindowStartAccumulator 2897 r := by
        rw [hprefix]
    _ < inverseSquareSinglePlateauAccumulator :=
      inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_lt_plateau_of_lt_1200 hr

/-- Local-increment-rule form of the actual first-stagnation prefix: if the
uniform early-prefix rounding rule is available, then the actual accumulator
is still below the plateau through the `k = 4095` prefix. -/
theorem inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_early_mantissa_increment_rule
    (hrule : inverseSquareSingleEarlyMantissaIncrementRule)
    {r : ℕ} (hr : r < 1200) :
    inverseSquareSingleForwardAccumulator (2896 + r) <
      inverseSquareSinglePlateauAccumulator :=
  inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_2896_eq_prePlateauWindowStart
    (inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart_of_early_mantissa_increment_rule
      hrule)
    hr

/-- Actual first-stagnation prefix theorem: the left-to-right single-precision
accumulator is still below the plateau through every prefix ending before the
`k = 4096` term. -/
theorem inverseSquareSingleForwardAccumulator_2896_add_lt_plateau
    {r : ℕ} (hr : r < 1200) :
    inverseSquareSingleForwardAccumulator (2896 + r) <
      inverseSquareSinglePlateauAccumulator :=
  inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_early_mantissa_increment_rule
    inverseSquareSingleEarlyMantissaIncrementRule_closed hr

/-- Local-increment-rule form of the actual plateau theorem: if the uniform
early-prefix rounding rule is available for terms `2, ..., 2896`, then the
actual left-to-right accumulator reaches the plateau at the `k = 4096` prefix
and stays there for every later term. -/
theorem inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_early_mantissa_increment_rule
    (hrule : inverseSquareSingleEarlyMantissaIncrementRule)
    (r : ℕ) :
    inverseSquareSingleForwardAccumulator (4096 + r) =
      inverseSquareSinglePlateauAccumulator :=
  inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_2896_eq_prePlateauWindowStart
    (inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart_of_early_mantissa_increment_rule
      hrule)
    r

/-- Actual forward-summation plateau theorem for Higham §1.12.3: the
left-to-right single-precision accumulator reaches the displayed plateau at the
`k = 4096` prefix and remains there for every later term. -/
theorem inverseSquareSingleForwardAccumulator_4096_add_eq_plateau
    (r : ℕ) :
    inverseSquareSingleForwardAccumulator (4096 + r) =
      inverseSquareSinglePlateauAccumulator :=
  inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_early_mantissa_increment_rule
    inverseSquareSingleEarlyMantissaIncrementRule_closed r

end NumStability
