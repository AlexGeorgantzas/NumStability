-- Analysis/ConditionEstimatorLowerBound.lean
--
-- The Hager/Higham LAPACK-style 1-norm condition-number estimator is a genuine
-- LOWER BOUND on the true 1-norm condition number.
--
-- Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002):
--   * §14.3 (pp. 292-295), Algorithms 14.3 / 14.4: the 1-norm power method and
--     its LAPACK realization, producing γ ≤ ‖B‖₁ for the sampled matrix B.
--   * §15.1 (pp. 305-307), eq. (15.1): the (1-norm) condition number
--         κ₁(A) = ‖A‖₁ · ‖A⁻¹‖₁,
--     estimated in practice by running Algorithm 14.4 on A⁻¹ (accessed through
--     linear solves) and multiplying the returned estimate by ‖A‖₁.
--
-- This file is IMPORT-ONLY. It never edits the Codex-owned estimator file
-- `Algorithms/CondEstimation.lean`; it reuses its public lower-bound lemmas
--   * `oneNormPowerMethod_lower_bound : (oneNormPowerMethod hn B fuel).γ ≤ ‖B‖₁`
--   * `lapackNormEstimator_lower_bound : lapackNormEstimator hn B ≤ ‖B‖₁`
-- and lifts them, unconditionally, to a lower bound on κ₁(A).
--
-- Honest statement strength.  The estimator only ever samples a *supplied*
-- matrix `B`.  What is unconditional and general is:
--     ‖A‖₁ · (estimator B) ≤ ‖A‖₁ · ‖B‖₁.
-- When `B` is a genuine (right) inverse of `A` — the case the algorithm targets,
-- witnessed here by the hypothesis `A * B = 1` — this is exactly the lower bound
-- on κ₁(A).  No spectral, separation, or convergence hypotheses are used; the
-- estimator can *under*-estimate κ₁(A) (that is the whole point of the word
-- "lower bound"), and nothing here silently upgrades it to an equality.

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Positivity
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.CondEstimation

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §15.1  The true 1-norm condition number κ₁(A) = ‖A‖₁‖A⁻¹‖₁
-- ============================================================

/-- **1-norm condition number** (Higham §15.1, eq. (15.1), p. 306).

    For an invertible `A` with inverse `B` (so `A * B = 1`), the 1-norm
    condition number is `κ₁(A) = ‖A‖₁ · ‖A⁻¹‖₁`.  Here the inverse is passed
    explicitly as `B`; the companion lemmas below identify `B` with Mathlib's
    canonical `A⁻¹` whenever `A * B = 1`.  We keep `B` as a separate argument so
    that the estimator lower bound holds for *whatever* matrix the algorithm
    actually samples (see `condOneNumber_ge_scaled_estimator`). -/
noncomputable def condOneNumber {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : ℝ :=
  oneNorm A * oneNorm B

/-- The 1-norm condition number is nonnegative (Higham §15.1). -/
lemma condOneNumber_nonneg {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    0 ≤ condOneNumber A B :=
  mul_nonneg (oneNorm_nonneg A) (oneNorm_nonneg B)

-- ============================================================
-- §14.3 → §15.1  Scaling a ‖·‖₁ lower bound to a κ₁ lower bound
-- ============================================================

/-- **Monotone scaling of a 1-norm lower bound** (Higham §15.1, combined with
    §14.3).

    If a scalar estimate `est` under-estimates `‖B‖₁`, then multiplying by the
    nonnegative factor `‖A‖₁` under-estimates `‖A‖₁ · ‖B‖₁ = κ₁(A)` (when `B` is
    the inverse of `A`).  This is the elementary but load-bearing step that
    turns the estimator's ‖·‖₁ guarantee into a condition-number guarantee. -/
theorem scaled_estimate_le_condOneNumber {n : ℕ}
    (A B : Fin n → Fin n → ℝ) {est : ℝ} (hest : est ≤ oneNorm B) :
    oneNorm A * est ≤ condOneNumber A B := by
  unfold condOneNumber
  exact mul_le_mul_of_nonneg_left hest (oneNorm_nonneg A)

/-- **Hager/Higham 1-norm condition estimator is a lower bound on κ₁**
    (Higham §14.3, Algorithm 14.4, applied per §15.1).

    Running the LAPACK 1-norm estimator (`lapackNormEstimator`) on the supplied
    matrix `B` and scaling by `‖A‖₁` never exceeds `‖A‖₁ · ‖B‖₁`.  When `B` is
    the inverse of `A`, the right-hand side is the true condition number
    `κ₁(A)`, so the scaled estimator is a genuine lower bound on `κ₁(A)`.

    Unconditional: no eigenvalue-separation, positive-definiteness, or
    convergence hypothesis is required. -/
theorem condOneNumber_ge_scaled_estimator {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ) :
    oneNorm A * lapackNormEstimator hn B ≤ condOneNumber A B :=
  scaled_estimate_le_condOneNumber A B (lapackNormEstimator_lower_bound hn B)

/-- **Power-method core is a lower bound on κ₁** (Higham §14.3, Algorithm 14.3,
    applied per §15.1).

    The same conclusion for the bare 1-norm power method at any fuel budget:
    `‖A‖₁ · (oneNormPowerMethod hn B fuel).γ ≤ ‖A‖₁ · ‖B‖₁ = κ₁(A)` when `B` is
    the inverse of `A`. -/
theorem condOneNumber_ge_scaled_powerMethod {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ) (fuel : ℕ) :
    oneNorm A * (oneNormPowerMethod hn B fuel).γ ≤ condOneNumber A B :=
  scaled_estimate_le_condOneNumber A B (oneNormPowerMethod_lower_bound hn B fuel)

-- ============================================================
-- §15.1  Identifying the sampled matrix with the genuine inverse A⁻¹
-- ============================================================

/-- **Estimator lower bound at the genuine inverse** (Higham §15.1, eq. (15.1)).

    If `B` is an actual right inverse of `A` (`A * B = 1`, using the matrix
    product), then Mathlib's canonical inverse satisfies `A⁻¹ = B`, so
    `condOneNumber A B = ‖A‖₁ · ‖A⁻¹‖₁ = κ₁(A)` is the textbook condition
    number, and the scaled LAPACK estimate is a genuine lower bound on it.

    The hypothesis is stated with `Matrix.of` so that `A * B` is the honest
    matrix product; `inv_eq_right_inv` then pins `A⁻¹` to `B`. -/
theorem condOneNumber_eq_kappaOne_of_rightInverse {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (h : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) *
         (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) = 1) :
    condOneNumber A B =
      oneNorm A *
        oneNorm (fun i j => (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) := by
  have hinv : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ = Matrix.of B :=
    Matrix.inv_eq_right_inv h
  unfold condOneNumber
  congr 1
  -- `oneNorm B = oneNorm (entries of A⁻¹)`, since `A⁻¹ = of B`.
  simp only [hinv, Matrix.of_apply]

/-- **The LAPACK estimator under-estimates the textbook κ₁(A)** (Higham §14.3 +
    §15.1, eq. (15.1)).

    Combining `condOneNumber_ge_scaled_estimator` with
    `condOneNumber_eq_kappaOne_of_rightInverse`: for an invertible `A` with a
    supplied inverse `B` (`A * B = 1`), the scaled LAPACK 1-norm estimate is a
    genuine lower bound on the true 1-norm condition number
    `‖A‖₁ · ‖A⁻¹‖₁`.  This is the headline result. -/
theorem lapack_condEstimate_le_kappaOne {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ)
    (h : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) *
         (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) = 1) :
    oneNorm A * lapackNormEstimator hn B ≤
      oneNorm A *
        oneNorm (fun i j => (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) := by
  have hle := condOneNumber_ge_scaled_estimator hn A B
  rwa [condOneNumber_eq_kappaOne_of_rightInverse A B h] at hle

end NumStability
