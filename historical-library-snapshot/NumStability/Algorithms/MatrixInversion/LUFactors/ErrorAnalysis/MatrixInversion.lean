import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms MatrixInversion LUFactors ErrorAnalysis MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Method A column-wise backward error** (Higham eq. 14.15).

    Method A computes X̂ ≈ A⁻¹ by solving Ax̂ⱼ = eⱼ for j = 1:n via LU.
    From Theorem 9.4, each column satisfies (A + ΔAⱼ)x̂ⱼ = eⱼ
    with |ΔAⱼ| ≤ (3γₙ + γₙ²)|L̂||Û|. -/
theorem methodA_column_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      let b_j : Fin n → ℝ := fun i => if i = j then 1 else 0
      let y_hat := fl_forwardSub fp n L_hat b_j
      let x_hat_j := fl_backSub fp n U_hat y_hat
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * x_hat_j k = b_j i := by
  intro j b_j y_hat x_hat_j
  exact lu_solve_backward_error fp n A L_hat U_hat b_j hL_diag hU_diag hLU hn

/-- Method A column-wise backward error specialized to the named computed
inverse matrix `methodAComputedInverse`. -/
theorem methodA_column_backward_error_computed_inverse (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n,
          (A i k + ΔA i k) *
            methodAComputedInverse fp n L_hat U_hat k j =
          if i = j then 1 else 0 := by
  intro j
  simpa [methodAComputedInverse] using
    methodA_column_backward_error n fp A L_hat U_hat
      hL_diag hU_diag hLU hn j

/-- Method A column-wise backward error with an exposed LU factorization
coefficient.  The LU factorization is certified at level `epsLU`, while the
forward and back triangular solves are still charged at `gamma fp n`. -/
theorem methodA_column_backward_error_factor_bound (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {epsLU : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      let b_j : Fin n → ℝ := fun i => if i = j then 1 else 0
      let y_hat := fl_forwardSub fp n L_hat b_j
      let x_hat_j := fl_backSub fp n U_hat y_hat
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤
          (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * x_hat_j k = b_j i := by
  intro j b_j y_hat x_hat_j
  exact
    lu_solve_backward_error_factor_gamma fp n A L_hat U_hat b_j
      hepsLU hL_diag hU_diag hLU hn

/-- Coefficient-exposed Method A column-wise backward error specialized to the
named computed inverse matrix `methodAComputedInverse`. -/
theorem methodA_column_backward_error_computed_inverse_factor_bound
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {epsLU : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤
          (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n,
          (A i k + ΔA i k) *
            methodAComputedInverse fp n L_hat U_hat k j =
          if i = j then 1 else 0 := by
  intro j
  simpa [methodAComputedInverse] using
    methodA_column_backward_error_factor_bound n fp A L_hat U_hat
      hepsLU hL_diag hU_diag hLU hn j

/-- **Method A right residual** (Higham eq. 14.16).

    |AX̂ − I| ≤ c'ₙu|L̂||Û||X̂|.

    Each column has (A + ΔAⱼ)x̂ⱼ = eⱼ, so Ax̂ⱼ = eⱼ − ΔAⱼx̂ⱼ,
    hence |Ax̂ⱼ − eⱼ| = |ΔAⱼx̂ⱼ| ≤ (3γₙ+γₙ²)(|L̂||Û|)|x̂ⱼ|. -/
theorem methodA_right_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_hat : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp n)
    -- Each column j has backward error: (A+ΔAⱼ)x̂ⱼ = eⱼ with |ΔAⱼ| ≤ c|L̂||Û|
    (hCol : ∀ j : Fin n, ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i k, |ΔA i k| ≤ (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
      ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
          |X_hat k j| := by
  intro i j
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ := hCol j
  have hAX : ∑ k : Fin n, A i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔA i k * X_hat k j) := by
    have h := hΔA_eq i
    have hsplit : ∑ k : Fin n, A i k * X_hat k j +
        ∑ k : Fin n, ΔA i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hAX, abs_neg]
  calc |∑ k : Fin n, ΔA i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔA i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔA i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, ((3 * gamma fp n + gamma fp n ^ 2) *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔA_bound i k) (abs_nonneg _)
    _ = (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
            |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- Method A right residual with an externally supplied componentwise column
backward-error coefficient `c`. -/
theorem methodA_right_residual_of_column_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_hat : Fin n → Fin n → ℝ)
    (c : ℝ)
    (hCol : ∀ j : Fin n, ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i k, |ΔA i k| ≤ c *
        ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
      ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      c * ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
        |X_hat k j| := by
  intro i j
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ := hCol j
  have hAX : ∑ k : Fin n, A i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔA i k * X_hat k j) := by
    have h := hΔA_eq i
    have hsplit : ∑ k : Fin n, A i k * X_hat k j +
        ∑ k : Fin n, ΔA i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hAX, abs_neg]
  calc |∑ k : Fin n, ΔA i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔA i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔA i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (c *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔA_bound i k) (abs_nonneg _)
    _ = c * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
            |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Method A forward error** (Higham eq. 14.17).

    |X̂ − A⁻¹| ≤ c'ₙu|A⁻¹||L̂||Û||X̂|. -/
theorem methodA_forward_error (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat X_hat : Fin n → Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (_hn : gammaValid fp n)
    -- Right residual hypothesis
    (hRes : ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
          |X_hat k j|) :
    ∀ i j : Fin n,
      |X_hat i j - A_inv i j| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
            |X_hat k₂ j|) := by
  intro i j
  -- Define E_{k₁j} = (AX̂)_{k₁j} − δ_{k₁j}, the residual
  -- From AX̂ = I + E, multiply by A⁻¹: X̂ = A⁻¹ + A⁻¹E
  -- So X̂_{ij} − A⁻¹_{ij} = (A⁻¹E)_{ij}
  let c := 3 * gamma fp n + gamma fp n ^ 2
  have hDiff : X_hat i j - A_inv i j =
      ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) := by
    have hRHS_expand : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) -
        ∑ k₁ : Fin n, A_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k₁ _; ring
    rw [hRHS_expand]
    have hSecond : ∑ k₁ : Fin n, A_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) = A_inv i j := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hFirst : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) = X_hat i j := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hInvA : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂) = if i = k₂ then 1 else 0 :=
        fun k₂ => hInv i k₂
      simp_rw [hInvA]
      simp [Finset.mem_univ]
    rw [hFirst, hSecond]
  rw [hDiff]
  calc |∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)|
      ≤ ∑ k₁ : Fin n, |A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |A_inv i k₁| *
        |∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |A_inv i k₁| *
        (c * ∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        exact mul_le_mul_of_nonneg_left (hRes k₁ j) (abs_nonneg _)
    _ = c * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _; ring

/-- Method A forward error with an externally supplied residual coefficient
`c`. -/
theorem methodA_forward_error_of_residual_bound (n : ℕ)
    (A A_inv L_hat U_hat X_hat : Fin n → Fin n → ℝ)
    (c : ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hRes : ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      c * ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
        |X_hat k j|) :
    ∀ i j : Fin n,
      |X_hat i j - A_inv i j| ≤
      c * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
  intro i j
  have hDiff : X_hat i j - A_inv i j =
      ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) := by
    have hRHS_expand : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) -
        ∑ k₁ : Fin n, A_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k₁ _; ring
    rw [hRHS_expand]
    have hSecond : ∑ k₁ : Fin n, A_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) = A_inv i j := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hFirst : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) = X_hat i j := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hInvA : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂) = if i = k₂ then 1 else 0 :=
        fun k₂ => hInv i k₂
      simp_rw [hInvA]
      simp [Finset.mem_univ]
    rw [hFirst, hSecond]
  rw [hDiff]
  calc |∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)|
      ≤ ∑ k₁ : Fin n, |A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |A_inv i k₁| *
        |∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |A_inv i k₁| *
        (c * ∑ k₂ : Fin n,
          (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
            |X_hat k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        exact mul_le_mul_of_nonneg_left (hRes k₁ j) (abs_nonneg _)
    _ = c * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _; ring

/-- Method A computed inverse entrywise forward-error certificate for the
repository nonsingular inverse, with a visible scalar budget `eta`. -/
theorem methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_budget
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {eta : ℝ}
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hBudget :
      ∀ i j : Fin n,
        (3 * gamma fp n + gamma fp n ^ 2) *
            ∑ k₁ : Fin n,
              |nonsingInv n A i k₁| *
                (∑ k₂ : Fin n,
                  (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp n L_hat U_hat k₂ j|) ≤ eta) :
    ∀ i j : Fin n,
      |nonsingInv n A i j -
          methodAComputedInverse fp n L_hat U_hat i j| ≤ eta := by
  intro i j
  have hInv : IsInverse n A (nonsingInv n A) :=
    isInverse_nonsingInv_of_det_ne_zero n A hdet
  have hCol :=
    methodA_column_backward_error_computed_inverse n fp A L_hat U_hat
      hL_diag hU_diag hLU hn
  have hRes :=
    methodA_right_residual n fp A L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) hn hCol
  have hFwd :=
    methodA_forward_error n fp A (nonsingInv n A) L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) hInv.1 hn hRes i j
  rw [abs_sub_comm]
  exact le_trans hFwd (hBudget i j)

/-- Method A computed inverse entrywise forward-error certificate with an
exposed LU factorization coefficient `epsLU`.  This is the implementation-facing
variant used when the LU factors are certified for a computed input matrix and
that input error has already been transferred into the `LUBackwardError`
coefficient. -/
theorem methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_factor_budget
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {epsLU eta : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n)
    (hBudget :
      ∀ i j : Fin n,
        (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ k₁ : Fin n,
              |nonsingInv n A i k₁| *
                (∑ k₂ : Fin n,
                  (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp n L_hat U_hat k₂ j|) ≤ eta) :
    ∀ i j : Fin n,
      |nonsingInv n A i j -
          methodAComputedInverse fp n L_hat U_hat i j| ≤ eta := by
  intro i j
  have hInv : IsInverse n A (nonsingInv n A) :=
    isInverse_nonsingInv_of_det_ne_zero n A hdet
  have hCol :=
    methodA_column_backward_error_computed_inverse_factor_bound n fp A L_hat U_hat
      hepsLU hL_diag hU_diag hLU hn
  let c := epsLU + 2 * gamma fp n + gamma fp n ^ 2
  have hRes :=
    methodA_right_residual_of_column_bound n A L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) c hCol
  have hFwd :=
    methodA_forward_error_of_residual_bound n A (nonsingInv n A) L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) c hInv.1 hRes i j
  rw [abs_sub_comm]
  exact le_trans hFwd (hBudget i j)

/-- **Method B left residual** (Higham eq. 14.18).

    Method B: compute X_U ≈ U⁻¹ (by an analogue of Method 2 or 2C for upper
    triangular matrices), then solve for X in XL̂ = X_U by back substitution
    from the right.

    The left residual satisfies:
      |X̂A − I| ≤ c'ₙu|X̂||L̂||Û|.

    Note: eq. 14.18 is the left residual analogue of eq. 14.16.
    The LINPACK manual incorrectly states this as a right residual bound. -/
theorem methodB_left_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    -- X_U satisfies right residual for U⁻¹: |X_U · Û − I| ≤ γₙ|X_U||Û|
    (hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    -- X̂ is computed by solving X̂L̂ = X_U from the right (back sub rows):
    -- |X̂L̂ − X_U| ≤ γₙ|X̂||L̂| (this is the Δ(X̂, L̂) term)
    (hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L_hat k j - X_U i j| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L_hat k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k₁ : Fin n, |X_hat i k₁| *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) := by
  intro i j
  let γ := gamma fp n
  -- Step 1: Decompose A = L̂Û − (L̂Û − A)
  -- X̂A = X̂L̂Û − X̂(L̂Û − A)
  -- Step 2: X̂L̂Û − I = (X̂L̂ − X_U)Û + (X_UÛ − I) = E₁Û + E₂
  -- where E₁ = X̂L̂ − X_U, E₂ = X_UÛ − I
  -- Bound |X_U| ≤ (1+γ)|X̂||L̂| from E₁ bound
  -- Total: |X̂A − I| ≤ (3γ + γ²)|X̂||L̂||Û|
  -- Abbreviate the componentwise product bound
  let B := fun i j => ∑ k₁ : Fin n, |X_hat i k₁| *
    (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)
  -- The LU backward error gives |L̂Û − A| ≤ γ|L̂||Û|
  have hLUerr := hLU.backward_bound
  -- Bound: X̂(A − L̂Û) contribution
  have hLU_contrib : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k *
        (A k j - ∑ l : Fin n, L_hat k l * U_hat l j)| ≤ γ * B i j := by
    intro i' j'
    calc |∑ k : Fin n, X_hat i' k *
          (A k j' - ∑ l : Fin n, L_hat k l * U_hat l j')|
        ≤ ∑ k : Fin n, |X_hat i' k| *
          |A k j' - ∑ l : Fin n, L_hat k l * U_hat l j'| := by
          calc _ ≤ ∑ k, |X_hat i' k * (A k j' - ∑ l, L_hat k l * U_hat l j')| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, |X_hat i' k| *
            (γ * ∑ l : Fin n, |L_hat k l| * |U_hat l j'|) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have h := hLUerr k j'
          rwa [abs_sub_comm] at h
      _ = γ * B i' j' := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
  -- Bound: E₁Û contribution where E₁ = X̂L̂ − X_U
  have hE1U_contrib : ∀ i j : Fin n,
      |∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) *
        U_hat k j| ≤ γ * B i j := by
    intro i' j'
    calc |∑ k : Fin n, (∑ l : Fin n, X_hat i' l * L_hat l k - X_U i' k) *
          U_hat k j'|
        ≤ ∑ k : Fin n, |∑ l : Fin n, X_hat i' l * L_hat l k - X_U i' k| *
          |U_hat k j'| := by
          calc _ ≤ ∑ k, |(∑ l, X_hat i' l * L_hat l k - X_U i' k) * U_hat k j'| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, (γ * ∑ l : Fin n, |X_hat i' l| * |L_hat l k|) *
          |U_hat k j'| := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hXL_res i' k) (abs_nonneg _)
      _ = γ * B i' j' := by
          have hfact : ∀ k : Fin n,
              (γ * ∑ l, |X_hat i' l| * |L_hat l k|) * |U_hat k j'| =
              γ * ((∑ l, |X_hat i' l| * |L_hat l k|) * |U_hat k j'|) :=
            fun _ => by ring
          simp_rw [hfact, ← Finset.mul_sum, Finset.sum_mul]
          congr 1; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro l _
          simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  -- Bound: E₂ contribution where E₂ = X_UÛ − I, with |X_U| ≤ (1+γ)|X̂||L̂|
  -- First bound |X_U|
  have hXU_bound : ∀ i' k : Fin n,
      |X_U i' k| ≤ (1 + γ) * ∑ l : Fin n, |X_hat i' l| * |L_hat l k| := by
    intro i' k
    have hXL_abs : |∑ l : Fin n, X_hat i' l * L_hat l k| ≤
        ∑ l : Fin n, |X_hat i' l| * |L_hat l k| := by
      calc _ ≤ ∑ l, |X_hat i' l * L_hat l k| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by apply Finset.sum_congr rfl; intro l _; exact abs_mul _ _
    have hE1 : |∑ l : Fin n, X_hat i' l * L_hat l k - X_U i' k| ≤
        γ * ∑ l : Fin n, |X_hat i' l| * |L_hat l k| := hXL_res i' k
    have key : |X_U i' k| ≤ |∑ l, X_hat i' l * L_hat l k| +
        |∑ l, X_hat i' l * L_hat l k - X_U i' k| := by
      have h := abs_add_le (X_U i' k - ∑ l, X_hat i' l * L_hat l k)
        (∑ l, X_hat i' l * L_hat l k)
      rw [sub_add_cancel] at h
      rw [abs_sub_comm] at h; linarith
    linarith
  -- Bound E₂ contribution: |E₂|_ij ≤ γ(1+γ)|X̂||L̂||Û|
  have hE2_contrib : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j -
        if i = j then (1 : ℝ) else 0| ≤
      γ * (1 + γ) * B i j := by
    intro i' j'
    calc |∑ k : Fin n, X_U i' k * U_hat k j' -
          if i' = j' then (1 : ℝ) else 0|
        ≤ γ * ∑ k : Fin n, |X_U i' k| * |U_hat k j'| := hXU_res i' j'
      _ ≤ γ * ∑ k : Fin n, ((1 + γ) * ∑ l : Fin n, |X_hat i' l| * |L_hat l k|) *
            |U_hat k j'| := by
          apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn)
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hXU_bound i' k) (abs_nonneg _)
      _ = γ * (1 + γ) * B i' j' := by
          rw [show γ * ∑ k : Fin n,
            ((1 + γ) * ∑ l : Fin n, |X_hat i' l| * |L_hat l k|) * |U_hat k j'| =
            γ * (1 + γ) * ∑ k : Fin n,
              (∑ l : Fin n, |X_hat i' l| * |L_hat l k|) * |U_hat k j'| from by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring]
          congr 1
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro l _
          simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  -- Fubini: ∑_k(∑_l X̂L̂)Û = ∑_k X̂(∑_l L̂Û)
  have hFub : ∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k) * U_hat k j =
      ∑ k : Fin n, X_hat i k * ∑ l : Fin n, L_hat k l * U_hat l j := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _; ring
  -- Algebraic decomposition: target = E₂ + E₁Û + X̂(A−L̂Û)
  have hDecomp : ∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0) =
      (∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)) +
      (∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j) +
      (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j)) := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.sum_sub_distrib]
    linarith [hFub]
  rw [hDecomp]
  have h1 := hE2_contrib i j
  have h2 := hE1U_contrib i j
  have h3 := hLU_contrib i j
  calc |(∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)) +
        (∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j) +
        (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j))|
      ≤ |∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)| +
        |(∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j) +
         (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j))| :=
      by rw [add_assoc]; exact abs_add_le _ _
    _ ≤ |∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)| +
        |∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j| +
        |∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j)| := by
      have := abs_add_le (∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j)
        (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j))
      linarith
    _ ≤ γ * (1 + γ) * B i j + γ * B i j + γ * B i j := by linarith
    _ = (3 * γ + γ ^ 2) * B i j := by ring

/-- **Abstract Method C mixed residual interface** (Higham eq. 14.19).

    Method C solves UX̂L = I, computing X̂ a partial row and column at a time.
    The "mixed" residual satisfies:
      |ÛX̂L̂ − I| ≤ cₙu|Û||X̂||L̂|.

    From this, bounds on both the left and right residuals (weaker than A/B)
    can be obtained by multiplying by |U⁻¹| or |L⁻¹|.

    The hypothesis `hMixed` is the local Method C error analysis; later
    theorems in this file derive forward-error consequences from it. -/
theorem methodC_mixed_residual (n : ℕ) (fp : FPModel)
    (U_hat L_hat X_hat : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp n)
    -- Hypothesis: X̂ is computed by Method C with the given error structure
    (hMixed : ∀ i j : Fin n,
      |∑ k₁ : Fin n, U_hat i k₁ *
        (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ j) -
          if i = j then 1 else 0| ≤
      gamma fp n * ∑ k₁ : Fin n, |U_hat i k₁| *
        (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k₁ : Fin n, U_hat i k₁ *
        (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ j) -
          if i = j then 1 else 0| ≤
      gamma fp n * ∑ k₁ : Fin n, |U_hat i k₁| *
        (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ j|) :=
  hMixed

/-- **Method C forward error relative to LU-inverse** (from eq. 14.19).

    From the mixed residual ÛX̂L̂ = I + E, multiplying by Û⁻¹ on the left
    and L̂⁻¹ on the right gives X̂ = Û⁻¹L̂⁻¹ + Û⁻¹EL̂⁻¹.
    The forward error relative to the LU-inverse satisfies:
      |X̂ − Û⁻¹L̂⁻¹| ≤ cₙu|Û⁻¹| · |Û||X̂||L̂| · |L̂⁻¹|. -/
theorem methodC_forward_error (n : ℕ) (fp : FPModel)
    (U_hat L_hat X_hat : Fin n → Fin n → ℝ)
    (U_inv L_inv : Fin n → Fin n → ℝ)
    (hUinv : IsLeftInverse n U_hat U_inv)
    (hLinv : IsRightInverse n L_hat L_inv)
    (_hn : gammaValid fp n)
    (hMixed : ∀ i j : Fin n,
      |∑ k₁ : Fin n, U_hat i k₁ *
        (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ j) -
          if i = j then 1 else 0| ≤
      gamma fp n * ∑ k₁ : Fin n, |U_hat i k₁| *
        (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ j|)) :
    ∀ i j : Fin n,
      |X_hat i j - matMul n U_inv L_inv i j| ≤
      gamma fp n *
        ∑ a : Fin n, |U_inv i a| *
          (∑ b : Fin n, (∑ k₁ : Fin n, |U_hat a k₁| *
            (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) *
              |L_inv b j|) := by
  intro i j
  let γ := gamma fp n
  -- Define E(a,b) = (ÛX̂L̂)_{ab} − δ_{ab}
  let E : Fin n → Fin n → ℝ := fun a b =>
    ∑ k₁ : Fin n, U_hat a k₁ * (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) -
      if a = b then 1 else 0
  -- Step 1: Apply L̂·L_inv = I to simplify ∑_b (∑_k₂ X̂·L̂)·L_inv = X̂
  have hLinv_app : ∀ k₁ : Fin n,
      ∑ b : Fin n, (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) * L_inv b j =
      X_hat k₁ j := by
    intro k₁
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [show ∀ (k₂ b : Fin n), X_hat k₁ k₂ * L_hat k₂ b * L_inv b j =
      X_hat k₁ k₂ * (L_hat k₂ b * L_inv b j) from fun _ _ => by ring]
    simp_rw [← Finset.mul_sum, hLinv _ j]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Step 2: Apply U_inv·Û = I to simplify ∑_a U_inv·(∑_k₁ Û·X̂) = X̂
  have hUinv_app :
      ∑ a : Fin n, U_inv i a * (∑ k₁ : Fin n, U_hat a k₁ * X_hat k₁ j) =
      X_hat i j := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hUinv i]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 3: Simplify ∑_b E(a,b)·L_inv(b,j) = ∑_k₁ Û(a,k₁)·X̂(k₁,j) − L_inv(a,j)
  have hEL : ∀ a : Fin n,
      ∑ b : Fin n, E a b * L_inv b j =
      ∑ k₁ : Fin n, U_hat a k₁ * X_hat k₁ j - L_inv a j := by
    intro a; simp only [E]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    · simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k₁ _
      simp_rw [show ∀ b : Fin n,
          U_hat a k₁ * (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) * L_inv b j =
          U_hat a k₁ * ((∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) * L_inv b j)
        from fun _ => by ring]
      rw [← Finset.mul_sum]
      congr 1; exact hLinv_app k₁
    · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 4: Algebraic identity ∑_a U_inv·(∑_b E·L_inv) = X̂ − U_inv·L_inv
  have hIdentity : ∑ a : Fin n, U_inv i a * (∑ b : Fin n, E a b * L_inv b j) =
      X_hat i j - matMul n U_inv L_inv i j := by
    simp_rw [hEL, mul_sub, Finset.sum_sub_distrib]
    unfold matMul; linarith [hUinv_app]
  -- Step 5: Bound |U_inv · E · L_inv| ≤ γ · |U_inv| · |E| · |L_inv|
  rw [show X_hat i j - matMul n U_inv L_inv i j =
    ∑ a : Fin n, U_inv i a * (∑ b : Fin n, E a b * L_inv b j) from hIdentity.symm]
  calc |∑ a : Fin n, U_inv i a * (∑ b : Fin n, E a b * L_inv b j)|
      ≤ ∑ a : Fin n, |U_inv i a| * |∑ b : Fin n, E a b * L_inv b j| := by
        calc _ ≤ ∑ a, |U_inv i a * (∑ b, E a b * L_inv b j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro a _; exact abs_mul _ _
    _ ≤ ∑ a : Fin n, |U_inv i a| *
        (∑ b : Fin n, |E a b| * |L_inv b j|) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ ∑ b, |E a b * L_inv b j| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro b _; exact abs_mul _ _
    _ ≤ ∑ a : Fin n, |U_inv i a| *
        (∑ b : Fin n, (γ * ∑ k₁ : Fin n, |U_hat a k₁| *
          (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j|) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro b _
        exact mul_le_mul_of_nonneg_right (hMixed a b) (abs_nonneg _)
    _ = γ * ∑ a : Fin n, |U_inv i a| *
        (∑ b : Fin n, (∑ k₁ : Fin n, |U_hat a k₁| *
          (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        have hfact : ∀ b : Fin n,
            (γ * ∑ k₁ : Fin n, |U_hat a k₁| *
              (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j| =
            γ * ((∑ k₁ : Fin n, |U_hat a k₁| *
              (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j|) :=
          fun _ => by ring
        simp_rw [hfact, ← Finset.mul_sum]; ring

/-- **Abstract Method D left residual interface** (Higham eq. 14.20–14.23).

    Method D: compute X_L ≈ L⁻¹ and X_U ≈ U⁻¹ separately,
    then form X̂ = fl(X_U · X_L).

    From eq. 14.20: X̂ = X_U · X_L + Δ(X_U, X_L).
    The left residual satisfies (eq. 14.23):
      |X̂A − I| ≤ c''ₙu|U⁻¹||L⁻¹||L̂||Û|.

    This theorem records the named residual contract once the separate
    triangular-inverse and matrix-product error terms have been combined by an
    external/local Method D analysis. -/
theorem methodD_left_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_L X_hat : Fin n → Fin n → ℝ)
    (_hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (_hn : gammaValid fp n)
    -- X_L has left residual: |X_L · L̂ − I| ≤ γₙ|X_L||L̂|
    (_hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    -- X_U has right residual: |Û · X_U − I| ≤ γₙ|Û||X_U|
    -- (or equivalently left residual |X_U · Û − I| ≤ γₙ|X_U||Û|)
    (_hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    -- X̂ = fl(X_U · X_L) with product error
    (_hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    -- The left residual bound, combining all four error terms.
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) :=
  hLeftRes

/-- **Abstract Method D SPD specialization** (Higham §14.3.4, p. 274).

    For A = RᵀR (Cholesky), Method D computes X_R ≈ R⁻¹ and forms
    X̂ = X_R · X_Rᵀ.  Using the symmetry, the left residual satisfies
      |X̂A − I| ≤ dₙu|X_R||X_Rᵀ||R̂ᵀ||R̂|.

    This is the specialization of methodD_left_residual with
    L̂ = R̂ᵀ, Û = R̂, X_L = X_Rᵀ, X_U = X_R.  The final specialized
    residual is supplied as `hLeftRes`. -/
theorem methodD_spd_left_residual (n : ℕ) (fp : FPModel)
    (A R_hat : Fin n → Fin n → ℝ)
    (X_R X_hat : Fin n → Fin n → ℝ)
    (_hSPD : IsSymPosDef n A)
    (_hn : gammaValid fp n)
    -- Cholesky: A + ΔA = R̂ᵀR̂ with |ΔA| ≤ γₙ|R̂ᵀ||R̂|
    (_hChol : ∀ i j : Fin n,
      |A i j - ∑ k : Fin n, R_hat k i * R_hat k j| ≤
      gamma fp n * ∑ k : Fin n, |R_hat k i| * |R_hat k j|)
    -- X_R has right residual for R̂⁻¹
    (_hXR_res : ∀ i j : Fin n,
      |∑ k : Fin n, R_hat i k * X_R k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |R_hat i k| * |X_R k j|)
    -- X̂ = fl(X_R · X_Rᵀ)
    (_hProd : MatProdError n X_hat
      (matMul n X_R (fun i j => X_R j i))
      (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_R i k| * |X_R j k|))
    -- The left residual bound (specialization of methodD_left_residual
    -- with L̂ = R̂ᵀ, Û = R̂, X_L = X_Rᵀ, X_U = X_R).
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l : Fin n, |X_R i l| * |X_R k₁ l|) *
          (∑ k₂ : Fin n, |R_hat k₂ k₁| * |R_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l : Fin n, |X_R i l| * |X_R k₁ l|) *
          (∑ k₂ : Fin n, |R_hat k₂ k₁| * |R_hat k₂ j|) :=
  hLeftRes

end NumStability
