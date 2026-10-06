-- Analysis/ForwardError.lean
--
-- Forward error analysis for triangular systems (Higham §8.2).
--
-- Given the backward error result (T + ΔT)x̂ = b with |ΔT| ≤ γ(n)|T|,
-- and assuming Tx = b with T invertible, we derive:
--   |x - x̂| ≤ γ(n) · |T⁻¹| · |T| · |x̂|   (componentwise)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

/-!
# Forward-error analysis for triangular systems

Reusable componentwise forward-error bounds obtained from backward-error
certificates and an explicit inverse.
-/

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Forward error from backward error (Higham §8.2, top)
-- ============================================================

/-- **Componentwise forward error for triangular solve** (Higham §8.2).

    Given:
    - T x = b (exact system)
    - (T + ΔT) x̂ = b (perturbed system, b unperturbed)
    - |ΔT_ij| ≤ ε |T_ij| for all i,j
    - T_inv is a left inverse of T

    Then: |x_i - x̂_i| ≤ ε · (|T⁻¹| |T| |x̂|)_i

    This is the componentwise version of the first result in §8.2:
      |x - x̂| = |T⁻¹ ΔT x̂| ≤ ε |T⁻¹| |T| |x̂|.

    The bound ε is typically γ(n) from Theorem 8.5. -/
theorem forward_error_from_backward_componentwise (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ)
    (x x_hat b : Fin n → ℝ)
    (ΔT : Fin n → Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hInv : IsLeftInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (T i j + ΔT i j) * x_hat j = b i)
    (hΔT : ∀ i j, |ΔT i j| ≤ ε * |T i j|) :
    ∀ i, |x i - x_hat i| ≤
      ε * ∑ j : Fin n, |T_inv i j| * (∑ k : Fin n, |T j k| * |x_hat k|) := by
  -- Step 1: From the two systems, T(x - x̂) = ΔT x̂
  -- Since Tx = b and (T+ΔT)x̂ = b, we get Tx = Tx̂ + ΔTx̂, hence T(x-x̂) = ΔTx̂.
  have hDiff : ∀ i, ∑ j : Fin n, T i j * (x j - x_hat j) =
      ∑ j : Fin n, ΔT i j * x_hat j := by
    intro i
    have h1 := hTx i
    have h2 := hPerturbed i
    have hsub : ∑ j : Fin n, T i j * (x j - x_hat j) =
        (∑ j : Fin n, T i j * x j) - ∑ j : Fin n, T i j * x_hat j := by
      simp_rw [mul_sub]; rw [Finset.sum_sub_distrib]
    rw [hsub, h1]
    have h2' : ∑ j : Fin n, T i j * x_hat j + ∑ j : Fin n, ΔT i j * x_hat j = b i := by
      rw [← Finset.sum_add_distrib]
      convert h2 using 1
      apply Finset.sum_congr rfl; intro j _; ring
    linarith
  -- Step 2: x - x̂ = T_inv * ΔT x̂, so (x - x̂)_i = ∑_j T_inv_ij (∑_k ΔT_jk x̂_k)
  have hSol : ∀ i, x i - x_hat i =
      ∑ j : Fin n, T_inv i j * (∑ k : Fin n, ΔT j k * x_hat k) := by
    intro i
    -- Multiply hDiff by T_inv on the left
    have key : ∑ j : Fin n, T_inv i j * (∑ k : Fin n, T j k * (x k - x_hat k)) =
        ∑ j : Fin n, T_inv i j * (∑ k : Fin n, ΔT j k * x_hat k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hDiff j]
    -- LHS = ∑_j T_inv_ij ∑_k T_jk (x_k - x̂_k) = ∑_k (∑_j T_inv_ij T_jk)(x_k - x̂_k)
    -- = ∑_k δ_ik (x_k - x̂_k) = x_i - x̂_i
    -- Expand LHS of key
    have lhs_eq : ∑ j : Fin n, T_inv i j * (∑ k : Fin n, T j k * (x k - x_hat k)) =
        ∑ k : Fin n, (∑ j : Fin n, T_inv i j * T j k) * (x k - x_hat k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [lhs_eq] at key
    -- ∑_k (∑_j T_inv_ij T_jk)(x_k - x̂_k) = ∑_k δ_ik (x_k - x̂_k) = x_i - x̂_i
    have inv_eq : ∀ k : Fin n, (∑ j : Fin n, T_inv i j * T j k) =
        if i = k then 1 else 0 := fun k => hInv i k
    have lhs_simp : ∑ k : Fin n, (∑ j : Fin n, T_inv i j * T j k) * (x k - x_hat k) =
        x i - x_hat i := by
      simp_rw [inv_eq]
      simp
    linarith
  -- Step 3: Take absolute values and apply triangle inequality + bound on ΔT
  intro i
  rw [hSol i]
  calc |∑ j : Fin n, T_inv i j * (∑ k : Fin n, ΔT j k * x_hat k)|
      ≤ ∑ j : Fin n, |T_inv i j * (∑ k : Fin n, ΔT j k * x_hat k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |T_inv i j| * |∑ k : Fin n, ΔT j k * x_hat k| := by
        apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |T_inv i j| * (∑ k : Fin n, |ΔT j k * x_hat k|) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ = ∑ j : Fin n, |T_inv i j| * (∑ k : Fin n, |ΔT j k| * |x_hat k|) := by
        apply Finset.sum_congr rfl; intro j _
        congr 1; apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |T_inv i j| * (∑ k : Fin n, ε * |T j k| * |x_hat k|) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔT j k) (abs_nonneg _)
    _ = ε * ∑ j : Fin n, |T_inv i j| * (∑ k : Fin n, |T j k| * |x_hat k|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        have : ∑ k : Fin n, ε * |T j k| * |x_hat k| =
            ε * ∑ k : Fin n, |T j k| * |x_hat k| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
        rw [this]; ring

/-- **Forward error for back substitution** (Higham §8.2, applied to Theorem 8.5).

    Combines `backSub_backward_error` with the forward error bound:
    if Ux = b and U is invertible with left inverse U_inv, then
      |x_i - x̂_i| ≤ γ(n) · (|U⁻¹| |U| |x̂|)_i.

    This is a specialization of `forward_error_from_backward_componentwise`
    with ε = γ(n) and ΔT from the backward error theorem. -/
theorem backSub_forward_error (fp : FPModel) (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hInv : IsLeftInverse n U U_inv)
    (hTx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hn : gammaValid fp n) :
    let x_hat := fl_backSub fp n U b
    ∀ i, |x i - x_hat i| ≤
      gamma fp n * ∑ j : Fin n, |U_inv i j| * (∑ k : Fin n, |U j k| * |x_hat k|) := by
  intro x_hat
  obtain ⟨ΔU, hΔU_bound, hΔU_eq⟩ := backSub_backward_error fp n U b hU hUT hn
  exact forward_error_from_backward_componentwise n U U_inv x x_hat b ΔU
    (gamma fp n) (gamma_nonneg fp hn) hInv hTx hΔU_eq hΔU_bound

/-- **Forward error for forward substitution** (Higham §8.2, applied to Theorem 8.5 analog).

    Combines `forwardSub_backward_error` with the forward error bound:
    if Lx = b and L is invertible with left inverse L_inv, then
      |x_i - x̂_i| ≤ γ(n) · (|L⁻¹| |L| |x̂|)_i. -/
theorem forwardSub_forward_error (fp : FPModel) (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hn : gammaValid fp n) :
    let x_hat := fl_forwardSub fp n L b
    ∀ i, |x i - x_hat i| ≤
      gamma fp n * ∑ j : Fin n, |L_inv i j| * (∑ k : Fin n, |L j k| * |x_hat k|) := by
  intro x_hat
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ := forwardSub_backward_error fp n L b hL hLT hn
  exact forward_error_from_backward_componentwise n L L_inv x x_hat b ΔL
    (gamma fp n) (gamma_nonneg fp hn) hInv hTx hΔL_eq hΔL_bound

end NumStability
