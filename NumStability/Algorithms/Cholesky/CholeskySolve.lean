-- Algorithms/Cholesky/CholeskySolve.lean
--
-- Theorem 10.4: Overall backward error for solving Ax = b via Cholesky.
--
-- Combining the Cholesky factorization backward error (Theorem 10.3)
-- with two triangular solves (R̂^T y = b, R̂x = y) gives:
--   (A + ΔA)x̂ = b  with  |ΔA| ≤ γ(3n+1) · |R̂^T||R̂|
--
-- The three error sources use different ε values:
--   ε₁ = γ(n+1) for factorization, ε₂ = ε₃ = γ(n) for triangular solves.
-- The expanded bound γ(n+1) + 2γ(n) + γ(n)² absorbs to γ(3n+1).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.Cholesky.CholeskySpec

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §10.1  Theorem 10.4: Cholesky solve backward error
-- ============================================================

/-- **Cholesky solve backward error (expanded form)** (Higham §10.1, Theorem 10.4).

    Computing x̂ via Cholesky factorization + triangular solves gives:
      (A + ΔA)x̂ = b  with  |ΔA| ≤ (γ(n+1) + 2γ(n) + γ(n)²) · |R̂^T||R̂|

    The three error sources use their natural ε values:
    1. Factorization: R̂^T R̂ = A + ΔA₁ with |ΔA₁| ≤ γ(n+1)|R̂^T||R̂|
    2. Forward sub: (R̂^T + ΔR^T)ŷ = b with |ΔR^T| ≤ γ(n)|R̂^T|
    3. Back sub: (R̂ + ΔR)x̂ = ŷ with |ΔR| ≤ γ(n)|R̂|

    Using `lu_solve_backward_error_mixed` with ε₁ = γ(n+1), ε₂ = ε₃ = γ(n),
    the combined bound is (ε₁ + ε₂ + ε₃ + ε₂·ε₃) = γ(n+1) + 2γ(n) + γ(n)². -/
theorem cholesky_solve_backward_error_expanded (fp : FPModel) (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError n A R_hat (gamma fp (n + 1)))
    (hn1 : gammaValid fp (n + 1)) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT b
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let R_hatT := fun i j : Fin n => R_hat j i
  let y_hat := fl_forwardSub fp n R_hatT b
  let x_hat := fl_backSub fp n R_hat y_hat
  -- R̂^T is lower triangular
  have hRT_lower : ∀ i j : Fin n, i.val < j.val → R_hatT i j = 0 :=
    fun i j hij => hChol.R_upper j i hij
  -- R̂ is upper triangular
  have hR_upper : ∀ i j : Fin n, j.val < i.val → R_hat i j = 0 :=
    hChol.R_upper
  -- R̂^T has nonzero diagonal (same as R̂)
  have hRT_diag : ∀ i : Fin n, R_hatT i i ≠ 0 :=
    fun i => hR_diag i
  -- gammaValid fp n (for triangular solve bounds)
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hn1
  -- Step 1: Factorization backward error with ε₁ = γ(n+1)
  have hε₁ : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  obtain ⟨ΔA_fact, hΔA_fact_bound, hΔA_fact_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat (gamma fp (n + 1)) hε₁ hChol
  -- Step 2: Forward sub backward error on R̂^T with ε₂ = γ(n)
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    forwardSub_backward_error fp n R_hatT b hRT_diag hRT_lower hn
  -- Step 3: Back sub backward error on R̂ with ε₃ = γ(n)
  obtain ⟨ΔU, hΔU_bound, hΔU_eq⟩ :=
    backSub_backward_error fp n R_hat y_hat hR_diag hR_upper hn
  -- Apply the mixed-ε LU solve backward error theorem
  have hε₂ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hmixed := lu_solve_backward_error_mixed n A R_hatT R_hat y_hat x_hat
    (gamma fp (n + 1)) (gamma fp n) (gamma fp n) hε₁ hε₂ hε₂
    ΔA_fact hΔA_fact_bound hΔA_fact_eq b ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
  -- Rewrite the coefficient to match our statement
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ := hmixed
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hcoeff : gamma fp (n + 1) + gamma fp n + gamma fp n + gamma fp n * gamma fp n =
      gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2 := by ring
  rw [hcoeff] at hΔA_bound
  exact hΔA_bound i j

/-- **Cholesky solve backward error (absorbed form)** (Higham §10.1, Theorem 10.4).

    The expanded bound γ(n+1) + 2γ(n) + γ(n)² absorbs to γ(3n+1):
    - γ(n) + γ(n) + γ(n)·γ(n) ≤ γ(2n)  by gamma_sum_le
    - γ(n+1) + γ(2n) ≤ γ(n+1) + γ(2n) + γ(n+1)·γ(2n) ≤ γ(3n+1)  by gamma_sum_le

    Final bound: (A + ΔA)x̂ = b  with  |ΔA| ≤ γ(3n+1) · |R̂^T||R̂| -/
theorem cholesky_solve_backward_error (fp : FPModel) (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError n A R_hat (gamma fp (n + 1)))
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n + 1)) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT b
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n + 1) *
        ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let R_hatT := fun i j : Fin n => R_hat j i
  let y_hat := fl_forwardSub fp n R_hatT b
  let x_hat := fl_backSub fp n R_hat y_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_solve_backward_error_expanded fp n A R_hat b hR_diag hChol hn1
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  -- Step 1: γ(n) + γ(n) + γ(n)·γ(n) ≤ γ(2n)
  have hstep1 : gamma fp n + gamma fp n + gamma fp n * gamma fp n ≤ gamma fp (2 * n) := by
    have heq : n + n = 2 * n := by omega
    have h := gamma_sum_le fp n n (gammaValid_mono fp (by omega) hn3)
    rw [heq] at h; exact h
  -- Step 2: γ(n+1) + γ(2n) ≤ γ(n+1) + γ(2n) + γ(n+1)·γ(2n) ≤ γ(3n+1)
  have hstep2 : gamma fp (n + 1) + gamma fp (2 * n) ≤ gamma fp (3 * n + 1) := by
    have heq : (n + 1) + 2 * n = 3 * n + 1 := by omega
    have h := gamma_sum_le fp (n + 1) (2 * n) (heq ▸ hn3)
    have hnn1 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
    have hnn2 : 0 ≤ gamma fp (2 * n) := by
      apply gamma_nonneg fp
      exact gammaValid_mono fp (by omega) hn3
    rw [heq] at h
    linarith [mul_nonneg hnn1 hnn2]
  -- Combine: γ(n+1) + 2γ(n) + γ(n)² ≤ γ(n+1) + γ(2n) ≤ γ(3n+1)
  have habsorb : gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2 ≤
      gamma fp (3 * n + 1) := by
    have : gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2 =
        gamma fp (n + 1) + (gamma fp n + gamma fp n + gamma fp n * gamma fp n) := by ring
    rw [this]
    linarith [hstep1, hstep2]
  have hS := absRT_R_product_nonneg n R_hat i j
  calc |ΔA i j|
      ≤ (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n + 1) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j| := by
        apply mul_le_mul_of_nonneg_right habsorb hS

/-- **Cholesky solve SPD backward stability** (Higham §10.1, combining Theorem 10.4 + growth = 1).

    For SPD with nonneg R̂ and γ(3n+1) < 1:
      (A + ΔA)x̂ = b  with  |ΔA| ≤ γ(3n+1)/(1−γ(n+1)) · |A| -/
theorem cholesky_solve_spd_backward_stable (fp : FPModel) (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError n A R_hat (gamma fp (n + 1)))
    (hn1 : gammaValid fp (n + 1))
    (hn1_lt : gamma fp (n + 1) < 1)
    (hn3 : gammaValid fp (3 * n + 1))
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT b
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n + 1) / (1 - gamma fp (n + 1)) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let R_hatT := fun i j : Fin n => R_hat j i
  let y_hat := fl_forwardSub fp n R_hatT b
  let x_hat := fl_backSub fp n R_hat y_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_solve_backward_error fp n A R_hat b hR_diag hChol hn1 hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hε_nn : (0 : ℝ) ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have hgrowth := cholesky_spd_optimal_growth n A R_hat
    (gamma fp (n + 1)) hn1_lt hε_nn hChol hR_nn i j
  have hγ3_nn : 0 ≤ gamma fp (3 * n + 1) := gamma_nonneg fp hn3
  calc |ΔA i j|
      ≤ gamma fp (3 * n + 1) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n + 1) * (|A i j| / (1 - gamma fp (n + 1))) := by
        apply mul_le_mul_of_nonneg_left hgrowth hγ3_nn
    _ = gamma fp (3 * n + 1) / (1 - gamma fp (n + 1)) * |A i j| := by ring

end NumStability
