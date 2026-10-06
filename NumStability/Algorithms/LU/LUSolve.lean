-- Algorithms/LU/LUSolve.lean
--
-- Overall backward error for solving Ax = b via LU factorization (Higham §9.4, Theorem 9.4).
--
-- Combines the LU factorization backward error (Theorem 9.3) with the
-- triangular solve backward errors (Chapter 8) to show that the computed
-- solution x̂ satisfies (A + ΔA)x̂ = b.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.ForwardError
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LU.GaussianElimination

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §9.4  LU solve: combining factorization and triangular solves
-- ============================================================

/-- **Overall backward error for LU solve** (Higham §9.4, Theorem 9.4).

    Given:
    - L̂, Û computed by Gaussian elimination with `LUBackwardError` at level γ(n)
    - ŷ = fl_forwardSub(L̂, b)  with backward error (L̂ + ΔL)ŷ = b, |ΔL| ≤ γ(n)|L̂|
    - x̂ = fl_backSub(Û, ŷ)    with backward error (Û + ΔU)x̂ = ŷ, |ΔU| ≤ γ(n)|Û|

    Then (A + ΔA)x̂ = b where ΔA arises from expanding
      (L̂ + ΔL)(Û + ΔU) = L̂Û + L̂ΔU + ΔLÛ + ΔLΔU = (A + ΔA_LU) + L̂ΔU + ΔLÛ + ΔLΔU

    The componentwise bound on ΔA is:
      |ΔA_ij| ≤ γ(n) (|L̂||Û|)_ij       (from LU factorization)
             + γ(n) (|L̂||Û|)_ij         (from |L̂||ΔU| ≤ γ(n)|L̂||Û|)
             + γ(n) (|L̂||Û|)_ij         (from |ΔL||Û| ≤ γ(n)|L̂||Û|)
             + γ(n)² (|L̂||Û|)_ij        (from |ΔL||ΔU| ≤ γ(n)²|L̂||Û|)
      = (3γ(n) + γ(n)²) (|L̂||Û|)_ij

    This is Higham's Theorem 9.4 (the exact coefficient 3γ_n + γ_n² = γ_n(3 + γ_n)). -/
theorem lu_solve_backward_error (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  -- Step 1: Forward substitution gives (L̂ + ΔL)ŷ = b
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    forwardSub_backward_error fp n L_hat b hL_diag hLU.L_upper_zero hn
  -- Step 2: Back substitution gives (Û + ΔU)x̂ = ŷ
  obtain ⟨ΔU, hΔU_bound, hΔU_eq⟩ :=
    backSub_backward_error fp n U_hat y_hat hU_diag hLU.U_lower_zero hn
  -- Step 3: LU backward error gives L̂Û = A + ΔA_LU
  obtain ⟨ΔA_LU, hΔA_LU_bound, hΔA_LU_eq⟩ :=
    lu_backward_error_gamma fp n A L_hat U_hat hn hLU
  -- Step 4: Define total perturbation
  -- (L̂+ΔL)(Û+ΔU) = L̂Û + L̂ΔU + ΔLÛ + ΔLΔU
  -- = (A + ΔA_LU) + L̂ΔU + ΔLÛ + ΔLΔU
  -- So ΔA_total = ΔA_LU + L̂ΔU + ΔLÛ + ΔLΔU (in row-column product form)
  let ΔA : Fin n → Fin n → ℝ := fun i j =>
    -- ΔA_LU_ij + (L̂ΔU)_ij + (ΔLÛ)_ij + (ΔLΔU)_ij
    ΔA_LU i j +
    ∑ k : Fin n, L_hat i k * ΔU k j +
    ∑ k : Fin n, ΔL i k * U_hat k j +
    ∑ k : Fin n, ΔL i k * ΔU k j
  refine ⟨ΔA, fun i j => ?_, fun i => ?_⟩
  · -- Bound: |ΔA_ij| ≤ (3γ(n) + γ(n)²) * (|L̂||Û|)_ij
    show |ΔA i j| ≤ _
    -- Triangle inequality on the four terms
    have h1 : |ΔA_LU i j| ≤ gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
      hΔA_LU_bound i j
    -- |L̂ΔU|_ij ≤ ∑_k |L̂_ik||ΔU_kj| ≤ γ(n) ∑_k |L̂_ik||Û_kj|
    have h2 : |∑ k : Fin n, L_hat i k * ΔU k j| ≤
        gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      calc |∑ k : Fin n, L_hat i k * ΔU k j|
          ≤ ∑ k : Fin n, |L_hat i k * ΔU k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |L_hat i k| * |ΔU k j| := by
            apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, |L_hat i k| * (gamma fp n * |U_hat k j|) := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul_of_nonneg_left (hΔU_bound k j) (abs_nonneg _)
        _ = gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    -- |ΔLÛ|_ij ≤ ∑_k |ΔL_ik||Û_kj| ≤ γ(n) ∑_k |L̂_ik||Û_kj|
    have h3 : |∑ k : Fin n, ΔL i k * U_hat k j| ≤
        gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      calc |∑ k : Fin n, ΔL i k * U_hat k j|
          ≤ ∑ k : Fin n, |ΔL i k * U_hat k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |ΔL i k| * |U_hat k j| := by
            apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, (gamma fp n * |L_hat i k|) * |U_hat k j| := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
        _ = gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    -- |ΔLΔU|_ij ≤ ∑_k |ΔL_ik||ΔU_kj| ≤ γ(n)² ∑_k |L̂_ik||Û_kj|
    have h4 : |∑ k : Fin n, ΔL i k * ΔU k j| ≤
        gamma fp n ^ 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      calc |∑ k : Fin n, ΔL i k * ΔU k j|
          ≤ ∑ k : Fin n, |ΔL i k * ΔU k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |ΔL i k| * |ΔU k j| := by
            apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, (gamma fp n * |L_hat i k|) * (gamma fp n * |U_hat k j|) := by
            apply Finset.sum_le_sum; intro k _
            apply mul_le_mul (hΔL_bound i k) (hΔU_bound k j)
              (abs_nonneg _) (mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _))
        _ = gamma fp n ^ 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    -- Combine via triangle inequality (abs_add unavailable, use abs_le pattern)
    let W := ∑ k : Fin n, |L_hat i k| * |U_hat k j|
    let a := ΔA_LU i j
    let b' := ∑ k : Fin n, L_hat i k * ΔU k j
    let c := ∑ k : Fin n, ΔL i k * U_hat k j
    let d := ∑ k : Fin n, ΔL i k * ΔU k j
    have hab : |a + b' + c + d| ≤ |a| + |b'| + |c| + |d| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le a, neg_abs_le b', neg_abs_le c, neg_abs_le d]
      · linarith [le_abs_self a, le_abs_self b', le_abs_self c, le_abs_self d]
    show |ΔA i j| ≤ _
    calc |ΔA i j|
        = |a + b' + c + d| := rfl
      _ ≤ |a| + |b'| + |c| + |d| := hab
      _ ≤ gamma fp n * W + gamma fp n * W + gamma fp n * W +
          gamma fp n ^ 2 * W := by linarith [h1, h2, h3, h4]
      _ = (3 * gamma fp n + gamma fp n ^ 2) * W := by ring
  · -- Equation: (A + ΔA)x̂ = b
    -- We know (L̂+ΔL)(Û+ΔU)x̂ = b
    -- and L̂Û = A + ΔA_LU
    -- So (A + ΔA_LU + L̂ΔU + ΔLÛ + ΔLΔU)x̂ = b
    -- which is (A + ΔA)x̂ = b with our definition of ΔA
    show ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i
    -- From backward errors: (L̂+ΔL)ŷ = b and (Û+ΔU)x̂ = ŷ
    -- So ∑_k (L̂+ΔL)_{ik} ŷ_k = b_i where ŷ_k = ∑_j (Û+ΔU)_{kj} x̂_j
    have hb : ∑ k : Fin n, (L_hat i k + ΔL i k) *
        (∑ j : Fin n, (U_hat k j + ΔU k j) * x_hat j) = b i := by
      rw [← hΔL_eq i]
      apply Finset.sum_congr rfl
      intro k _; rw [hΔU_eq k]
    -- Expand (L̂+ΔL)(Û+ΔU) = L̂Û + L̂ΔU + ΔLÛ + ΔLΔU
    -- and use L̂Û = A + ΔA_LU
    -- So the sum = ∑_j (A_ij + ΔA_LU_ij + (L̂ΔU)_ij + (ΔLÛ)_ij + (ΔLΔU)_ij) x̂_j
    -- = ∑_j (A_ij + ΔA_ij) x̂_j
    -- Key identity: (L̂+ΔL)(Û+ΔU) row-col product = A + ΔA
    have hexpand : ∀ j : Fin n,
        ∑ k : Fin n, (L_hat i k + ΔL i k) * (U_hat k j + ΔU k j) =
        A i j + ΔA i j := by
      intro j
      have hLU_eq := hΔA_LU_eq i j
      -- Expand product: (a+b)(c+d) = ac + ad + bc + bd
      have hprod : ∑ k : Fin n, (L_hat i k + ΔL i k) * (U_hat k j + ΔU k j) =
          ∑ k, L_hat i k * U_hat k j + ∑ k, L_hat i k * ΔU k j +
          ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j := by
        simp_rw [mul_add, add_mul, Finset.sum_add_distrib]; ring
      rw [hprod, hLU_eq]
      show A i j + ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
           ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j =
        A i j + (ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
                 ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j)
      ring
    -- Rewrite LHS: ∑_k (L̂+ΔL)_{ik} (∑_j (Û+ΔU)_{kj} x̂_j)
    -- = ∑_k ∑_j (L̂+ΔL)_{ik} (Û+ΔU)_{kj} x̂_j
    -- = ∑_j (∑_k (L̂+ΔL)_{ik} (Û+ΔU)_{kj}) x̂_j
    -- = ∑_j (A_ij + ΔA_ij) x̂_j
    rw [← hb]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hexpand j]

/-- **Generalized LU solve backward error** (Higham §9.4, Theorem 9.4, bandwidth-aware).

    Like `lu_solve_backward_error` but takes the three component error bounds
    as hypotheses with a generic ε instead of γ(n). This allows specialization
    to bandwidth-adapted bounds (e.g., ε = γ(2) for tridiagonal systems).

    The combined bound is: |ΔA_ij| ≤ (3ε + ε²) · (|L̂||Û|)_ij -/
theorem lu_solve_backward_error_bw (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    -- LU factorization: L̂Û = A + ΔA_LU with |ΔA_LU| ≤ ε|L̂||Û|
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤ ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    -- Forward substitution: (L̂ + ΔL)ŷ = b with |ΔL| ≤ ε|L̂|
    (b : Fin n → ℝ)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ ε * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    -- Back substitution: (Û + ΔU)x̂ = ŷ with |ΔU| ≤ ε|Û|
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ ε * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (3 * ε + ε ^ 2) * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let ΔA : Fin n → Fin n → ℝ := fun i j =>
    ΔA_LU i j +
    ∑ k : Fin n, L_hat i k * ΔU k j +
    ∑ k : Fin n, ΔL i k * U_hat k j +
    ∑ k : Fin n, ΔL i k * ΔU k j
  refine ⟨ΔA, fun i j => ?_, fun i => ?_⟩
  · show |ΔA i j| ≤ _
    have h1 : |ΔA_LU i j| ≤ ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
      hΔA_LU_bound i j
    have h2 : |∑ k : Fin n, L_hat i k * ΔU k j| ≤
        ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      calc |∑ k : Fin n, L_hat i k * ΔU k j|
          ≤ ∑ k : Fin n, |L_hat i k * ΔU k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |L_hat i k| * |ΔU k j| := by
            apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, |L_hat i k| * (ε * |U_hat k j|) := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul_of_nonneg_left (hΔU_bound k j) (abs_nonneg _)
        _ = ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    have h3 : |∑ k : Fin n, ΔL i k * U_hat k j| ≤
        ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      calc |∑ k : Fin n, ΔL i k * U_hat k j|
          ≤ ∑ k : Fin n, |ΔL i k * U_hat k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |ΔL i k| * |U_hat k j| := by
            apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, (ε * |L_hat i k|) * |U_hat k j| := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
        _ = ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    have h4 : |∑ k : Fin n, ΔL i k * ΔU k j| ≤
        ε ^ 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      calc |∑ k : Fin n, ΔL i k * ΔU k j|
          ≤ ∑ k : Fin n, |ΔL i k * ΔU k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |ΔL i k| * |ΔU k j| := by
            apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, (ε * |L_hat i k|) * (ε * |U_hat k j|) := by
            apply Finset.sum_le_sum; intro k _
            apply mul_le_mul (hΔL_bound i k) (hΔU_bound k j)
              (abs_nonneg _) (mul_nonneg hε (abs_nonneg _))
        _ = ε ^ 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    let W := ∑ k : Fin n, |L_hat i k| * |U_hat k j|
    have hab : |ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
               ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j| ≤
        |ΔA_LU i j| + |∑ k, L_hat i k * ΔU k j| +
        |∑ k, ΔL i k * U_hat k j| + |∑ k, ΔL i k * ΔU k j| := by
      rw [abs_le]; constructor
      · linarith [neg_abs_le (ΔA_LU i j),
                   neg_abs_le (∑ k, L_hat i k * ΔU k j),
                   neg_abs_le (∑ k, ΔL i k * U_hat k j),
                   neg_abs_le (∑ k, ΔL i k * ΔU k j)]
      · linarith [le_abs_self (ΔA_LU i j),
                   le_abs_self (∑ k, L_hat i k * ΔU k j),
                   le_abs_self (∑ k, ΔL i k * U_hat k j),
                   le_abs_self (∑ k, ΔL i k * ΔU k j)]
    calc |ΔA i j| = |ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
                     ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j| := rfl
      _ ≤ |ΔA_LU i j| + |∑ k, L_hat i k * ΔU k j| +
          |∑ k, ΔL i k * U_hat k j| + |∑ k, ΔL i k * ΔU k j| := hab
      _ ≤ ε * W + ε * W + ε * W + ε ^ 2 * W := by linarith [h1, h2, h3, h4]
      _ = (3 * ε + ε ^ 2) * W := by ring
  · show ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i
    have hb : ∑ k : Fin n, (L_hat i k + ΔL i k) *
        (∑ j : Fin n, (U_hat k j + ΔU k j) * x_hat j) = b i := by
      rw [← hΔL_eq i]
      apply Finset.sum_congr rfl
      intro k _; rw [hΔU_eq k]
    have hexpand : ∀ j : Fin n,
        ∑ k : Fin n, (L_hat i k + ΔL i k) * (U_hat k j + ΔU k j) =
        A i j + ΔA i j := by
      intro j
      have hLU_eq := hΔA_LU_eq i j
      have hprod : ∑ k : Fin n, (L_hat i k + ΔL i k) * (U_hat k j + ΔU k j) =
          ∑ k, L_hat i k * U_hat k j + ∑ k, L_hat i k * ΔU k j +
          ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j := by
        simp_rw [mul_add, add_mul, Finset.sum_add_distrib]; ring
      rw [hprod, hLU_eq]
      show A i j + ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
           ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j =
        A i j + (ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
                 ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j)
      ring
    rw [← hb]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hexpand j]

/-- **Tight overall backward error for LU solve** (Higham §9.4, Theorem 9.4).

    The coefficient 3γ(n) + γ(n)² from the expanded form is absorbed into
    the cleaner γ(3n) bound using `three_gamma_plus_sq_le_gamma`:
      |ΔA_ij| ≤ γ(3n) · (|L̂||Û|)_ij

    This is the form stated in Higham's book. -/
theorem lu_solve_backward_error_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        gamma fp (3 * n) * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error fp n A L_hat U_hat b hL_diag hU_diag hLU hn
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have h_absorb := three_gamma_plus_sq_le_gamma fp n hn3
  have hW : 0 ≤ ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc |ΔA i j|
      ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n) * ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
        mul_le_mul_of_nonneg_right h_absorb hW

/-- **Mixed-ε LU solve backward error** (generalization of Theorem 9.4).

    Like `lu_solve_backward_error_bw` but takes separate error bounds for
    factorization (ε₁), forward substitution (ε₂), and back substitution (ε₃).

    The combined bound is: |ΔA_ij| ≤ (ε₁ + ε₂ + ε₃ + ε₂·ε₃) · (|L̂||Û|)_ij

    This is useful for Cholesky where the factorization error γ(n+1) differs
    from the triangular solve errors γ(n), giving a tighter result than
    promoting everything to the maximum ε. -/
theorem lu_solve_backward_error_mixed (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (ε₁ ε₂ ε₃ : ℝ) (_hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (_hε₃ : 0 ≤ ε₃)
    -- LU factorization: L̂Û = A + ΔA_LU with |ΔA_LU| ≤ ε₁|L̂||Û|
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤ ε₁ * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    -- Forward substitution: (L̂ + ΔL)ŷ = b with |ΔL| ≤ ε₂|L̂|
    (b : Fin n → ℝ)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ ε₂ * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    -- Back substitution: (Û + ΔU)x̂ = ŷ with |ΔU| ≤ ε₃|Û|
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ ε₃ * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (ε₁ + ε₂ + ε₃ + ε₂ * ε₃) * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let ΔA : Fin n → Fin n → ℝ := fun i j =>
    ΔA_LU i j +
    ∑ k : Fin n, L_hat i k * ΔU k j +
    ∑ k : Fin n, ΔL i k * U_hat k j +
    ∑ k : Fin n, ΔL i k * ΔU k j
  refine ⟨ΔA, fun i j => ?_, fun i => ?_⟩
  · show |ΔA i j| ≤ _
    have h1 : |ΔA_LU i j| ≤ ε₁ * ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
      hΔA_LU_bound i j
    have h2 : |∑ k : Fin n, L_hat i k * ΔU k j| ≤
        ε₃ * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      calc |∑ k : Fin n, L_hat i k * ΔU k j|
          ≤ ∑ k : Fin n, |L_hat i k * ΔU k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |L_hat i k| * |ΔU k j| := by
            apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, |L_hat i k| * (ε₃ * |U_hat k j|) := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul_of_nonneg_left (hΔU_bound k j) (abs_nonneg _)
        _ = ε₃ * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    have h3 : |∑ k : Fin n, ΔL i k * U_hat k j| ≤
        ε₂ * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      calc |∑ k : Fin n, ΔL i k * U_hat k j|
          ≤ ∑ k : Fin n, |ΔL i k * U_hat k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |ΔL i k| * |U_hat k j| := by
            apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, (ε₂ * |L_hat i k|) * |U_hat k j| := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
        _ = ε₂ * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    have h4 : |∑ k : Fin n, ΔL i k * ΔU k j| ≤
        (ε₂ * ε₃) * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      calc |∑ k : Fin n, ΔL i k * ΔU k j|
          ≤ ∑ k : Fin n, |ΔL i k * ΔU k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |ΔL i k| * |ΔU k j| := by
            apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, (ε₂ * |L_hat i k|) * (ε₃ * |U_hat k j|) := by
            apply Finset.sum_le_sum; intro k _
            apply mul_le_mul (hΔL_bound i k) (hΔU_bound k j)
              (abs_nonneg _) (mul_nonneg hε₂ (abs_nonneg _))
        _ = (ε₂ * ε₃) * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    let W := ∑ k : Fin n, |L_hat i k| * |U_hat k j|
    have hab : |ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
               ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j| ≤
        |ΔA_LU i j| + |∑ k, L_hat i k * ΔU k j| +
        |∑ k, ΔL i k * U_hat k j| + |∑ k, ΔL i k * ΔU k j| := by
      rw [abs_le]; constructor
      · linarith [neg_abs_le (ΔA_LU i j),
                   neg_abs_le (∑ k, L_hat i k * ΔU k j),
                   neg_abs_le (∑ k, ΔL i k * U_hat k j),
                   neg_abs_le (∑ k, ΔL i k * ΔU k j)]
      · linarith [le_abs_self (ΔA_LU i j),
                   le_abs_self (∑ k, L_hat i k * ΔU k j),
                   le_abs_self (∑ k, ΔL i k * U_hat k j),
                   le_abs_self (∑ k, ΔL i k * ΔU k j)]
    calc |ΔA i j| = |ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
                     ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j| := rfl
      _ ≤ |ΔA_LU i j| + |∑ k, L_hat i k * ΔU k j| +
          |∑ k, ΔL i k * U_hat k j| + |∑ k, ΔL i k * ΔU k j| := hab
      _ ≤ ε₁ * W + ε₃ * W + ε₂ * W + (ε₂ * ε₃) * W := by linarith [h1, h2, h3, h4]
      _ = (ε₁ + ε₂ + ε₃ + ε₂ * ε₃) * W := by ring
  · show ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i
    have hb : ∑ k : Fin n, (L_hat i k + ΔL i k) *
        (∑ j : Fin n, (U_hat k j + ΔU k j) * x_hat j) = b i := by
      rw [← hΔL_eq i]
      apply Finset.sum_congr rfl
      intro k _; rw [hΔU_eq k]
    have hexpand : ∀ j : Fin n,
        ∑ k : Fin n, (L_hat i k + ΔL i k) * (U_hat k j + ΔU k j) =
        A i j + ΔA i j := by
      intro j
      have hLU_eq := hΔA_LU_eq i j
      have hprod : ∑ k : Fin n, (L_hat i k + ΔL i k) * (U_hat k j + ΔU k j) =
          ∑ k, L_hat i k * U_hat k j + ∑ k, L_hat i k * ΔU k j +
          ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j := by
        simp_rw [mul_add, add_mul, Finset.sum_add_distrib]; ring
      rw [hprod, hLU_eq]
      show A i j + ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
           ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j =
        A i j + (ΔA_LU i j + ∑ k, L_hat i k * ΔU k j +
                 ∑ k, ΔL i k * U_hat k j + ∑ k, ΔL i k * ΔU k j)
      ring
    rw [← hb]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hexpand j]

/-- LU solve backward error with an exposed factorization coefficient.

The LU factorization may be certified at level `epsLU`, while the forward and
back triangular solves are still the concrete repository routines and therefore
charge `gamma fp n`.  The total coefficient is
`epsLU + 2 * gamma fp n + gamma fp n ^ 2`. -/
theorem lu_solve_backward_error_factor_gamma (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    {epsLU : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA_LU, hΔA_LU_bound, hΔA_LU_eq⟩ :=
    lu_backward_error_perturbation n A L_hat U_hat epsLU hepsLU hLU
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    forwardSub_backward_error fp n L_hat b hL_diag hLU.L_upper_zero hn
  obtain ⟨ΔU, hΔU_bound, hΔU_eq⟩ :=
    backSub_backward_error fp n U_hat y_hat hU_diag hLU.U_lower_zero hn
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_mixed n A L_hat U_hat y_hat x_hat
      epsLU (gamma fp n) (gamma fp n)
      hepsLU (gamma_nonneg fp hn) (gamma_nonneg fp hn)
      ΔA_LU hΔA_LU_bound hΔA_LU_eq
      b ΔL hΔL_bound hΔL_eq
      ΔU hΔU_bound hΔU_eq
  refine ⟨ΔA, ?_, hΔA_eq⟩
  intro i j
  convert hΔA_bound i j using 1
  ring

end NumStability
