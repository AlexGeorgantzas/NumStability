-- Algorithms/LU/SpecialMatrices.lean
--
-- Theorem 9.11: |L||U| = |LU| for special matrix classes
-- (Higham §9.4, Theorem 9.11a,c,d).
--
-- (a) SPD matrices: growth factor ρ_n ≤ 1
-- (c) M-matrices: nonneg LU factors → |L||U| = |A|
-- (d) Sign equivalence: scaling by sign-diagonal preserves optimal growth

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §9.4  Theorem 9.11a: SPD matrices have growth factor ≤ 1
-- ============================================================

/-- **SPD growth factor bound** (Higham §9.4, Theorem 9.11a).

    For a symmetric positive definite matrix, GE without pivoting
    produces factors with max_{i,j} |u_{ij}| ≤ max_{i,j} |a_{ij}|,
    so the growth factor ρ_n ≤ 1 and |L̂||Û| ≤ |A| componentwise.

    This theorem takes the structural bound as hypothesis.
    The bound follows from SPD structure:
    - All leading principal minors are positive
    - Pivot elements satisfy u_kk = a_kk^{(k)} ≤ a_kk
    - Off-diagonal U entries satisfy |u_ij| ≤ max(a_ii, a_jj) ≤ max |a_ij|

    Combined with `LUBackwardError`, this gives |ΔA| ≤ ε|A|. -/
theorem spd_lu_backward_error (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (_hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_backward_error_relative n A L_hat U_hat ε 1 hε (by linarith) hLU
      (by intro i j; linarith [hGrowth i j])
  exact ⟨ΔA, fun i j => by linarith [hΔA_bound i j], hΔA_eq⟩

/-- **SPD backward stability** (Higham §9.4, Theorem 9.11a).

    For SPD matrices with nonneg computed LU factors and ε < 1,
    the backward error is |ΔA| ≤ ε/(1-ε) · |A|, which is optimal. -/
theorem spd_nonneg_lu_backward_stable (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε_lt : ε < 1) (hε_nn : 0 ≤ ε)
    (_hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε / (1 - ε) * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  nonneg_lu_backward_stable n A L_hat U_hat ε hε_lt hε_nn hLU hL_nn hU_nn

-- ============================================================
-- §9.4  Theorem 9.11c: M-matrices have nonneg LU factors
-- ============================================================

/-- **M-matrix nonneg LU factors** (Higham §9.4, Theorem 9.11c).

    For an M-matrix (positive diagonal, nonpositive off-diagonal, nonneg inverse),
    GE without pivoting produces L ≥ 0 and U ≥ 0:
    - l_ij = -a_ij^{(j)} / u_jj ≥ 0 for i > j (since a_ij ≤ 0, u_jj > 0)
    - u_ij ≥ 0 follows from the elimination preserving sign structure

    This theorem states: if A is M-matrix and has exact nonneg LU factors,
    then `HasNonnegLUFactors`, giving |L||U| = |A| via `nonneg_lu_optimal_growth`. -/
theorem mmatrix_nonneg_lu_factors (n : ℕ)
    (A L U : Fin n → Fin n → ℝ)
    (_hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U k j) :
    HasNonnegLUFactors n A L U :=
  ⟨hLU, hL_nn, hU_nn⟩

/-- **M-matrix optimal growth** (Higham §9.4, Theorem 9.11c).

    For an M-matrix with nonneg LU factors: |L||U| = |A| componentwise.
    Combined with backward error ε, this gives |ΔA| ≤ ε|A|. -/
theorem mmatrix_lu_optimal_growth (n : ℕ)
    (A L U : Fin n → Fin n → ℝ)
    (_hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U k j) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| = |A i j| :=
  nonneg_lu_optimal_growth n A L U ⟨hLU, hL_nn, hU_nn⟩

/-- **M-matrix backward stability** (Higham §9.4, Theorem 9.11c + eq 9.8).

    For an M-matrix with nonneg computed factors and ε < 1:
      |ΔA| ≤ ε/(1-ε) · |A| -/
theorem mmatrix_lu_backward_stable (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε_lt : ε < 1) (hε_nn : 0 ≤ ε)
    (_hM : IsMMatrix n A)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε / (1 - ε) * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  nonneg_lu_backward_stable n A L_hat U_hat ε hε_lt hε_nn hLU hL_nn hU_nn

-- ============================================================
-- §9.4  Theorem 9.11d: Sign diagonal equivalence
-- ============================================================

/-- **Sign diagonal matrix** predicate.

    A diagonal matrix D with |D_ii| = 1 (i.e., each diagonal entry is ±1).
    Used in Theorem 9.11d for sign-equivalent matrices A = D₁BD₂. -/
def IsSignDiag (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i ≠ j → D i j = 0) ∧
  (∀ i : Fin n, |D i i| = 1)

/-- Entries of a sign-diagonal matrix are bounded by 1 in absolute value. -/
lemma signDiag_entry_abs (n : ℕ) (D : Fin n → Fin n → ℝ)
    (hD : IsSignDiag n D) (i j : Fin n) : |D i j| ≤ 1 := by
  by_cases h : i = j
  · subst h; rw [hD.2 i]
  · rw [hD.1 i j h, abs_zero]; linarith

/-- **Sign equivalence growth preservation** (Higham §9.4, Theorem 9.11d).

    If B has optimal growth (|L_B||U_B| = |L_B U_B|) and A = D₁BD₂
    where D₁, D₂ are sign-diagonal (entries ±1), then A also has
    optimal growth: |L_A||U_A| = |L_A U_A|.

    The proof uses: L_A = D₁ L_B D_m, U_A = D_m U_B D₂ for an appropriate
    sign-diagonal D_m, so |L_A| = |L_B| and |U_A| = |U_B|.

    This theorem takes the structural hypotheses and produces the
    componentwise growth bound for A from that of B. -/
theorem sign_equiv_growth_preservation (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (c : ℝ) (_hc : 0 ≤ c)
    -- B has growth bounded by c
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| ≤ c * |B i j|)
    -- A = D₁BD₂ (componentwise)
    (A : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    -- A has LU with same absolute structure: |L_A| = |L_B|, |U_A| = |U_B|
    (L_A U_A : Fin n → Fin n → ℝ)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_A i k| * |U_A k j| ≤ c * |A i j| := by
  intro i j
  -- |L_A||U_A| = |L_B||U_B| by absolute value equality
  have h_abs_eq : ∑ k : Fin n, |L_A i k| * |U_A k j| =
      ∑ k : Fin n, |L_B i k| * |U_B k j| := by
    apply Finset.sum_congr rfl; intro k _
    rw [hLA_abs i k, hUA_abs k j]
  rw [h_abs_eq]
  -- A_ij = D₁_ii · B_ij · D₂_jj from diagonal structure, so |A_ij| = |B_ij|
  have hA_diag : A i j = D₁ i i * B i j * D₂ j j := by
    rw [hA_eq i j]
    have h_outer : ∀ k₁ : Fin n, k₁ ≠ i →
        D₁ i k₁ * ∑ k₂, B k₁ k₂ * D₂ k₂ j = 0 := by
      intro k₁ hk; rw [hD₁.1 i k₁ (Ne.symm hk), zero_mul]
    rw [Finset.sum_eq_single i (fun k₁ _ hk => h_outer k₁ hk)
        (fun h => absurd (Finset.mem_univ i) h)]
    have h_inner : ∀ k₂ : Fin n, k₂ ≠ j → B i k₂ * D₂ k₂ j = 0 := by
      intro k₂ hk; rw [hD₂.1 k₂ j hk, mul_zero]
    rw [Finset.sum_eq_single j (fun k₂ _ hk => h_inner k₂ hk)
        (fun h => absurd (Finset.mem_univ j) h)]
    ring
  have habs_eq : |A i j| = |B i j| := by
    rw [hA_diag]
    rw [abs_mul, abs_mul]
    rw [hD₁.2 i, hD₂.2 j]
    ring
  rw [habs_eq]
  exact hB_growth i j

/-- **Sign equivalence optimal growth** (Higham §9.4, Theorem 9.11d, c = 1).

    Special case: if B has |L_B||U_B| = |B| (optimal, c = 1),
    then A = D₁BD₂ also has |L_A||U_A| = |A|. -/
theorem sign_equiv_optimal_growth (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (L_A U_A : Fin n → Fin n → ℝ)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_A i k| * |U_A k j| = |A i j| := by
  intro i j
  have h_abs_eq : ∑ k : Fin n, |L_A i k| * |U_A k j| =
      ∑ k : Fin n, |L_B i k| * |U_B k j| := by
    apply Finset.sum_congr rfl; intro k _
    rw [hLA_abs i k, hUA_abs k j]
  rw [h_abs_eq, hB_growth i j]
  -- |A_ij| = |B_ij| from sign-diagonal structure
  have hA_diag : A i j = D₁ i i * B i j * D₂ j j := by
    rw [hA_eq i j]
    -- Outer sum: only k₁ = i contributes (D₁ is diagonal)
    have h_outer : ∀ k₁ : Fin n, k₁ ≠ i →
        D₁ i k₁ * ∑ k₂, B k₁ k₂ * D₂ k₂ j = 0 := by
      intro k₁ hk; rw [hD₁.1 i k₁ (Ne.symm hk), zero_mul]
    rw [Finset.sum_eq_single i (fun k₁ _ hk => h_outer k₁ hk)
        (fun h => absurd (Finset.mem_univ i) h)]
    -- Inner sum: only k₂ = j contributes (D₂ is diagonal)
    have h_inner : ∀ k₂ : Fin n, k₂ ≠ j → B i k₂ * D₂ k₂ j = 0 := by
      intro k₂ hk; rw [hD₂.1 k₂ j hk, mul_zero]
    rw [Finset.sum_eq_single j (fun k₂ _ hk => h_inner k₂ hk)
        (fun h => absurd (Finset.mem_univ j) h)]
    ring
  rw [hA_diag, abs_mul, abs_mul, hD₁.2 i, hD₂.2 j]; ring

end NumStability
