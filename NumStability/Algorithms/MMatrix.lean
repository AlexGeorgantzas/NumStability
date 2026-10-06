-- Algorithms/MMatrix.lean
--
-- Higham §8.2: M-matrix solution properties and Corollary 8.11 in μ-form.
--
-- When L is a lower triangular M-matrix and b ≥ 0:
--   1. The exact solution x = L⁻¹b is nonneg
--   2. The computed solution x̂ = fl_forwardSub(L, b) is nonneg
--   3. |x_i - x̂_i| ≤ γ(n) · (L⁻¹ |L| x̂)_i  (componentwise)
--   4. |x_i - x̂_i| ≤ μ_i · |x_i|  (relative-error form)
--
-- The theorem below proves the relative-error statement using the library's
-- μ constant.  The asymptotic simplification
-- μ_i ≤ (n²+n+1)u + O(u²) is not formalized as a separate Big-O theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.ForwardError
import NumStability.Algorithms.LinearSystems.Triangular.ComparisonBounds
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Nonneg solutions of lower triangular M-matrix systems
-- ============================================================

/-- Solutions of lower triangular M-matrix systems with nonneg RHS are nonneg.

    If T is lower triangular with T_ii > 0 and T_ij ≤ 0 for j < i,
    and Tx = b with b ≥ 0, then x ≥ 0.

    Proof by induction on i: at row i, T_ii x_i = b_i - Σ_{j<i} T_ij x_j.
    Since T_ij ≤ 0 and x_j ≥ 0 (IH), the off-diagonal sum is ≤ 0,
    so T_ii x_i ≥ b_i ≥ 0. With T_ii > 0, x_i ≥ 0. -/
theorem lower_tri_mmatrix_solution_nonneg (n : ℕ)
    (T : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, j.val < i.val → T i j ≤ 0)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i) :
    ∀ i, 0 ≤ x i := by
  suffices h : ∀ (d : ℕ), ∀ i : Fin n, i.val ≤ d → 0 ≤ x i from
    fun i => h i.val i (le_refl _)
  intro d
  induction d with
  | zero =>
    intro i hi
    have hTxi := hTx i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hTxi
    have hoff : ∑ j ∈ Finset.univ.erase i, T i j * x j = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      have hne := Finset.ne_of_mem_erase hj
      rw [hLT i j (by
        by_contra hc; push_neg at hc
        exact hne (Fin.ext (by omega))), zero_mul]
    have hprod_nn : 0 ≤ T i i * x i := by linarith [hb i]
    by_contra hc; push_neg at hc
    linarith [mul_neg_of_pos_of_neg (hT_diag_pos i) hc]
  | succ d' ih =>
    intro i hi
    by_cases hle : i.val ≤ d'
    · exact ih i hle
    · have hTxi := hTx i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hTxi
      have hoff : ∑ j ∈ Finset.univ.erase i, T i j * x j ≤ 0 := by
        apply Finset.sum_nonpos; intro j hj
        have hne := Finset.ne_of_mem_erase hj
        by_cases hjlt : j.val < i.val
        · exact mul_nonpos_of_nonpos_of_nonneg (hT_offdiag i j hjlt) (ih j (by omega))
        · push_neg at hjlt
          rw [hLT i j (by
            by_contra hc; push_neg at hc
            exact hne (Fin.ext (by omega))), zero_mul]
      have hprod_nn : 0 ≤ T i i * x i := by linarith [hb i]
      by_contra hc; push_neg at hc
      linarith [mul_neg_of_pos_of_neg (hT_diag_pos i) hc]

-- ============================================================
-- Nonnegativity of computed solution
-- ============================================================

/-- The computed forward substitution solution is nonneg for M-matrix L with b ≥ 0.

    Proof: the backward error gives (L+ΔL)x̂ = b where |ΔL| ≤ γ(n)|L|.
    Since γ(n) < 1 (from `gammaValid fp (2*n)`), L+ΔL inherits L's M-matrix
    structure: positive diagonal, nonpositive off-diagonal, lower triangular.
    By `lower_tri_mmatrix_solution_nonneg`, x̂ ≥ 0. -/
theorem forwardSub_nonneg (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0)
    (hb : ∀ i, 0 ≤ b i)
    (hn : gammaValid fp n)
    (h2n : gammaValid fp (2 * n)) :
    ∀ i, 0 ≤ fl_forwardSub fp n L b i := by
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    forwardSub_backward_error fp n L b (fun i => ne_of_gt (hL_diag_pos i)) hLT hn
  have hγ_lt : gamma fp n < 1 := gamma_lt_one fp n h2n
  -- Apply lower_tri_mmatrix_solution_nonneg with T = L + ΔL
  refine lower_tri_mmatrix_solution_nonneg n
    (fun i j => L i j + ΔL i j) (fl_forwardSub fp n L b) b ?_ ?_ ?_ hΔL_eq hb
  -- Lower triangular: for j > i, L_ij = 0 and |ΔL_ij| ≤ γ(n)*0 = 0
  · intro i j hij
    have hLz := hLT i j hij
    have hbd := hΔL_bound i j
    rw [hLz, abs_zero, mul_zero] at hbd
    have hΔz : ΔL i j = 0 := by
      have := le_antisymm hbd (abs_nonneg _)
      rwa [abs_eq_zero] at this
    simp [hLz, hΔz]
  -- Positive diagonal: L_ii + ΔL_ii ≥ L_ii(1 - γ(n)) > 0
  · intro i
    have hbd := hΔL_bound i i
    have habs : |L i i| = L i i := abs_of_pos (hL_diag_pos i)
    rw [habs] at hbd
    have hΔ_lo : -(gamma fp n * L i i) ≤ ΔL i i := by linarith [neg_abs_le (ΔL i i)]
    have h1 : L i i + ΔL i i ≥ L i i * (1 - gamma fp n) := by linarith
    exact lt_of_lt_of_le (mul_pos (hL_diag_pos i) (by linarith : (0:ℝ) < 1 - gamma fp n)) h1
  -- Nonpositive off-diagonal: L_ij + ΔL_ij ≤ L_ij(1 - γ(n)) ≤ 0
  · intro i j hjlt
    have hbd := hΔL_bound i j
    have hoff := hL_offdiag i j hjlt
    have habs : |L i j| = -(L i j) := abs_of_nonpos hoff
    rw [habs] at hbd
    have hΔ_hi : ΔL i j ≤ gamma fp n * -(L i j) := le_trans (le_abs_self _) hbd
    have h1 : L i j + ΔL i j ≤ L i j * (1 - gamma fp n) := by linarith
    exact le_of_le_of_eq (le_trans h1 (mul_nonpos_of_nonpos_of_nonneg hoff (by linarith))) rfl

-- ============================================================
-- Weak Corollary 8.11: M-matrix forward error bound
-- ============================================================

/-- **Weak Corollary 8.11** (Higham §8.2).

    For a lower triangular M-matrix L with b ≥ 0:
      1. The exact solution x ≥ 0
      2. The computed solution x̂ ≥ 0
      3. |x_i - x̂_i| ≤ γ(n) · (L⁻¹ |L| x̂)_i

    Part 3 is Theorem 8.9 specialized to M-matrices (where M(L) = L,
    so M(L)⁻¹ = L⁻¹). The nonnegativity of x̂ allows dropping absolute
    values: |x̂_k| = x̂_k in the bound.

    Note: Higham's full Corollary 8.11 gives the tighter bound
    |x - x̂| ≤ ((n²+n+1)u + O(u²))|x| via a direct recurrence proof. -/
theorem mmatrix_forwardSub_componentwise_bound (fp : FPModel) (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0)
    (hInv : IsInverse n L L_inv)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hn : gammaValid fp n)
    (h2n : gammaValid fp (2 * n)) :
    let x_hat := fl_forwardSub fp n L b
    (∀ i, 0 ≤ x i) ∧
    (∀ i, 0 ≤ x_hat i) ∧
    (∀ i, |x i - x_hat i| ≤
      gamma fp n * ∑ j : Fin n, L_inv i j * (∑ k : Fin n, |L j k| * x_hat k)) := by
  intro x_hat
  have hL_diag : ∀ i, L i i ≠ 0 := fun i => ne_of_gt (hL_diag_pos i)
  -- Part 1: exact solution nonneg
  have hx_nn : ∀ i, 0 ≤ x i :=
    lower_tri_mmatrix_solution_nonneg n L x b hLT hL_diag_pos hL_offdiag hTx hb
  -- Part 2: computed solution nonneg
  have hx_hat_nn : ∀ i, 0 ≤ x_hat i :=
    forwardSub_nonneg fp n L b hLT hL_diag_pos hL_offdiag hb hn h2n
  -- Part 3: forward error bound via Theorem 8.9 with M(L)⁻¹ = L⁻¹
  have hML := comparisonMatrix_eq_self_mmatrix_lower n L hLT hL_diag_pos hL_offdiag
  have hInv_lt := inv_lower_tri n L L_inv hLT hL_diag hInv.1
  have h89 := forwardSub_forward_error_comparison fp n L L_inv L_inv x b hL_diag hLT hInv
    (by rw [hML]; exact hInv.2) hInv_lt hTx hn
  refine ⟨hx_nn, hx_hat_nn, ?_⟩
  -- Rewrite |x̂_k| → x̂_k using nonnegativity
  intro i
  calc |x i - x_hat i|
      ≤ gamma fp n * ∑ j : Fin n, L_inv i j *
          (∑ k : Fin n, |L j k| * |x_hat k|) := h89 i
    _ = gamma fp n * ∑ j : Fin n, L_inv i j *
          (∑ k : Fin n, |L j k| * x_hat k) := by
        congr 1; apply Finset.sum_congr rfl; intro j _
        congr 1; apply Finset.sum_congr rfl; intro k _
        rw [abs_of_nonneg (hx_hat_nn k)]

-- ============================================================
-- Corollary 8.11 in μ-form: M-matrix forward relative error
-- ============================================================

/-- **Corollary 8.11 in μ-form** (Higham §8.2).

    For a lower triangular M-matrix L with b ≥ 0, the computed solution
    from forward substitution satisfies:
      |x_i - x̂_i| ≤ μ_i · |x_i|

    where μ_k = (1+γ(n+1))^k · (1+u) − 1.  Higham further simplifies
    this to (n²+n+1)u + O(u²); that asymptotic expansion is not formalized
    as a separate Big-O theorem here.

    This shows that every component of the solution is computed to high
    relative accuracy when T is an M-matrix and b ≥ 0, irrespective of
    the condition number κ(T).

    Proof: From Theorem 8.9, |x_i - x̂_i| ≤ μ_i · (M(L)⁻¹|b|)_i.
    For M-matrices: M(L) = L, so M(L)⁻¹ = L⁻¹.
    Since L⁻¹ ≥ 0 and b ≥ 0, M(L)⁻¹|b| = L⁻¹b = x ≥ 0 = |x|. -/
theorem mmatrix_forwardSub_relative_error (fp : FPModel) (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0)
    (hInv : IsInverse n L L_inv)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (h2n : gammaValid fp (2 * n)) :
    let x_hat := fl_forwardSub fp n L b
    (∀ i, 0 ≤ x i) ∧
    (∀ i, 0 ≤ x_hat i) ∧
    (∀ i, |x i - x_hat i| ≤ mu fp n i.val * |x i|) := by
  intro x_hat
  have hL_diag : ∀ i, L i i ≠ 0 := fun i => ne_of_gt (hL_diag_pos i)
  -- Part 1: exact solution nonneg
  have hx_nn : ∀ i, 0 ≤ x i :=
    lower_tri_mmatrix_solution_nonneg n L x b hLT hL_diag_pos hL_offdiag hTx hb
  -- Part 2: computed solution nonneg
  have hx_hat_nn : ∀ i, 0 ≤ x_hat i :=
    forwardSub_nonneg fp n L b hLT hL_diag_pos hL_offdiag hb hn h2n
  -- M(L) = L for M-matrices
  have hML := comparisonMatrix_eq_self_mmatrix_lower n L hLT hL_diag_pos hL_offdiag
  -- L_inv is lower triangular
  have hInv_lt := inv_lower_tri n L L_inv hLT hL_diag hInv.1
  -- L_inv is a right inverse of M(L) = L
  have hM_RInv : IsRightInverse n (comparisonMatrix n L) L_inv := by
    rw [hML]; exact hInv.2
  -- Part 3: Apply Theorem 8.9
  have h89 := forwardSub_forward_error_mu_bound fp n L L_inv L_inv x b
    hL_diag hLT hInv hM_RInv hInv_lt hTx hn hn1
  refine ⟨hx_nn, hx_hat_nn, ?_⟩
  -- Show y_i = |x_i| for M-matrices with b ≥ 0
  -- y_i = Σ_j L_inv i j * |b_j| = Σ_j L_inv i j * b_j = x_i = |x_i|
  intro i
  have h89i := h89 i
  -- y_i = Σ_j L_inv i j * |b_j|
  -- Since b ≥ 0: |b_j| = b_j
  have hb_abs : ∀ j : Fin n, |b j| = b j := fun j => abs_of_nonneg (hb j)
  -- So y_i = Σ_j L_inv i j * b_j
  have hy_eq_sum : (∑ j : Fin n, L_inv i j * |b j|) = ∑ j : Fin n, L_inv i j * b j := by
    apply Finset.sum_congr rfl; intro j _; rw [hb_abs]
  -- x_i = Σ_j L_inv i j * b_j (from L_inv * L * x = x and Lx = b)
  have hx_eq : x i = ∑ j : Fin n, L_inv i j * b j := by
    have hLI := hInv.1 i
    have : ∑ j : Fin n, L_inv i j * b j =
        ∑ j : Fin n, L_inv i j * (∑ k : Fin n, L j k * x k) := by
      congr 1; funext j; rw [hTx j]
    rw [this]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have hsimp : ∀ k : Fin n,
        (∑ j : Fin n, L_inv i j * L j k) * x k = (if i = k then 1 else 0) * x k := by
      intro k; congr 1; exact hLI k
    simp_rw [hsimp]; simp [Finset.mem_univ]
  -- y_i = x_i = |x_i| (since x ≥ 0)
  have hy_eq : (∑ j : Fin n, L_inv i j * |b j|) = |x i| := by
    rw [hy_eq_sum, ← hx_eq, abs_of_nonneg (hx_nn i)]
  dsimp only at h89i
  rw [hy_eq] at h89i
  exact h89i

end NumStability
