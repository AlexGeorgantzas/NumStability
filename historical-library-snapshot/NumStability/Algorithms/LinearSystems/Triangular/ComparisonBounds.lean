import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.ForwardError
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds

/-!
# Comparison-matrix bounds for triangular solves

Reusable componentwise forward-error bounds via comparison matrices,
including lower-triangular M-matrix utilities.
-/

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Backward-error-derived forward error via comparison matrix
-- ============================================================

/-- Forward error for forward substitution via comparison matrix (Theorems 8.5 + 8.11).

    The forward error for forward substitution satisfies:
      |x_i - x̂_i| ≤ γ(n) · (M(L)⁻¹ · |L| · |x̂|)_i

    This strengthens `forwardSub_forward_error` by replacing |L⁻¹| with
    M(L)⁻¹ using Theorem 8.11 (|L⁻¹| ≤ M(L)⁻¹). The bound can be
    much tighter because M(L)⁻¹ ≥ |L⁻¹| with equality when L = M(L).

    This is a useful consequence of the backward-error theorem and comparison
    matrix inverse bound. It is not Higham's direct Theorem 8.9, which is
    formalized below as `forwardSub_forward_error_mu_bound` and gives the
    tighter `M(T)⁻¹|b|` μ-bound by componentwise induction. -/
theorem forwardSub_forward_error_comparison (fp : FPModel) (n : ℕ)
    (L L_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n L) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hn : gammaValid fp n) :
    let x_hat := fl_forwardSub fp n L b
    ∀ i, |x i - x_hat i| ≤
      gamma fp n * ∑ j : Fin n, M_inv i j * (∑ k : Fin n, |L j k| * |x_hat k|) := by
  intro x_hat
  have hfwd := forwardSub_forward_error fp n L L_inv x b hL hLT hInv.1 hTx hn
  have habs_bound := abs_inv_le_compMatrix_inv_lowerTri n L L_inv M_inv hLT hL hInv
    hM_RInv hM_inv_lt
  -- M_inv has nonneg entries (M-matrix inverse)
  have hM_nn := lower_tri_mmatrix_inv_nonneg n (comparisonMatrix n L) M_inv
    (by intro i j hij; unfold comparisonMatrix
        simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hLT i j hij])
    (by intro i; simp [comparisonMatrix]; exact hL i)
    (by intro i j _; simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)])
    hM_RInv hM_inv_lt
  intro i
  calc |x i - x_hat i|
      ≤ gamma fp n * ∑ j : Fin n, |L_inv i j| *
          (∑ k : Fin n, |L j k| * |x_hat k|) := hfwd i
    _ ≤ gamma fp n * ∑ j : Fin n, M_inv i j *
          (∑ k : Fin n, |L j k| * |x_hat k|) := by
        apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn)
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg
          (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        exact habs_bound i j

-- ============================================================
-- M-matrix utilities for lower triangular matrices
-- ============================================================

/-- When L is a lower triangular M-matrix (positive diagonal, nonpositive off-diagonal),
    the comparison matrix equals L itself. -/
theorem comparisonMatrix_eq_self_mmatrix_lower (n : ℕ) (L : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0) :
    comparisonMatrix n L = L := by
  funext i j
  unfold comparisonMatrix
  by_cases hij : i = j
  · subst hij; simp [abs_of_pos (hL_diag_pos i)]
  · simp [hij]
    by_cases hlt : j.val < i.val
    · have hle := hL_offdiag i j hlt
      rw [abs_of_nonpos hle]; ring
    · push_neg at hlt
      have : i.val < j.val := Nat.lt_of_le_of_ne (by omega) (fun h => hij (Fin.ext h))
      rw [hLT i j this, abs_zero, neg_zero]

/-- When L is a lower triangular M-matrix, its inverse has nonneg entries. -/
theorem mmatrix_inv_nonneg_lower (n : ℕ) (L L_inv : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0)
    (hInv : IsInverse n L L_inv) :
    ∀ i j : Fin n, 0 ≤ L_inv i j := by
  have hInv_lt := inv_lower_tri n L L_inv hLT (fun i => ne_of_gt (hL_diag_pos i)) hInv.1
  exact lower_tri_mmatrix_inv_nonneg n L L_inv hLT hL_diag_pos hL_offdiag hInv.2 hInv_lt

-- ============================================================
-- Theorem 8.10: Direct forward error via comparison matrix
-- ============================================================

/-- The error multiplier recurrence for Theorem 8.9.
    mu_0 = u, mu_{k+1} = (1 + γ(n+1)) mu_k + γ(n+1). -/
noncomputable def mu (fp : FPModel) (n : ℕ) : ℕ → ℝ
  | 0     => fp.u
  | k + 1 => (1 + gamma fp (n + 1)) * mu fp n k + gamma fp (n + 1)

lemma mu_nonneg (fp : FPModel) (n : ℕ) (hn1 : gammaValid fp (n + 1)) :
    ∀ k, 0 ≤ mu fp n k := by
  intro k; induction k with
  | zero => exact fp.u_nonneg
  | succ k ih =>
    simp only [mu]
    exact add_nonneg (mul_nonneg (by linarith [gamma_nonneg fp hn1]) ih)
      (gamma_nonneg fp hn1)

lemma mu_mono (fp : FPModel) (n : ℕ) (hn1 : gammaValid fp (n + 1)) :
    ∀ k, mu fp n k ≤ mu fp n (k + 1) := by
  intro k; simp only [mu]
  nlinarith [mu_nonneg fp n hn1 k, gamma_nonneg fp hn1]

lemma gamma_le_mu_succ (fp : FPModel) (n : ℕ) (hn1 : gammaValid fp (n + 1)) :
    ∀ k, gamma fp (n + 1) ≤ mu fp n (k + 1) := by
  intro k; simp only [mu]
  linarith [mul_nonneg (by linarith [gamma_nonneg fp hn1] : (0:ℝ) ≤ 1 + gamma fp (n + 1))
    (mu_nonneg fp n hn1 k)]

/-- Closed form for the error multiplier recurrence:
    μ_k = (1 + γ(n+1))^k · (1 + u) − 1.

    From page 159 of Higham: solving μ_k = (1+γ)μ_{k-1} + γ with μ_0 = u
    gives μ_k = (1+γ)^k(1+u) − 1. -/
lemma mu_closed_form (fp : FPModel) (n : ℕ) :
    ∀ k, mu fp n k = (1 + gamma fp (n + 1)) ^ k * (1 + fp.u) - 1 := by
  intro k; induction k with
  | zero => simp [mu]
  | succ k ih => simp only [mu, ih]; ring

/-- Exact solution satisfies |x_i| ≤ (M(L)⁻¹|b|)_i componentwise.
    From |L⁻¹| ≤ M(L)⁻¹ and x = L⁻¹b. -/
lemma exact_solution_le_comp_inv_abs_b (n : ℕ)
    (L L_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hInv : IsInverse n L L_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n L) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i) :
    ∀ i, |x i| ≤ ∑ j : Fin n, M_inv i j * |b j| := by
  have habs := abs_inv_le_compMatrix_inv_lowerTri n L L_inv M_inv hLT hL_diag hInv
    hM_RInv hM_inv_lt
  intro i
  -- x = L_inv * b, so x_i = Σ L_inv_ij * b_j
  have hx : x i = ∑ j : Fin n, L_inv i j * b j := by
    have hLI := hInv.1 i
    have htx := hTx
    -- From L_inv * L = I and Lx = b, L_inv * b = L_inv * L * x = x
    have : ∑ j : Fin n, L_inv i j * b j =
        ∑ j : Fin n, L_inv i j * (∑ k : Fin n, L j k * x k) := by
      congr 1; funext j; rw [htx j]
    rw [this]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    -- Goal: x i = Σ k, (Σ j, L_inv i j * L j k) * x k
    -- Use L_inv * L = I: Σ j L_inv i j * L j k = if i = k then 1 else 0
    have hsimp : ∀ k : Fin n,
        (∑ j : Fin n, L_inv i j * L j k) * x k = (if i = k then 1 else 0) * x k := by
      intro k; congr 1; exact hLI k
    simp_rw [hsimp]; simp [Finset.mem_univ]
  rw [hx]
  calc |∑ j : Fin n, L_inv i j * b j|
      ≤ ∑ j : Fin n, |L_inv i j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |L_inv i j| * |b j| := by
        apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, M_inv i j * |b j| := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_right (habs i j) (abs_nonneg _)

/-- Row equation for M(L)⁻¹|b|: |L_ii| y_i = |b_i| + Σ_{j<i} |L_ij| y_j.
    From M(L) y = |b| expanded for lower triangular L. -/
lemma compMatrix_inv_row_eq (n : ℕ)
    (L M_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n L) M_inv)
    (_hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0)
    (i : Fin n) :
    let y := fun i => ∑ j : Fin n, M_inv i j * |b j|
    |L i i| * y i = |b i| +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
        |L i j| * y j := by
  intro y
  -- M(L) * M_inv = I, so Σ_k M(L)_ik * M_inv_kj = δ_ij
  -- For column j of M_inv: (M(L) * y')_i = |b_i| where y' = M_inv * |b|
  -- Expand: Σ_k M(L)_ik * (Σ_j M_inv_kj * |b_j|) = ...
  -- Actually use M(L) * (M_inv * |b|) = |b| from M(L) * M_inv = I
  have hMy : ∀ i', ∑ k : Fin n, comparisonMatrix n L i' k * y k = |b i'| := by
    intro i'
    simp only [y]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    conv_rhs => rw [show |b i'| = ∑ j : Fin n, (if i' = j then 1 else 0) * |b j| by
      simp [Finset.mem_univ]]
    apply Finset.sum_congr rfl; intro j _
    congr 1; exact hM_RInv i' j
  have hrow := hMy i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hrow
  -- M(L)_ii = |L_ii|
  have hM_ii : comparisonMatrix n L i i = |L i i| := by simp [comparisonMatrix]
  rw [hM_ii] at hrow
  -- Split remaining sum: j < i gives -|L_ij| * y_j, j > i gives 0
  have hrest : ∑ k ∈ Finset.univ.erase i, comparisonMatrix n L i k * y k =
      -(∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
        |L i j| * y j) := by
    -- Terms with k > i are zero (lower triangular), so erase i = filter (< i)
    have herase_eq : ∑ k ∈ Finset.univ.erase i, comparisonMatrix n L i k * y k =
        ∑ k ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
          comparisonMatrix n L i k * y k := by
      symm; apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
      · intro k hk hknot
        rw [Finset.mem_erase] at hk
        have hknot' : ¬(k.val < i.val) := by
          intro hc; exact hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
        have hgt : i.val < k.val := by omega
        unfold comparisonMatrix
        simp [show i ≠ k from Fin.ne_of_val_ne (by omega), hLT i k hgt, zero_mul]
    rw [herase_eq, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    unfold comparisonMatrix
    simp [show i ≠ k from Fin.ne_of_val_ne (by omega)]
  rw [hrest] at hrow; linarith

set_option maxHeartbeats 800000

/-- **Theorem 8.10** (Higham §8.2).

    The forward error for forward substitution, proved by direct component-wise
    induction (not via backward error), satisfies:
      |x_i - x̂_i| ≤ μ_i · (M(L)⁻¹ |b|)_i

    where μ_0 = u, μ_{k+1} = (1+γ(n+1))μ_k + γ(n+1).

    This bound involves |b| (not |L||x̂|) and gives the tighter coefficient
    μ_n ≤ (n²+n+1)u + O(u²) when expanded. -/
theorem forwardSub_forward_error_mu_bound (fp : FPModel) (n : ℕ)
    (L L_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n L) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1)) :
    let x_hat := fl_forwardSub fp n L b
    let y := fun i => ∑ j : Fin n, M_inv i j * |b j|
    ∀ i : Fin n, |x i - x_hat i| ≤ mu fp n i.val * y i := by
  intro x_hat y
  -- y ≥ 0 since M_inv ≥ 0 and |b| ≥ 0
  have hM_nn := lower_tri_mmatrix_inv_nonneg n (comparisonMatrix n L) M_inv
    (by intro i j hij; unfold comparisonMatrix
        simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hLT i j hij])
    (by intro i; simp [comparisonMatrix]; exact hL_diag i)
    (by intro i j _; simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)])
    hM_RInv hM_inv_lt
  have hy_nn : ∀ i, 0 ≤ y i := by
    intro i; apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (hM_nn i j) (abs_nonneg _)
  -- |x_j| ≤ y_j
  have hx_le_y := exact_solution_le_comp_inv_abs_b n L L_inv M_inv x b
    hLT hL_diag hInv hM_RInv hM_inv_lt hTx
  -- Get per-row spec
  have hspec := fl_forwardSub_satisfies_spec fp n L b hL_diag hn
  -- Row equation for y
  have hrow := compMatrix_inv_row_eq n L M_inv b hLT hL_diag hM_RInv hM_inv_lt
  -- γ shorthand
  set γ := gamma fp (n + 1) with hγ_def
  have hγ_nn : 0 ≤ γ := gamma_nonneg fp hn1
  -- Induction on i.val
  suffices h : ∀ d : ℕ, ∀ i : Fin n, i.val ≤ d →
      |x i - x_hat i| ≤ mu fp n i.val * y i from
    fun i => h i.val i (le_refl _)
  intro d
  induction d with
  | zero =>
    intro i hi
    have hi0 : i.val = 0 := by omega
    -- Base case: row 0, no off-diagonal terms
    obtain ⟨Θ, ρ, θ, hΘ, hρ, _, hspec_eq⟩ := hspec i
    -- Θ bound: |Θ| ≤ γ(0) = 0
    have hΘ0 : Θ = 0 := by
      have hg0 : gamma fp 0 = 0 := by unfold gamma; simp
      rw [hi0] at hΘ; rw [hg0] at hΘ
      exact abs_eq_zero.mp (le_antisymm hΘ (abs_nonneg Θ))
    -- No off-diagonal terms: filter is empty
    have hfilt_empty : Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ = ∅ := by
      ext j; simp; omega
    simp only [hΘ0, hfilt_empty, Finset.sum_empty, sub_zero, add_zero, mul_one] at hspec_eq
    -- L_ii x̂_i = b_i (1+ρ), L_ii x_i = b_i
    have hLx : L i i * x i = b i := by
      have := hTx i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
      have hoff : ∑ j ∈ Finset.univ.erase i, L i j * x j = 0 := by
        apply Finset.sum_eq_zero; intro j hj
        have hji := Finset.ne_of_mem_erase hj
        rw [hLT i j (by
          by_contra hc; push_neg at hc
          exact hji (Fin.ext (by omega))), zero_mul]
      linarith
    -- x_i - x̂_i = -b_i ρ / L_ii
    have hdiff : L i i * (x i - x_hat i) = -b i * ρ := by linarith
    have : |L i i * (x i - x_hat i)| = |L i i| * |x i - x_hat i| := abs_mul _ _
    have : |(-b i) * ρ| = |b i| * |ρ| := by rw [abs_mul, abs_neg]
    have habs_eq : |L i i| * |x i - x_hat i| = |b i| * |ρ| := by
      rw [← abs_mul]; conv_rhs => rw [← abs_neg (b i), ← abs_mul]
      exact congrArg _ hdiff
    -- |x_i - x̂_i| = |b_i| |ρ| / |L_ii| ≤ u |b_i| / |L_ii|
    have hLii_pos : 0 < |L i i| := abs_pos.mpr (hL_diag i)
    have hbound : |x i - x_hat i| ≤ fp.u * (|b i| / |L i i|) := by
      have hLii_ne : (|L i i| : ℝ) ≠ 0 := ne_of_gt hLii_pos
      have h1 : |L i i| * |x i - x_hat i| ≤ fp.u * |b i| := by
        nlinarith [habs_eq, mul_le_mul_of_nonneg_left hρ (abs_nonneg (b i))]
      calc |x i - x_hat i|
          = |L i i| * |x i - x_hat i| / |L i i| := by field_simp
        _ ≤ fp.u * |b i| / |L i i| := by
            exact div_le_div_of_nonneg_right h1 (le_of_lt hLii_pos)
        _ = fp.u * (|b i| / |L i i|) := by rw [mul_div_assoc]
    -- mu 0 = u, y_i = |b_i|/|L_ii| (since no off-diagonal terms)
    have hrow_i := hrow i
    dsimp only at hrow_i
    have hfilt_empty' : Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ = ∅ := by
      ext j; simp; omega
    rw [hfilt_empty'] at hrow_i; simp at hrow_i
    -- y_i = |b_i| / |L_ii|
    have hy_eq : y i = |b i| / |L i i| := by
      have := hrow_i; field_simp [ne_of_gt hLii_pos] at this ⊢; linarith
    rw [hi0]; simp only [mu]; rw [hy_eq]; linarith
  | succ d ih =>
    intro i hi
    by_cases hle : i.val ≤ d
    · exact ih i hle
    · have hi_pos : 0 < i.val := by omega
      -- Get per-row spec
      obtain ⟨Θ, ρ, θ, hΘ, hρ, hθ, hspec_eq⟩ := hspec i
      -- Exact equation: L_ii x_i = b_i - Σ_{j<i} L_ij x_j
      have hLx : L i i * x i = b i -
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
            L i j * x j := by
        have := hTx i
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
        have hoff : ∑ j ∈ Finset.univ.erase i, L i j * x j =
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), L i j * x j := by
          symm; apply Finset.sum_subset
          · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
          · intro j hj hjnot
            rw [Finset.mem_erase] at hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hjnot
            rw [hLT i j (by omega), zero_mul]
        linarith
      -- Subtract: L_ii(x_i - x̂_i) = b_i(1-(1+Θ)(1+ρ))
      --   + Σ L_ij(x̂_j(1+θ_j)(1+ρ) - x_j)
      -- = -b_i α + Σ L_ij(-(x_j-x̂_j)(1+θ_j)(1+ρ) + x_j((1+θ_j)(1+ρ)-1))
      -- where α = (1+Θ)(1+ρ) - 1
      have hdiff : L i i * (x i - x_hat i) =
          b i * (1 - (1+Θ)*(1+ρ)) +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
            L i j * (x_hat j * (1+θ j) * (1+ρ) - x j) := by
        have h1 : L i i * x_hat i =
            (b i * (1+Θ) - ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
              L i j * x_hat j * (1+θ j)) * (1+ρ) := hspec_eq
        have h2 : L i i * (x i - x_hat i) = L i i * x i - L i i * x_hat i := by ring
        rw [h2, hLx, h1]
        -- LHS: (b i - Σ L_ij x_j) - (b i(1+Θ) - Σ L_ij x̂_j(1+θ_j))(1+ρ)
        -- RHS: b i(1-(1+Θ)(1+ρ)) + Σ L_ij(x̂_j(1+θ_j)(1+ρ) - x_j)
        -- Goal: LHS = b i * (1-(1+Θ)*(1+ρ)) + Σ_{j<i} L i j * (x̂_j*(1+θ_j)*(1+ρ) - x_j)
        set S := Finset.univ.filter (fun j : Fin n => j.val < i.val) with hS_def
        -- Step 1: expand (... - Σ g) * (1+ρ) = ... * (1+ρ) - Σ g*(1+ρ)
        have hexpand : (b i * (1+Θ) - ∑ j ∈ S, L i j * x_hat j * (1+θ j)) * (1+ρ) =
            b i * (1+Θ) * (1+ρ) - ∑ j ∈ S, (L i j * x_hat j * (1+θ j) * (1+ρ)) := by
          rw [sub_mul, Finset.sum_mul]
        rw [hexpand]
        -- Step 2: Σ g - Σ f = Σ (g - f)
        have hcombine :
            ∑ j ∈ S, (L i j * x_hat j * (1+θ j) * (1+ρ)) - ∑ j ∈ S, (L i j * x j) =
            ∑ j ∈ S, (L i j * (x_hat j * (1+θ j) * (1+ρ) - x j)) := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
        linarith [hcombine]
      -- Take absolute values, divide by |L_ii|
      have hLii_pos : 0 < |L i i| := abs_pos.mpr (hL_diag i)
      have hLii_ne : |L i i| ≠ 0 := ne_of_gt hLii_pos
      -- Bound |α| = |1-(1+Θ)(1+ρ)| = |(1+Θ)(1+ρ)-1|
      -- From ForwardSubRowSpec: |Θ| ≤ γ(i.val) ≤ γ(n), |ρ| ≤ u ≤ γ(1)
      -- So |(1+Θ)(1+ρ)-1| ≤ γ(i.val+1) ≤ γ(n+1) by gamma_mul
      have hα_bound : |(1+Θ)*(1+ρ) - 1| ≤ γ := by
        have hi_valid : gammaValid fp i.val := gammaValid_mono fp (by omega) hn
        have h1_valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
        have hi1_valid : gammaValid fp (i.val + 1) := gammaValid_mono fp (by omega) hn1
        have hρ_γ1 : |ρ| ≤ gamma fp 1 :=
          le_trans hρ (u_le_gamma fp one_pos h1_valid)
        obtain ⟨η, hη, hη_eq⟩ := gamma_mul fp i.val 1 Θ ρ hΘ hρ_γ1 hi1_valid
        rw [show (1+Θ)*(1+ρ) - 1 = η by linarith [hη_eq]]
        exact le_trans hη (gamma_mono fp (by omega) hn1)
      -- For each j<i: |(1+θ_j)(1+ρ)-1| ≤ γ(n+1)
      have hη_bound : ∀ j : Fin n, j.val < i.val →
          |(1+θ j)*(1+ρ) - 1| ≤ γ := by
        intro j _
        have hθj : |θ j| ≤ gamma fp (i.val + 1) := hθ j
        have h1_valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
        have hi2_valid : gammaValid fp (i.val + 1 + 1) := gammaValid_mono fp (by omega) hn1
        have hρ_γ1 : |ρ| ≤ gamma fp 1 :=
          le_trans hρ (u_le_gamma fp one_pos h1_valid)
        obtain ⟨η, hη, hη_eq⟩ := gamma_mul fp (i.val + 1) 1 (θ j) ρ hθj hρ_γ1 hi2_valid
        rw [show (1+θ j)*(1+ρ) - 1 = η by linarith [hη_eq]]
        exact le_trans hη (gamma_mono fp (by omega) hn1)
      -- |(1+θ_j)(1+ρ)| ≤ 1 + γ
      have hξ_bound : ∀ j : Fin n, j.val < i.val →
          |(1+θ j)*(1+ρ)| ≤ 1 + γ := by
        intro j hj
        have : |(1+θ j)*(1+ρ)| = |(1+θ j)*(1+ρ) - 1 + 1| := by ring_nf
        rw [this]
        set a := (1+θ j)*(1+ρ) - 1 with ha_def
        -- |a + 1| ≤ |a| + 1 (triangle inequality workaround)
        have hab : |a + 1| ≤ |a| + 1 := by
          by_cases h : 0 ≤ a + 1
          · rw [abs_of_nonneg h]; linarith [le_abs_self a]
          · push_neg at h; rw [abs_of_neg h]; linarith [neg_abs_le a]
        linarith [hη_bound j hj]
      -- Main bound: split x̂_j(1+θ_j)(1+ρ) - x_j = -(x_j-x̂_j)(1+θ_j)(1+ρ) + x_j((1+θ_j)(1+ρ)-1)
      -- |L_ii| |x_i - x̂_i| ≤ |α| |b_i| + Σ |L_ij|(|(x_j-x̂_j)| · |(1+θ_j)(1+ρ)| + |x_j| · |η_j|)
      -- ≤ γ |b_i| + Σ |L_ij|((1+γ) |x_j - x̂_j| + γ |x_j|)
      -- By IH and |x_j| ≤ y_j:
      -- ≤ γ |b_i| + Σ |L_ij|((1+γ) μ_{i-1} y_j + γ y_j)
      -- = γ |b_i| + ((1+γ)μ_{i-1} + γ) Σ |L_ij| y_j
      -- = γ |b_i| + μ_i Σ |L_ij| y_j
      -- ≤ μ_i (|b_i| + Σ |L_ij| y_j)  [since γ ≤ μ_i for i ≥ 1]
      -- = μ_i · |L_ii| y_i   [comparison matrix row equation]
      -- Triangle inequality on the difference
      have htri : |L i i| * |x i - x_hat i| ≤
          γ * |b i| +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
            |L i j| * ((1+γ) * |x j - x_hat j| + γ * |x j|) := by
        calc |L i i| * |x i - x_hat i|
            = |L i i * (x i - x_hat i)| := (abs_mul _ _).symm
          _ = |b i * (1 - (1+Θ)*(1+ρ)) +
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                L i j * (x_hat j * (1+θ j) * (1+ρ) - x j)| := by rw [hdiff]
          _ ≤ |b i * (1 - (1+Θ)*(1+ρ))| +
              |∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                L i j * (x_hat j * (1+θ j) * (1+ρ) - x j)| := by
              -- |a + b| ≤ |a| + |b| (triangle inequality workaround)
              have hp := le_abs_self (b i * (1 - (1+Θ)*(1+ρ)))
              have hq := le_abs_self (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                L i j * (x_hat j * (1+θ j) * (1+ρ) - x j))
              have hnp := neg_abs_le (b i * (1 - (1+Θ)*(1+ρ)))
              have hnq := neg_abs_le (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                L i j * (x_hat j * (1+θ j) * (1+ρ) - x j))
              by_cases hpq : 0 ≤ b i * (1 - (1+Θ)*(1+ρ)) +
                ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                  L i j * (x_hat j * (1+θ j) * (1+ρ) - x j)
              · rw [abs_of_nonneg hpq]; linarith
              · push_neg at hpq; rw [abs_of_neg hpq]; linarith
          _ ≤ |b i| * |(1+Θ)*(1+ρ) - 1| +
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                |L i j * (x_hat j * (1+θ j) * (1+ρ) - x j)| := by
              have h1 : |b i * (1 - (1+Θ)*(1+ρ))| = |b i| * |(1+Θ)*(1+ρ) - 1| := by
                rw [show (1 - (1+Θ)*(1+ρ)) = -((1+Θ)*(1+ρ) - 1) by ring]
                rw [abs_mul, abs_neg]
              have h2 : |∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                    L i j * (x_hat j * (1+θ j) * (1+ρ) - x j)| ≤
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                    |L i j * (x_hat j * (1+θ j) * (1+ρ) - x j)| :=
                Finset.abs_sum_le_sum_abs _ _
              linarith
          _ ≤ γ * |b i| +
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                |L i j| * ((1+γ) * |x j - x_hat j| + γ * |x j|) := by
              apply add_le_add
              · -- |b i| * |(1+Θ)*(1+ρ) - 1| ≤ γ * |b i|
                linarith [mul_le_mul_of_nonneg_left hα_bound (abs_nonneg (b i)),
                  mul_comm (|b i|) (|(1+Θ)*(1+ρ) - 1|),
                  mul_comm γ (|b i|)]
              · -- bound each term in sum
                apply Finset.sum_le_sum
                intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                -- split: x̂_j(1+θ_j)(1+ρ) - x_j = -(x_j-x̂_j)(1+θ_j)(1+ρ) + x_j((1+θ_j)(1+ρ)-1)
                have hdecomp : x_hat j * (1+θ j) * (1+ρ) - x j =
                    -(x j - x_hat j) * ((1+θ j)*(1+ρ)) + x j * ((1+θ j)*(1+ρ) - 1) := by ring
                rw [abs_mul, hdecomp]
                have habs_tri : |-(x j - x_hat j) * ((1+θ j)*(1+ρ)) + x j * ((1+θ j)*(1+ρ) - 1)| ≤
                    |x j - x_hat j| * (1+γ) + |x j| * γ := by
                  have ht1 : |-(x j - x_hat j) * ((1+θ j)*(1+ρ))| =
                      |x j - x_hat j| * |(1+θ j)*(1+ρ)| := by rw [abs_mul, abs_neg]
                  have ht2 : |x j * ((1+θ j)*(1+ρ) - 1)| = |x j| * |(1+θ j)*(1+ρ) - 1| :=
                    abs_mul _ _
                  have hb1 : |x j - x_hat j| * |(1+θ j)*(1+ρ)| ≤ |x j - x_hat j| * (1+γ) :=
                    mul_le_mul_of_nonneg_left (hξ_bound j hj) (abs_nonneg _)
                  have hb2 : |x j| * |(1+θ j)*(1+ρ) - 1| ≤ |x j| * γ :=
                    mul_le_mul_of_nonneg_left (hη_bound j hj) (abs_nonneg _)
                  -- |p' + q'| ≤ |p'| + |q'| ≤ RHS
                  have hp' := le_abs_self (-(x j - x_hat j) * ((1+θ j)*(1+ρ)))
                  have hq' := le_abs_self (x j * ((1+θ j)*(1+ρ) - 1))
                  have hnp' := neg_abs_le (-(x j - x_hat j) * ((1+θ j)*(1+ρ)))
                  have hnq' := neg_abs_le (x j * ((1+θ j)*(1+ρ) - 1))
                  by_cases hpq' : 0 ≤ -(x j - x_hat j) * ((1+θ j)*(1+ρ)) + x j * ((1+θ j)*(1+ρ) - 1)
                  · rw [abs_of_nonneg hpq']; linarith [ht1, ht2, hb1, hb2]
                  · push_neg at hpq'; rw [abs_of_neg hpq']; linarith [ht1, ht2, hb1, hb2]
                calc |L i j| * |-(x j - x_hat j) * ((1+θ j)*(1+ρ)) + x j * ((1+θ j)*(1+ρ) - 1)|
                    ≤ |L i j| * (|x j - x_hat j| * (1+γ) + |x j| * γ) :=
                      mul_le_mul_of_nonneg_left habs_tri (abs_nonneg _)
                  _ = |L i j| * ((1+γ) * |x j - x_hat j| + γ * |x j|) := by ring
      -- Final assembly: from htri, use IH and comparison matrix row equation
      -- i.val = d + 1 (since i.val ≤ d+1 and i.val > d)
      have hi_eq : i.val = d + 1 := by omega
      have hLii_pos : 0 < |L i i| := abs_pos.mpr (hL_diag i)
      -- mu_{d+1} = (1+γ) * mu_d + γ
      have hmu_eq : mu fp n (d + 1) = (1 + γ) * mu fp n d + γ := by simp [mu, hγ_def]
      -- For j < i, j.val ≤ d, so by IH: |x j - x̂ j| ≤ mu fp n j.val * y j
      -- Also mu fp n j.val ≤ mu fp n d (by mu_mono iterated)
      have hmu_mono : ∀ k1 k2 : ℕ, k1 ≤ k2 → mu fp n k1 ≤ mu fp n k2 := by
        intro k1 k2 hle
        induction hle with
        | refl => exact le_refl _
        | step hle' ih => exact le_trans ih (mu_mono fp n hn1 _)
      -- Apply IH for each j < i
      have hj_bound : ∀ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
          |x j - x_hat j| ≤ mu fp n d * y j := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hjd : j.val ≤ d := by omega
        have := ih j (by omega)
        exact le_trans this (mul_le_mul_of_nonneg_right (hmu_mono j.val d hjd) (hy_nn j))
      -- Bound the sum
      calc |x i - x_hat i|
          ≤ (γ * |b i| +
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                |L i j| * ((1+γ) * |x j - x_hat j| + γ * |x j|)) / |L i i| := by
              rw [le_div_iff₀ hLii_pos]
              linarith [htri]
        _ ≤ (γ * |b i| +
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                |L i j| * ((1+γ) * (mu fp n d * y j) + γ * y j)) / |L i i| := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hLii_pos)
              have hsum_ineq :
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                    |L i j| * ((1+γ) * |x j - x_hat j| + γ * |x j|) ≤
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                    |L i j| * ((1+γ) * (mu fp n d * y j) + γ * y j) := by
                apply Finset.sum_le_sum; intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                have hih_j := hj_bound j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
                have hxle := hx_le_y j
                linarith [abs_nonneg (x j - x_hat j), mu_nonneg fp n hn1 d,
                  mul_nonneg (show (0:ℝ) ≤ 1+γ by linarith) (hy_nn j),
                  mul_le_mul_of_nonneg_left hih_j (show (0:ℝ) ≤ 1+γ by linarith),
                  mul_le_mul_of_nonneg_left hxle hγ_nn]
              linarith
        _ = (γ * |b i| +
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                |L i j| * (((1+γ) * mu fp n d + γ) * y j)) / |L i i| := by
              congr 2; apply Finset.sum_congr rfl; intro j _; ring
        _ = (γ * |b i| + mu fp n (d+1) *
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                |L i j| * y j) / |L i i| := by
              rw [hmu_eq]
              congr 2
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ (mu fp n (d+1) * |b i| + mu fp n (d+1) *
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                |L i j| * y j) / |L i i| := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hLii_pos)
              gcongr
              exact gamma_le_mu_succ fp n hn1 d
        _ = mu fp n (d+1) * (|b i| +
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
                |L i j| * y j) / |L i i| := by ring_nf
        _ = mu fp n (d+1) * (|L i i| * y i) / |L i i| := by
              rw [← hrow i]
        _ = mu fp n (d+1) * y i := by field_simp
        _ = mu fp n i.val * y i := by rw [hi_eq]

/-- Exact solution satisfies `|x_i| ≤ (M(U)⁻¹|b|)_i` componentwise for an
    upper-triangular system.  This is the upper-triangular analogue of
    `exact_solution_le_comp_inv_abs_b`. -/
lemma exact_upper_solution_le_comp_inv_abs_b (n : ℕ)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, U i j * x j = b i) :
    ∀ i, |x i| ≤ ∑ j : Fin n, M_inv i j * |b j| := by
  have habs := abs_inv_le_compMatrix_inv n U U_inv M_inv hUT hU_diag hInv
    hM_RInv hM_inv_ut
  intro i
  have hx : x i = ∑ j : Fin n, U_inv i j * b j := by
    have hLI := hInv.1 i
    have : ∑ j : Fin n, U_inv i j * b j =
        ∑ j : Fin n, U_inv i j * (∑ k : Fin n, U j k * x k) := by
      congr 1
      funext j
      rw [hTx j]
    rw [this]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have hsimp : ∀ k : Fin n,
        (∑ j : Fin n, U_inv i j * U j k) * x k =
          (if i = k then 1 else 0) * x k := by
      intro k
      congr 1
      exact hLI k
    simp_rw [hsimp]
    simp [Finset.mem_univ]
  rw [hx]
  calc
    |∑ j : Fin n, U_inv i j * b j|
        ≤ ∑ j : Fin n, |U_inv i j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |U_inv i j| * |b j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact abs_mul _ _
    _ ≤ ∑ j : Fin n, M_inv i j * |b j| := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (habs i j) (abs_nonneg _)

/-- An upper-triangular row sum over `univ.erase i` only sees the strict-upper
    entries. -/
private lemma upperTriangular_erase_sum_eq_strictUpper (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (i : Fin n) (v : Fin n → ℝ) :
    ∑ j ∈ Finset.univ.erase i, T i j * v j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * v j := by
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
  · intro j hj hnot
    rw [Finset.mem_erase] at hj
    have hnot' : ¬ i.val < j.val := by
      intro hij
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    have hji : j.val < i.val := by
      by_contra hge
      push_neg at hge
      exact hj.1 (Fin.ext (by omega))
    rw [hUT i j hji, zero_mul]

/-- Row equation for `(M(U)⁻¹ |b|)_i` in the upper-triangular case:
    `|U_ii| y_i = |b_i| + Σ_{j>i} |U_ij| y_j`. -/
lemma compMatrix_inv_upper_row_eq (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (_hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0)
    (i : Fin n) :
    let y := fun i => ∑ j : Fin n, M_inv i j * |b j|
    |U i i| * y i = |b i| +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
        |U i j| * y j := by
  intro y
  have hMy : ∀ i', ∑ k : Fin n, comparisonMatrix n U i' k * y k = |b i'| := by
    intro i'
    simp only [y]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    conv_rhs =>
      rw [show |b i'| = ∑ j : Fin n, (if i' = j then 1 else 0) * |b j| by
        simp [Finset.mem_univ]]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact hM_RInv i' j
  have hrow := hMy i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hrow
  have hM_ii : comparisonMatrix n U i i = |U i i| := by
    simp [comparisonMatrix]
  rw [hM_ii] at hrow
  have hrest :
      ∑ k ∈ Finset.univ.erase i, comparisonMatrix n U i k * y k =
        -(∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
          |U i j| * y j) := by
    have herase_eq :
        ∑ k ∈ Finset.univ.erase i, comparisonMatrix n U i k * y k =
          ∑ k ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
            comparisonMatrix n U i k * y k := by
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
      · intro k hk hknot
        rw [Finset.mem_erase] at hk
        have hknot' : ¬ i.val < k.val := by
          intro hc
          exact hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
        have hlt : k.val < i.val := by
          by_contra hle
          push_neg at hle
          exact hk.1 (Fin.ext (by omega))
        unfold comparisonMatrix
        simp [show i ≠ k from Fin.ne_of_val_ne (by omega), hUT i k hlt, zero_mul]
    rw [herase_eq, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    unfold comparisonMatrix
    simp [show i ≠ k from Fin.ne_of_val_ne (by omega)]
  rw [hrest] at hrow
  linarith

/-- Theorem 8.10-style `μ`-bound for back substitution, proved directly for
    upper-triangular systems.  This is the upper-triangular comparison-matrix
    analogue of `forwardSub_forward_error_mu_bound`. -/
theorem backSub_forward_error_mu_bound (fp : FPModel) (n : ℕ)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1)) :
    let x_hat := fl_backSub fp n U b
    let y := fun i => ∑ j : Fin n, M_inv i j * |b j|
    ∀ i : Fin n, |x i - x_hat i| ≤ mu fp n (n - 1 - i.val) * y i := by
  intro x_hat y
  have hM_nn := upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
    (by
      intro i j hij
      unfold comparisonMatrix
      simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
    (by
      intro i
      simp [comparisonMatrix, hU_diag i])
    (by
      intro i j _
      simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)])
    hM_RInv hM_inv_ut
  have hy_nn : ∀ i, 0 ≤ y i := by
    intro i
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hM_nn i j) (abs_nonneg _)
  have hx_le_y := exact_upper_solution_le_comp_inv_abs_b n U U_inv M_inv x b
    hUT hU_diag hInv hM_RInv hM_inv_ut hTx
  have hspec := fl_backSub_satisfies_spec fp n U b hU_diag hn
  have hrow := compMatrix_inv_upper_row_eq n U M_inv b hUT hU_diag hM_RInv hM_inv_ut
  set γ := gamma fp (n + 1) with hγ_def
  have hγ_nn : 0 ≤ γ := gamma_nonneg fp hn1
  suffices h :
      ∀ d : ℕ, ∀ i : Fin n, n - 1 - i.val ≤ d →
        |x i - x_hat i| ≤ mu fp n (n - 1 - i.val) * y i from
    fun i => h (n - 1 - i.val) i (le_refl _)
  intro d
  induction d with
  | zero =>
      intro i hi
      have hi_last : i.val = n - 1 := by omega
      obtain ⟨Θ, ρ, θ, hΘ, hρ, _, hspec_eq⟩ := hspec i
      have hΘ' : |Θ| ≤ gamma fp 0 := by
        simpa [hi_last] using hΘ
      have hΘ0 : Θ = 0 := by
        have hg0 : gamma fp 0 = 0 := by
          unfold gamma
          simp
        rw [hg0] at hΘ'
        exact abs_eq_zero.mp (le_antisymm hΘ' (abs_nonneg Θ))
      have hfilt_empty :
          Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ = ∅ := by
        ext j
        simp
        omega
      simp only [hΘ0, hfilt_empty, Finset.sum_empty, sub_zero, add_zero, mul_one] at hspec_eq
      have hUx : U i i * x i = b i := by
        have hTxi := hTx i
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hTxi
        rw [upperTriangular_erase_sum_eq_strictUpper n U hUT i x] at hTxi
        rw [hfilt_empty, Finset.sum_empty, add_zero] at hTxi
        simpa using hTxi
      have hdiff : U i i * (x i - x_hat i) = -b i * ρ := by
        linarith
      have habs_eq : |U i i| * |x i - x_hat i| = |b i| * |ρ| := by
        rw [← abs_mul]
        conv_rhs => rw [← abs_neg (b i), ← abs_mul]
        exact congrArg _ hdiff
      have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
      have hbound : |x i - x_hat i| ≤ fp.u * (|b i| / |U i i|) := by
        have h1 : |U i i| * |x i - x_hat i| ≤ fp.u * |b i| := by
          nlinarith [habs_eq, mul_le_mul_of_nonneg_left hρ (abs_nonneg (b i))]
        calc
          |x i - x_hat i| = |U i i| * |x i - x_hat i| / |U i i| := by
            field_simp [ne_of_gt hUii_pos]
          _ ≤ fp.u * |b i| / |U i i| := by
            exact div_le_div_of_nonneg_right h1 (le_of_lt hUii_pos)
          _ = fp.u * (|b i| / |U i i|) := by
            rw [mul_div_assoc]
      have hrow_i := hrow i
      dsimp only at hrow_i
      rw [hfilt_empty] at hrow_i
      simp at hrow_i
      have hy_eq : y i = |b i| / |U i i| := by
        have := hrow_i
        field_simp [ne_of_gt hUii_pos] at this ⊢
        linarith
      have hmu0 : mu fp n (n - 1 - i.val) = fp.u := by
        simp [hi_last, mu]
      rw [hmu0]
      rw [hy_eq]
      linarith
  | succ d ih =>
      intro i hi
      by_cases htail : n - 1 - i.val ≤ d
      · exact ih i htail
      · have hi_eq : n - 1 - i.val = d + 1 := by omega
        have hi_theta_eq : n - i.val = d + 2 := by omega
        obtain ⟨Θ, ρ, θ, hΘ, hρ, hθ, hspec_eq⟩ := hspec i
        have hUx : U i i * x i =
            b i -
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                U i j * x j := by
          have hTxi := hTx i
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hTxi
          rw [upperTriangular_erase_sum_eq_strictUpper n U hUT i x] at hTxi
          linarith
        have hdiff : U i i * (x i - x_hat i) =
            b i * (1 - (1 + Θ) * (1 + ρ)) +
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j) := by
          have h1 : U i i * x_hat i =
              (b i * (1 + Θ) -
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    U i j * x_hat j * (1 + θ j)) * (1 + ρ) := hspec_eq
          have h2 : U i i * (x i - x_hat i) = U i i * x i - U i i * x_hat i := by
            ring
          rw [h2, hUx, h1]
          set S := Finset.univ.filter (fun j : Fin n => i.val < j.val) with hS_def
          have hexpand :
              (b i * (1 + Θ) - ∑ j ∈ S, U i j * x_hat j * (1 + θ j)) * (1 + ρ) =
                b i * (1 + Θ) * (1 + ρ) -
                  ∑ j ∈ S, (U i j * x_hat j * (1 + θ j) * (1 + ρ)) := by
            rw [sub_mul, Finset.sum_mul]
          rw [hexpand]
          have hcombine :
              ∑ j ∈ S, (U i j * x_hat j * (1 + θ j) * (1 + ρ)) -
                  ∑ j ∈ S, (U i j * x j) =
                ∑ j ∈ S, (U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
          linarith [hcombine]
        have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
        have hα_bound : |(1 + Θ) * (1 + ρ) - 1| ≤ γ := by
          have hΘ' : |Θ| ≤ gamma fp (d + 1) := by
            simpa [hi_eq] using hΘ
          have h1_valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
          have hρ_γ1 : |ρ| ≤ gamma fp 1 :=
            le_trans hρ (u_le_gamma fp one_pos h1_valid)
          have hd2_valid : gammaValid fp (d + 2) := gammaValid_mono fp (by omega) hn1
          obtain ⟨η, hη, hη_eq⟩ := gamma_mul fp (d + 1) 1 Θ ρ hΘ' hρ_γ1 hd2_valid
          rw [show (1 + Θ) * (1 + ρ) - 1 = η by linarith [hη_eq]]
          exact le_trans hη (gamma_mono fp (by omega) hn1)
        have hη_bound : ∀ j : Fin n, i.val < j.val →
            |(1 + θ j) * (1 + ρ) - 1| ≤ γ := by
          intro j hj
          have hθj : |θ j| ≤ gamma fp (d + 2) := by
            simpa [hi_theta_eq] using hθ j
          have h1_valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
          have hρ_γ1 : |ρ| ≤ gamma fp 1 :=
            le_trans hρ (u_le_gamma fp one_pos h1_valid)
          have hd3_valid : gammaValid fp (d + 3) := gammaValid_mono fp (by omega) hn1
          obtain ⟨η, hη, hη_eq⟩ := gamma_mul fp (d + 2) 1 (θ j) ρ hθj hρ_γ1 hd3_valid
          rw [show (1 + θ j) * (1 + ρ) - 1 = η by linarith [hη_eq]]
          exact le_trans hη (gamma_mono fp (by omega) hn1)
        have hξ_bound : ∀ j : Fin n, i.val < j.val →
            |(1 + θ j) * (1 + ρ)| ≤ 1 + γ := by
          intro j hj
          have : |(1 + θ j) * (1 + ρ)| = |(1 + θ j) * (1 + ρ) - 1 + 1| := by
            ring_nf
          rw [this]
          set a := (1 + θ j) * (1 + ρ) - 1 with ha_def
          have hab : |a + 1| ≤ |a| + 1 := by
            by_cases h : 0 ≤ a + 1
            · rw [abs_of_nonneg h]
              linarith [le_abs_self a]
            · push_neg at h
              rw [abs_of_neg h]
              linarith [neg_abs_le a]
          linarith [hη_bound j hj]
        have htri : |U i i| * |x i - x_hat i| ≤
            γ * |b i| +
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                |U i j| * ((1 + γ) * |x j - x_hat j| + γ * |x j|) := by
          calc
            |U i i| * |x i - x_hat i| = |U i i * (x i - x_hat i)| := (abs_mul _ _).symm
            _ = |b i * (1 - (1 + Θ) * (1 + ρ)) +
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j)| := by
                  rw [hdiff]
            _ ≤ |b i * (1 - (1 + Θ) * (1 + ρ))| +
                |∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j)| := by
                  have hp := le_abs_self (b i * (1 - (1 + Θ) * (1 + ρ)))
                  have hq := le_abs_self
                    (∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                      U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j))
                  have hnp := neg_abs_le (b i * (1 - (1 + Θ) * (1 + ρ)))
                  have hnq := neg_abs_le
                    (∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                      U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j))
                  by_cases hpq :
                      0 ≤ b i * (1 - (1 + Θ) * (1 + ρ)) +
                        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                          U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j)
                  · rw [abs_of_nonneg hpq]
                    linarith
                  · push_neg at hpq
                    rw [abs_of_neg hpq]
                    linarith
            _ ≤ |b i| * |(1 + Θ) * (1 + ρ) - 1| +
                ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                  |U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j)| := by
                  have h1 :
                      |b i * (1 - (1 + Θ) * (1 + ρ))| =
                        |b i| * |(1 + Θ) * (1 + ρ) - 1| := by
                    rw [show (1 - (1 + Θ) * (1 + ρ)) = -((1 + Θ) * (1 + ρ) - 1) by ring]
                    rw [abs_mul, abs_neg]
                  have h2 :
                      |∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                          U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j)| ≤
                        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                          |U i j * (x_hat j * (1 + θ j) * (1 + ρ) - x j)| :=
                    Finset.abs_sum_le_sum_abs _ _
                  linarith
            _ ≤ γ * |b i| +
                ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                  |U i j| * ((1 + γ) * |x j - x_hat j| + γ * |x j|) := by
                  apply add_le_add
                  · linarith [mul_le_mul_of_nonneg_left hα_bound (abs_nonneg (b i)),
                      mul_comm (|b i|) (|(1 + Θ) * (1 + ρ) - 1|),
                      mul_comm γ (|b i|)]
                  · apply Finset.sum_le_sum
                    intro j hj
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                    have hdecomp :
                        x_hat j * (1 + θ j) * (1 + ρ) - x j =
                          -(x j - x_hat j) * ((1 + θ j) * (1 + ρ)) +
                            x j * ((1 + θ j) * (1 + ρ) - 1) := by
                      ring
                    rw [abs_mul, hdecomp]
                    have habs_tri :
                        |-(x j - x_hat j) * ((1 + θ j) * (1 + ρ)) +
                            x j * ((1 + θ j) * (1 + ρ) - 1)| ≤
                          |x j - x_hat j| * (1 + γ) + |x j| * γ := by
                      have ht1 :
                          |-(x j - x_hat j) * ((1 + θ j) * (1 + ρ))| =
                            |x j - x_hat j| * |(1 + θ j) * (1 + ρ)| := by
                        rw [abs_mul, abs_neg]
                      have ht2 :
                          |x j * ((1 + θ j) * (1 + ρ) - 1)| =
                            |x j| * |(1 + θ j) * (1 + ρ) - 1| :=
                        abs_mul _ _
                      have hb1 :
                          |x j - x_hat j| * |(1 + θ j) * (1 + ρ)| ≤
                            |x j - x_hat j| * (1 + γ) :=
                        mul_le_mul_of_nonneg_left (hξ_bound j hj) (abs_nonneg _)
                      have hb2 :
                          |x j| * |(1 + θ j) * (1 + ρ) - 1| ≤ |x j| * γ :=
                        mul_le_mul_of_nonneg_left (hη_bound j hj) (abs_nonneg _)
                      have hp' := le_abs_self (-(x j - x_hat j) * ((1 + θ j) * (1 + ρ)))
                      have hq' := le_abs_self (x j * ((1 + θ j) * (1 + ρ) - 1))
                      have hnp' := neg_abs_le (-(x j - x_hat j) * ((1 + θ j) * (1 + ρ)))
                      have hnq' := neg_abs_le (x j * ((1 + θ j) * (1 + ρ) - 1))
                      by_cases hpq' :
                          0 ≤ -(x j - x_hat j) * ((1 + θ j) * (1 + ρ)) +
                            x j * ((1 + θ j) * (1 + ρ) - 1)
                      · rw [abs_of_nonneg hpq']
                        linarith [ht1, ht2, hb1, hb2]
                      · push_neg at hpq'
                        rw [abs_of_neg hpq']
                        linarith [ht1, ht2, hb1, hb2]
                    calc
                      |U i j| *
                          |-(x j - x_hat j) * ((1 + θ j) * (1 + ρ)) +
                            x j * ((1 + θ j) * (1 + ρ) - 1)|
                          ≤ |U i j| *
                              (|x j - x_hat j| * (1 + γ) + |x j| * γ) :=
                            mul_le_mul_of_nonneg_left habs_tri (abs_nonneg _)
                      _ = |U i j| * ((1 + γ) * |x j - x_hat j| + γ * |x j|) := by
                            ring
        have hmu_eq : mu fp n (d + 1) = (1 + γ) * mu fp n d + γ := by
          simp [mu, hγ_def]
        have hmu_mono : ∀ k1 k2 : ℕ, k1 ≤ k2 → mu fp n k1 ≤ mu fp n k2 := by
          intro k1 k2 hle
          induction hle with
          | refl => exact le_refl _
          | step hle' ih => exact le_trans ih (mu_mono fp n hn1 _)
        have hj_bound :
            ∀ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
              |x j - x_hat j| ≤ mu fp n d * y j := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hj_tail : n - 1 - j.val ≤ d := by omega
          have hih_j := ih j hj_tail
          exact le_trans hih_j
            (mul_le_mul_of_nonneg_right
              (hmu_mono (n - 1 - j.val) d hj_tail) (hy_nn j))
        calc
          |x i - x_hat i| ≤
              (γ * |b i| +
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    |U i j| * ((1 + γ) * |x j - x_hat j| + γ * |x j|)) / |U i i| := by
                rw [le_div_iff₀ hUii_pos]
                linarith [htri]
          _ ≤
              (γ * |b i| +
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    |U i j| * ((1 + γ) * (mu fp n d * y j) + γ * y j)) / |U i i| := by
                apply div_le_div_of_nonneg_right _ (le_of_lt hUii_pos)
                have hsum_ineq :
                    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                      |U i j| * ((1 + γ) * |x j - x_hat j| + γ * |x j|) ≤
                    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                      |U i j| * ((1 + γ) * (mu fp n d * y j) + γ * y j) := by
                  apply Finset.sum_le_sum
                  intro j hj
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                  have hih_j := hj_bound j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
                  have hxle := hx_le_y j
                  linarith [abs_nonneg (x j - x_hat j), mu_nonneg fp n hn1 d,
                    mul_nonneg (show (0 : ℝ) ≤ 1 + γ by linarith) (hy_nn j),
                    mul_le_mul_of_nonneg_left hih_j (show (0 : ℝ) ≤ 1 + γ by linarith),
                    mul_le_mul_of_nonneg_left hxle hγ_nn]
                linarith
          _ =
              (γ * |b i| +
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    |U i j| * (((1 + γ) * mu fp n d + γ) * y j)) / |U i i| := by
                congr 2
                apply Finset.sum_congr rfl
                intro j _
                ring
          _ =
              (γ * |b i| +
                  mu fp n (d + 1) *
                    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                      |U i j| * y j) / |U i i| := by
                rw [hmu_eq]
                congr 2
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
          _ ≤
              (mu fp n (d + 1) * |b i| +
                  mu fp n (d + 1) *
                    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                      |U i j| * y j) / |U i i| := by
                apply div_le_div_of_nonneg_right _ (le_of_lt hUii_pos)
                gcongr
                exact gamma_le_mu_succ fp n hn1 d
          _ = mu fp n (d + 1) *
                (|b i| +
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    |U i j| * y j) / |U i i| := by
                ring_nf
          _ = mu fp n (d + 1) * (|U i i| * y i) / |U i i| := by
                rw [← hrow i]
          _ = mu fp n (d + 1) * y i := by
                field_simp [ne_of_gt hUii_pos]
          _ = mu fp n (n - 1 - i.val) * y i := by
                rw [hi_eq]

end NumStability
