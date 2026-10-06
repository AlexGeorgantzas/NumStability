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

/-!
# Inverse bounds for triangular matrices

Reusable comparison-matrix and infinity-norm bounds for inverses of
triangular matrices.
-/

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Comparison matrix M(U)
-- ============================================================

/-- The comparison matrix M(U): m_ij = |u_ii| if i = j, -|u_ij| if i ≠ j.
    For a nonsingular triangular matrix, M(U) is an M-matrix. -/
noncomputable def comparisonMatrix (n : ℕ) (U : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => if i = j then |U i j| else -|U i j|

-- ============================================================
-- M-matrix inverse nonnegativity (triangular case)
-- ============================================================

/-- The inverse of an upper triangular M-matrix has nonneg entries.

    An upper triangular M-matrix has positive diagonal and nonpositive
    off-diagonal entries. Its inverse (also upper triangular) has all
    nonneg entries.

    Proof: By induction on j - i using the right-inverse recurrence.
    For j > i: T_ii * T_inv_ij = -∑ T_ik * T_inv_kj.
    Since T_ik ≤ 0 (off-diagonal) and T_inv_kj ≥ 0 (IH), the sum ≤ 0,
    so T_ii * T_inv_ij ≥ 0. With T_ii > 0, T_inv_ij ≥ 0. -/
theorem upper_tri_mmatrix_inv_nonneg (n : ℕ) (T T_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hRInv : IsRightInverse n T T_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → T_inv i j = 0) :
    ∀ i j : Fin n, 0 ≤ T_inv i j := by
  suffices h : ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
      0 ≤ T_inv i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij; rw [hInv_ut i j (by omega)]
  intro d
  induction d with
  | zero =>
    intro i j hdiff hij
    have heq : i = j := Fin.ext (by omega)
    subst heq
    -- Diagonal: T_ii * T_inv_ii = 1 from right inverse
    have hR := hRInv i i; simp at hR
    have hdiag : T i i * T_inv i i = 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hR
      suffices ∑ k ∈ Finset.univ.erase i, T i k * T_inv k i = 0 by linarith
      apply Finset.sum_eq_zero; intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      by_cases hlt : k.val < i.val
      · rw [hUT i k (by omega), zero_mul]
      · rw [hInv_ut k i (by
          rcases Nat.lt_or_ge i.val k.val with h | h
          · exact h
          · exact absurd (Fin.ext (by omega)) hki), mul_zero]
    have : 0 < T_inv i i := by
      by_contra hc; push_neg at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hT_diag_pos i)) hc]
    linarith
  | succ d' ih =>
    intro i j hdiff hij
    by_cases heq : i.val = j.val
    · exact ih i j (by omega) (by omega)
    · have hij' : i.val < j.val := by omega
      have hrec := inv_recurrence n T T_inv hUT (fun k => ne_of_gt (hT_diag_pos k))
        hRInv hInv_ut i j hij'
      have hsum_neg : ∑ k ∈ Finset.univ.filter
          (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
          T i k * T_inv k j ≤ 0 := by
        apply Finset.sum_nonpos; intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact mul_nonpos_of_nonpos_of_nonneg (hT_offdiag i k (by omega))
          (ih k j (by omega) (by omega))
      have h_prod_nn : 0 ≤ T i i * T_inv i j := by linarith
      have h1 : 0 ≤ T i i * T_inv i j / T i i :=
        div_nonneg h_prod_nn (le_of_lt (hT_diag_pos i))
      rwa [mul_div_cancel_left₀ (T_inv i j) (ne_of_gt (hT_diag_pos i))] at h1

-- ============================================================
-- Theorem 8.12: |U⁻¹| ≤ M(U)⁻¹ (first inequality, componentwise)
-- ============================================================

/-- **Theorem 8.12, first inequality** (Higham §8.3).

    For a nonsingular upper triangular U with inverse U_inv, and M_inv the
    inverse of M(U), we have |U_inv_ij| ≤ M_inv_ij componentwise.

    Proof by induction on j - i using recurrences. -/
theorem abs_inv_le_compMatrix_inv (n : ℕ) (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    ∀ i j : Fin n, |U_inv i j| ≤ M_inv i j := by
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  -- M(U) is an upper triangular M-matrix, so its inverse has nonneg entries
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i; simp [comparisonMatrix]; exact hU_diag i
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j _; simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij; unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_nn := upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
    hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  -- Now prove |U_inv_ij| ≤ M_inv_ij by induction on j - i
  suffices h : ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
      |U_inv i j| ≤ M_inv i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij
        rw [hInv_ut i j (by omega), hM_inv_ut i j (by omega), abs_zero]
  intro d
  induction d with
  | zero =>
    intro i j hdiff hij
    have heq : i = j := Fin.ext (by omega)
    subst heq
    -- |U_inv_ii| = 1/|U_ii| = M_inv_ii
    rw [inv_diag_entry n U U_inv hUT hU_diag hInv.1 hInv_ut, abs_div, abs_one]
    -- M_inv_ii = 1/|U_ii| = 1/M(U)_ii from right inverse equation
    have hMR := hM_RInv i i; simp at hMR
    have hM_diag : comparisonMatrix n U i i * M_inv i i = 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hMR
      suffices ∑ k ∈ Finset.univ.erase i, comparisonMatrix n U i k * M_inv k i = 0 by
        linarith
      apply Finset.sum_eq_zero; intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      by_cases hlt : k.val < i.val
      · rw [hM_ut i k (by omega), zero_mul]
      · rw [hM_inv_ut k i (by
          rcases Nat.lt_or_ge i.val k.val with h | h
          · exact h
          · exact absurd (Fin.ext (by omega)) hki), mul_zero]
    simp [comparisonMatrix] at hM_diag
    have : M_inv i i = 1 / |U i i| := by
      field_simp [ne_of_gt (abs_pos.mpr (hU_diag i))]; linarith
    rw [this]
  | succ d' ih =>
    intro i j hdiff hij
    by_cases heq : i.val = j.val
    · exact ih i j (by omega) (by omega)
    · have hij' : i.val < j.val := by omega
      -- Recurrence for U_inv: U_ii * U_inv_ij = -∑ U_ik * U_inv_kj
      have hrec_U := inv_recurrence n U U_inv hUT hU_diag hInv.2 hInv_ut i j hij'
      -- Similarly for M(U): M_ii * M_inv_ij + ∑ M_ik * M_inv_kj = 0
      have hrec_M := inv_recurrence n (comparisonMatrix n U) M_inv hM_ut
        (fun k => ne_of_gt (hM_diag_pos k)) hM_RInv hM_inv_ut i j hij'
      have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
      have hUii_ne : U i i ≠ 0 := hU_diag i
      -- From U recurrence: U_ii * U_inv_ij = -(∑ U_ik * U_inv_kj)
      have hU_prod : U i i * U_inv i j =
          -(∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            U i k * U_inv k j) := by linarith
      -- |U_inv_ij| = |U_ii * U_inv_ij| / |U_ii| = |∑...| / |U_ii|
      have habs_eq : |U_inv i j| =
          |∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            U i k * U_inv k j| / |U i i| := by
        have h1 : U_inv i j = -(∑ k ∈ Finset.univ.filter
            (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            U i k * U_inv k j) / U i i := by
          field_simp [hUii_ne]; linarith
        rw [h1, abs_div, abs_neg]
      -- comparisonMatrix n U i i = |U i i|
      have hM_ii : comparisonMatrix n U i i = |U i i| := by simp [comparisonMatrix]
      -- For i < k: comparisonMatrix n U i k = -|U i k|
      have hM_ik : ∀ k : Fin n, i.val < k.val →
          comparisonMatrix n U i k = -|U i k| := by
        intro k hik; unfold comparisonMatrix
        simp [show i ≠ k from Fin.ne_of_val_ne (by omega)]
      -- From M recurrence: |U_ii| * M_inv_ij = ∑ |U_ik| * M_inv_kj
      have hM_prod : |U i i| * M_inv i j =
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            |U i k| * M_inv k j := by
        -- hrec_M: M_ii * M_inv_ij + ∑ M_ik * M_inv_kj = 0
        -- Rewrite M_ik = -|U_ik| for i < k, M_ii = |U_ii|
        have hsum_rw : ∑ k ∈ Finset.univ.filter
            (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            comparisonMatrix n U i k * M_inv k j =
            -(∑ k ∈ Finset.univ.filter
            (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            |U i k| * M_inv k j) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hM_ik k hk.1]; ring
        rw [hM_ii] at hrec_M; rw [hsum_rw] at hrec_M; linarith
      -- |U_inv_ij| ≤ (∑ |U_ik| * |U_inv_kj|) / |U_ii|
      --            ≤ (∑ |U_ik| * M_inv_kj) / |U_ii|    (by IH)
      --            = M_inv_ij
      calc |U_inv i j|
          = |∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
              U i k * U_inv k j| / |U i i| := habs_eq
        _ ≤ (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
              |U i k * U_inv k j|) / |U i i| :=
            div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (le_of_lt hUii_pos)
        _ = (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
              |U i k| * |U_inv k j|) / |U i i| := by
            congr 1; apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
              |U i k| * M_inv k j) / |U i i| := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hUii_pos)
            apply Finset.sum_le_sum; intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            exact mul_le_mul_of_nonneg_left (ih k j (by omega) (by omega)) (abs_nonneg _)
        _ = M_inv i j := by
            rw [← hM_prod]; field_simp [ne_of_gt hUii_pos]

-- ============================================================
-- Algorithm 8.13: comparison-inverse row recurrence
-- ============================================================

/-- **Algorithm 8.13 row recurrence** (Higham §8.3).

    If `M_inv` is a right inverse of the comparison matrix `M(U)`, then the
    vector `y = M(U)⁻¹ e` satisfies exactly the recurrence used by Higham's
    Algorithm 8.13:

    `|u_ii| y_i = 1 + sum_{j>i} |u_ij| y_j`.

    This is exact algebra; no floating-point rounding is modeled here. -/
theorem compMatrix_inv_upper_row_eq_ones (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (i : Fin n) :
    let y := fun i => ∑ j : Fin n, M_inv i j
    |U i i| * y i = 1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
        |U i j| * y j := by
  intro y
  have hMy : ∀ i', ∑ k : Fin n, comparisonMatrix n U i' k * y k = 1 := by
    intro i'
    simp only [y]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs =>
      rw [show (1 : ℝ) =
          ∑ j : Fin n, (if i' = j then 1 else 0) by
        simp [Finset.mem_univ]]
    apply Finset.sum_congr rfl
    intro j _
    exact hM_RInv i' j
  have hrow := hMy i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hrow
  have hM_ii : comparisonMatrix n U i i = |U i i| := by
    simp [comparisonMatrix]
  rw [hM_ii] at hrow
  have hrest : ∑ k ∈ Finset.univ.erase i, comparisonMatrix n U i k * y k =
      -(∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
        |U i j| * y j) := by
    have herase_eq : ∑ k ∈ Finset.univ.erase i, comparisonMatrix n U i k * y k =
        ∑ k ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
          comparisonMatrix n U i k * y k := by
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
      · intro k hk hknot
        rw [Finset.mem_erase] at hk
        have hknot' : ¬(i.val < k.val) := by
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

-- ============================================================
-- Theorem 8.14: Row sum bounds under diagonal dominance
-- ============================================================

/-- **Theorem 8.14, lower-bound ingredient** (Higham §8.3).

    For a nonsingular upper triangular U, the row sum of |U⁻¹| at row i
    satisfies ∑_j |U_inv i j| ≥ 1/|U_ii|.

    In particular, max_i ∑_j |U_inv_ij| ≥ 1/min_k |U_kk|. -/
theorem triInv_row_sum_lowerBound (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv) :
    ∀ i : Fin n, 1 / |U i i| ≤ ∑ j : Fin n, |U_inv i j| := by
  intro i
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  have hdiag := inv_diag_entry n U U_inv hUT hU_diag hInv.1 hInv_ut
  calc 1 / |U i i|
      = |1 / U i i| := by rw [abs_div, abs_one]
    _ = |U_inv i i| := by rw [hdiag]
    _ ≤ ∑ j : Fin n, |U_inv i j| := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        linarith [abs_nonneg (U_inv i i),
          Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ.erase i) => abs_nonneg (U_inv i j))]

/-- **Theorem 8.14, upper-bound ingredient** (Higham §8.3).

    Under diagonal dominance (|U_ii| ≥ |U_ij| for j > i), the row sum
    of |U⁻¹| at row i satisfies
      ∑_j |U_inv i j| ≤ 2^{n-1-i} / min_k |U_kk|.

    In particular, ‖U⁻¹‖_∞ ≤ 2^{n-1} / min_k |U_kk|.

    Proof: Write V = D⁻¹U where D = diag(U_ii). Then V is unit upper
    triangular with |V_ij| ≤ 1, and |U_inv_ij| = |V_inv_ij| / |U_jj|.
    So ∑_j |U_inv_ij| ≤ (1/min_k |U_kk|) · ∑_j |V_inv_ij|
       ≤ (1/min_k |U_kk|) · 2^{n-1-i}   by inv_row_sum_bound. -/
theorem triInv_row_sum_upperBound (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    ∀ i : Fin n, ∑ j : Fin n, |U_inv i j| ≤
      2 ^ (n - 1 - i.val) *
        (1 / Finset.inf' Finset.univ ⟨i, Finset.mem_univ i⟩ (fun k => |U k k|)) := by
  obtain ⟨hUT, hU_diag, hU_dom⟩ := hDD
  obtain ⟨hLInv, _hRInv⟩ := hInv
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hLInv
  intro i
  -- Define V = D⁻¹U, V_inv = U_inv * D (same factoring as inv_abs_mul_bound_diagDom)
  let V : Fin n → Fin n → ℝ := fun a b => U a b / U a a
  let V_inv : Fin n → Fin n → ℝ := fun a b => U_inv a b * U b b
  -- V properties
  have hVT : ∀ a b : Fin n, b.val < a.val → V a b = 0 := by
    intro a b hab; simp only [V, hUT a b hab, zero_div]
  have hV_unit : ∀ a : Fin n, V a a = 1 := by
    intro a; simp only [V]; exact div_self (hU_diag a)
  have hV_bound : ∀ a b : Fin n, a.val < b.val → |V a b| ≤ 1 := by
    intro a b hab; simp only [V, abs_div]
    exact (div_le_one (abs_pos.mpr (hU_diag a))).mpr (hU_dom a b hab)
  -- V_inv properties
  have hVinv_ut : ∀ a b : Fin n, b.val < a.val → V_inv a b = 0 := by
    intro a b hab; simp only [V_inv, hInv_ut a b hab, zero_mul]
  have hVinv_diag : ∀ a : Fin n, V_inv a a = 1 := by
    intro a; simp only [V_inv]
    rw [inv_diag_entry n U U_inv hUT hU_diag hLInv hInv_ut a]
    field_simp [hU_diag a]
  -- V_inv is a left inverse of V
  have hVLInv : IsLeftInverse n V V_inv := by
    intro a b; simp only [V, V_inv]
    have h := hLInv a b
    have hsimp : ∑ k : Fin n, U_inv a k * U k k * (U k b / U k k) =
        ∑ k : Fin n, U_inv a k * U k b := by
      apply Finset.sum_congr rfl; intro k _
      have hk := hU_diag k; field_simp [hk]
    rw [hsimp]; exact h
  -- Key: |U_inv i j| = |V_inv i j| / |U j j|
  have hconv : ∀ j : Fin n, |U_inv i j| = |V_inv i j| / |U j j| := by
    intro j; simp only [V_inv, abs_mul]
    rw [mul_div_cancel_right₀ _ (ne_of_gt (abs_pos.mpr (hU_diag j)))]
  -- Let α = min_k |U_kk|
  let α := Finset.inf' Finset.univ ⟨i, Finset.mem_univ i⟩ (fun k => |U k k|)
  have hα_pos : 0 < α := by
    rw [Finset.lt_inf'_iff]; intro k _; exact abs_pos.mpr (hU_diag k)
  -- Each |U_inv i j| / 1 ≤ |V_inv i j| / α
  -- ∑ |U_inv i j| = ∑ |V_inv i j| / |U j j| ≤ (1/α) ∑ |V_inv i j|
  have hle : ∑ j : Fin n, |U_inv i j| ≤
      (1 / α) * ∑ j : Fin n, |V_inv i j| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    rw [hconv j]
    -- Goal: |V_inv i j| / |U j j| ≤ 1 / α * |V_inv i j|
    rw [← sub_nonneg]
    have hUj_ne : |U j j| ≠ 0 := ne_of_gt (abs_pos.mpr (hU_diag j))
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    have : 1 / α * |V_inv i j| - |V_inv i j| / |U j j| =
        |V_inv i j| * (|U j j| - α) / (α * |U j j|) := by
      field_simp [hα_ne, hUj_ne]
    rw [this]
    apply div_nonneg
    · apply mul_nonneg (abs_nonneg _)
      linarith [Finset.inf'_le (fun k => |U k k|) (Finset.mem_univ j)]
    · exact le_of_lt (mul_pos hα_pos (abs_pos.mpr (hU_diag j)))
  -- ∑ |V_inv i j| ≤ 2^{n-1-i} (V_inv upper tri, then inv_row_sum_bound)
  have hV_sum : ∑ j : Fin n, |V_inv i j| ≤ 2 ^ (n - 1 - i.val) := by
    -- Split: j < i gives 0, j ≥ i bounded by inv_row_sum_bound
    have hsplit : ∑ j : Fin n, |V_inv i j| =
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val), |V_inv i j| := by
      symm; apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      rw [hVinv_ut i j hj, abs_zero]
    rw [hsplit]
    -- Need j.val ≤ n-1 for the last valid index
    by_cases hn : n = 0
    · subst hn; exact absurd i.isLt (by omega)
    · have hn' : 0 < n := by omega
      have hfilt_eq : Finset.univ.filter (fun j : Fin n => i.val ≤ j.val) =
          Finset.univ.filter (fun j : Fin n => i.val ≤ j.val ∧
            j.val ≤ (⟨n - 1, by omega⟩ : Fin n).val) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨h, by omega⟩, fun ⟨h, _⟩ => h⟩
      rw [hfilt_eq]
      exact inv_row_sum_bound n V V_inv hVT hV_unit hV_bound hVLInv hVinv_ut hVinv_diag
        (n - 1 - i.val) i ⟨n - 1, by omega⟩ (by simp) (by simp; omega)
  calc ∑ j : Fin n, |U_inv i j|
      ≤ (1 / α) * ∑ j : Fin n, |V_inv i j| := hle
    _ ≤ (1 / α) * 2 ^ (n - 1 - i.val) :=
        mul_le_mul_of_nonneg_left hV_sum (by positivity)
    _ = 2 ^ (n - 1 - i.val) * (1 / α) := by ring

/-- **Higham Theorem 8.14, matrix ∞-norm form**.

    Under the repository's diagonal-dominance hypothesis for an upper
    triangular matrix, the row-sum theorem gives the usual
    `‖U⁻¹‖∞ ≤ 2^(n-1) / min_i |u_ii|` estimate.  The explicit index `i0`
    supplies the nonempty witness for the finite minimum. -/
theorem triInv_infNorm_upperBound (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    infNorm U_inv ≤
      2 ^ (n - 1) *
        (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k => |U k k|)) := by
  classical
  have hU_diag : ∀ i : Fin n, U i i ≠ 0 := hDD.2.1
  let α : ℝ :=
    Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|)
  have hα_pos : 0 < α := by
    rw [Finset.lt_inf'_iff]
    intro k _
    exact abs_pos.mpr (hU_diag k)
  apply infNorm_le_of_row_sum_le
  · intro i
    have hrow := triInv_row_sum_upperBound n U U_inv hDD hInv i
    have hmin_eq :
        Finset.inf' Finset.univ ⟨i, Finset.mem_univ i⟩
            (fun k : Fin n => |U k k|) = α := by
      apply le_antisymm
      · apply Finset.le_inf'
        intro r hr
        exact Finset.inf'_le (f := fun k : Fin n => |U k k|) hr
      · unfold α
        apply Finset.le_inf'
        intro r hr
        exact Finset.inf'_le (f := fun k : Fin n => |U k k|) hr
    rw [hmin_eq] at hrow
    have hpow :
        (2 : ℝ) ^ (n - 1 - i.val) ≤ (2 : ℝ) ^ (n - 1) := by
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le (n - 1) i.val)
    have hinv_nonneg : 0 ≤ 1 / α :=
      div_nonneg zero_le_one (le_of_lt hα_pos)
    calc
      ∑ j : Fin n, |U_inv i j|
          ≤ 2 ^ (n - 1 - i.val) * (1 / α) := hrow
      _ ≤ 2 ^ (n - 1) * (1 / α) :=
          mul_le_mul_of_nonneg_right hpow hinv_nonneg
  · exact mul_nonneg (by positivity) (div_nonneg zero_le_one (le_of_lt hα_pos))

/-- Squared budget form of `triInv_infNorm_upperBound`.

    This is the form used by the QR bottleneck route: if the advertised
    budget `K` dominates the Higham ∞-norm estimate squared, then it also
    dominates `(n : ℝ) * ‖U⁻¹‖∞²`. -/
theorem triInv_infNorm_sq_budget_of_diagDominantUpper (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n) (K : ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv)
    (hK :
      (n : ℝ) *
          (2 ^ (n - 1) *
            (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k => |U k k|))) ^ 2 ≤ K) :
    (n : ℝ) * infNorm U_inv ^ 2 ≤ K := by
  classical
  have hU_diag : ∀ i : Fin n, U i i ≠ 0 := hDD.2.1
  let α : ℝ :=
    Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|)
  let B : ℝ := 2 ^ (n - 1) * (1 / α)
  have hα_pos : 0 < α := by
    rw [Finset.lt_inf'_iff]
    intro k _
    exact abs_pos.mpr (hU_diag k)
  have hB_nonneg : 0 ≤ B := by
    exact mul_nonneg (by positivity) (div_nonneg zero_le_one (le_of_lt hα_pos))
  have hnorm : infNorm U_inv ≤ B := by
    simpa [B, α] using triInv_infNorm_upperBound n U U_inv i0 hDD hInv
  have hsquare : infNorm U_inv ^ 2 ≤ B ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg (infNorm_nonneg U_inv), abs_of_nonneg hB_nonneg]
        using hnorm)
  have hmul : (n : ℝ) * infNorm U_inv ^ 2 ≤ (n : ℝ) * B ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg n)
  exact hmul.trans (by simpa [B, α] using hK)

/-- Determinant-facing form of the diagonal-dominant triangular inverse
    budget.  A nonzero determinant supplies the repository nonsingular inverse,
    so callers do not need to pass an explicit inverse witness. -/
theorem triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero (n : ℕ)
    (U : Fin n → Fin n → ℝ)
    (i0 : Fin n) (K : ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hdet : Matrix.det (U : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hK :
      (n : ℝ) *
          (2 ^ (n - 1) *
            (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k => |U k k|))) ^ 2 ≤ K) :
    (n : ℝ) * infNorm (nonsingInv n U) ^ 2 ≤ K :=
  triInv_infNorm_sq_budget_of_diagDominantUpper n U (nonsingInv n U)
    i0 K hDD (isInverse_nonsingInv_of_det_ne_zero n U hdet) hK

/-- The explicit squared inverse-∞ budget produced by Higham's
    diagonal-dominant triangular inverse estimate. -/
noncomputable def diagDominantUpperInvBudgetExpr (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i0 : Fin n) : ℝ :=
  (n : ℝ) *
    (2 ^ (n - 1) *
      (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
        (fun k : Fin n => |U k k|))) ^ 2

/-- The explicit diagonal-dominant inverse budget is positive. -/
theorem diagDominantUpperInvBudgetExpr_pos (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i0 : Fin n)
    (hDD : IsDiagDominantUpper n U) :
    0 < diagDominantUpperInvBudgetExpr n U i0 := by
  classical
  have hn_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le i0.val) i0.isLt
  have hn : (0 : ℝ) < n := by exact_mod_cast hn_nat
  let α : ℝ :=
    Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|)
  have hα : 0 < α := by
    rw [Finset.lt_inf'_iff]
    intro k _
    exact abs_pos.mpr (hDD.2.1 k)
  have hpow : 0 < (2 : ℝ) ^ (n - 1) := pow_pos (by norm_num) _
  have hinv : 0 < 1 / α := one_div_pos.mpr hα
  have hbudget : 0 <
      2 ^ (n - 1) *
        (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k : Fin n => |U k k|)) := by
    simpa [α] using mul_pos hpow hinv
  unfold diagDominantUpperInvBudgetExpr
  exact mul_pos hn (sq_pos_of_pos hbudget)

/-- Determinant-facing diagonal-dominant inverse budget with the concrete
    auxiliary value `K = 2 * D`, where `D` is the displayed Higham budget. -/
theorem triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero_twice_budget
    (n : ℕ) (U : Fin n → Fin n → ℝ) (i0 : Fin n)
    (hDD : IsDiagDominantUpper n U)
    (hdet : Matrix.det (U : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    (n : ℝ) * infNorm (nonsingInv n U) ^ 2 ≤
      2 * diagDominantUpperInvBudgetExpr n U i0 := by
  classical
  refine
    triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero
      n U i0 (2 * diagDominantUpperInvBudgetExpr n U i0)
      hDD hdet ?_
  have hD_nonneg :
      0 ≤ diagDominantUpperInvBudgetExpr n U i0 :=
    le_of_lt (diagDominantUpperInvBudgetExpr_pos n U i0 hDD)
  have hle :
      diagDominantUpperInvBudgetExpr n U i0 ≤
        2 * diagDominantUpperInvBudgetExpr n U i0 := by
    linarith
  simpa [diagDominantUpperInvBudgetExpr] using hle

/-- Product-form sufficient condition for the direct compact smallness
    inequality used by the concrete dual-budget QR route. -/
theorem mul_sq_lt_inv_two_mul_of_two_mul_mul_sq_lt_one
    {m B D : ℝ} (hD : 0 < D)
    (hsmall : 2 * D * (m * B ^ 2) < 1) :
    m * B ^ 2 < 1 / (2 * D) := by
  have hden : 0 < 2 * D := by nlinarith
  rw [lt_div_iff₀ hden]
  nlinarith [hsmall]

/-- Monotone replacement for the product-form compact smallness condition.

    If a nonnegative local compact budget is bounded by a larger nonnegative
    computed-loop budget, then product smallness for the larger budget implies
    product smallness for the local one. -/
theorem two_mul_mul_sq_lt_one_of_nonneg_le
    {D m b B : ℝ}
    (hD : 0 ≤ D) (hm : 0 ≤ m) (hb : 0 ≤ b) (hbB : b ≤ B)
    (hsmall : 2 * D * (m * B ^ 2) < 1) :
    2 * D * (m * b ^ 2) < 1 := by
  have hB : 0 ≤ B := le_trans hb hbB
  have hsq : b ^ 2 ≤ B ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg hb, abs_of_nonneg hB] using hbB)
  have hmul : m * b ^ 2 ≤ m * B ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hm
  have hprod : 2 * D * (m * b ^ 2) ≤ 2 * D * (m * B ^ 2) :=
    mul_le_mul_of_nonneg_left hmul (by nlinarith)
  exact lt_of_le_of_lt hprod hsmall

/-- Positivity of the inverse budget alone does not imply the product-form
    compact smallness condition. The missing QR hypothesis must include a
    genuine bound on the compact update budget, not just `D > 0`. -/
theorem not_forall_pos_implies_two_mul_mul_sq_lt_one :
    ¬ (∀ D B : ℝ, 0 < D → 2 * D * ((1 : ℝ) * B ^ 2) < 1) := by
  intro h
  have hbad := h 1 1 (by norm_num)
  norm_num at hbad

/-- Diagonal dominance and the displayed Higham inverse budget still do not
    imply the product-form compact smallness condition without a genuine bound
    on the compact update budget.  Even the `1 x 1` identity block fails if the
    compact budget is chosen as `B = 1`. -/
theorem not_forall_diagDominantUpper_implies_two_mul_budget_expr_mul_sq_lt_one :
    ¬ (∀ U : Fin 1 → Fin 1 → ℝ, IsDiagDominantUpper 1 U →
        ∀ i0 : Fin 1,
          2 * diagDominantUpperInvBudgetExpr 1 U i0 *
              ((1 : ℝ) * (1 : ℝ) ^ 2) < 1) := by
  intro h
  let U : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
  have hDD : IsDiagDominantUpper 1 U := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hji
      fin_cases i
      fin_cases j
      omega
    · intro i
      fin_cases i
      norm_num [U]
    · intro i j hij
      fin_cases i
      fin_cases j
      omega
  have hbad := h U hDD ⟨0, by norm_num⟩
  norm_num [diagDominantUpperInvBudgetExpr, U] at hbad

/-- Product compact smallness plus upper-triangular nonsingularity still does
    not imply diagonal dominance.

    The witness is the same `2 x 2` matrix `[[1,2],[0,1]]` from
    `TriangularForwardBound.lean`.  Its leading diagonal entries make the
    displayed diagonal-dominant inverse budget finite, and the compact budget
    can be chosen small enough to satisfy the product inequality, but the block
    is not diagonally dominant.  Thus the remaining QR bottleneck cannot merge
    the product-smallness assumption into a proof of diagonal dominance. -/
theorem not_forall_upper_tri_det_ne_zero_product_budget_implies_diagDominant :
    ¬ (∀ (U : Fin 2 → Fin 2 → ℝ) (B : ℝ),
      (∀ i j : Fin 2, j.val < i.val → U i j = 0) →
      Matrix.det (U : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 →
      0 < B →
      2 * diagDominantUpperInvBudgetExpr 2 U ⟨0, by norm_num⟩ *
          ((1 : ℝ) * B ^ 2) < 1 →
      IsDiagDominantUpper 2 U) := by
  intro h
  have hdiagInf :
      Finset.inf' Finset.univ
          ⟨(⟨0, by norm_num⟩ : Fin 2), Finset.mem_univ _⟩
          (fun k : Fin 2 => |diagDominanceCounterexample2 k k|) = 1 := by
    apply Finset.inf'_eq_of_forall
    intro k _
    fin_cases k <;> norm_num [diagDominanceCounterexample2]
  have hprod :
      2 *
          diagDominantUpperInvBudgetExpr 2 diagDominanceCounterexample2
            ⟨0, by norm_num⟩ *
        ((1 : ℝ) * ((1 : ℝ) / 8) ^ 2) < 1 := by
    dsimp [diagDominantUpperInvBudgetExpr]
    rw [hdiagInf]
    norm_num
  exact
    diagDominanceCounterexample2_not_diagDominant
      (h diagDominanceCounterexample2 ((1 : ℝ) / 8)
        diagDominanceCounterexample2_upper
        diagDominanceCounterexample2_det_ne_zero
        (by norm_num)
        hprod)

/-- Upper-triangular nonsingularity plus a finite `κ∞` budget still does not
    imply the product-form compact smallness condition.

    The compact-update side condition cannot be recovered from conditioning
    data alone: the same nonsingular triangular witness `[[1,2],[0,1]]`
    satisfies a finite `κ∞` bound, but choosing compact budget `B = 1` makes
    the displayed product inequality false. -/
theorem not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_two_mul_budget_expr_mul_sq_lt_one :
    ¬ (∀ (U : Fin 2 → Fin 2 → ℝ) (κ B : ℝ),
      (∀ i j : Fin 2, j.val < i.val → U i j = 0) →
      Matrix.det (U : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 →
      kappaInf 2 (by norm_num : 0 < 2)
        (U : Matrix (Fin 2) (Fin 2) ℝ)
        (nonsingInv 2 (U : Matrix (Fin 2) (Fin 2) ℝ)) ≤ κ →
      0 < B →
      2 * diagDominantUpperInvBudgetExpr 2 U ⟨0, by norm_num⟩ *
          ((1 : ℝ) * B ^ 2) < 1) := by
  intro h
  have hdiagInf :
      Finset.inf' Finset.univ
          ⟨(⟨0, by norm_num⟩ : Fin 2), Finset.mem_univ _⟩
          (fun k : Fin 2 => |diagDominanceCounterexample2 k k|) = 1 := by
    apply Finset.inf'_eq_of_forall
    intro k _
    fin_cases k <;> norm_num [diagDominanceCounterexample2]
  let κ : ℝ :=
    kappaInf 2 (by norm_num : 0 < 2)
      (diagDominanceCounterexample2 : Matrix (Fin 2) (Fin 2) ℝ)
      (nonsingInv 2
        (diagDominanceCounterexample2 : Matrix (Fin 2) (Fin 2) ℝ))
  have hbad :=
    h diagDominanceCounterexample2 κ 1
      diagDominanceCounterexample2_upper
      diagDominanceCounterexample2_det_ne_zero
      (by rfl)
      (by norm_num)
  dsimp [diagDominantUpperInvBudgetExpr] at hbad
  rw [hdiagInf] at hbad
  norm_num at hbad

-- ============================================================
-- Lower triangular inverse infrastructure
-- ============================================================

/-- The left inverse of a lower triangular matrix is lower triangular.

    Proof by downward strong induction on j: for j > i, the left inverse equation
    ∑_k L_inv_ik * L_kj = 0 reduces to L_inv_ij * L_jj = 0
    because for k < j, L_kj = 0 (lower triangularity of L), and for k > j,
    L_inv_ik = 0 by the induction hypothesis (since i < j < k). -/
theorem inv_lower_tri (n : ℕ) (L L_inv : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hInv : IsLeftInverse n L L_inv) :
    ∀ i j : Fin n, i.val < j.val → L_inv i j = 0 := by
  -- Downward induction: prove for large j first using strong induction on (n - jv)
  suffices ∀ (d : ℕ), ∀ (jv : ℕ) (hjv : jv < n), n - jv ≤ d →
      ∀ i : Fin n, i.val < jv → L_inv i ⟨jv, hjv⟩ = 0 by
    intro i j hij; exact this (n - j.val) j.val j.isLt (le_refl _) i hij
  intro d
  induction d with
  | zero =>
    intro jv hjv hd i hi
    omega
  | succ d' ih =>
    intro jv hjv hd i hi
    let j : Fin n := ⟨jv, hjv⟩
    have hij : i ≠ j := Fin.ne_of_val_ne (by simp [j]; omega)
    have h := hInv i j
    simp [hij] at h
    have : L_inv i j * L j j = 0 := by
      suffices ∑ k : Fin n, L_inv i k * L k j = L_inv i j * L j j by linarith
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      suffices ∑ k ∈ Finset.univ.erase j, L_inv i k * L k j = 0 by linarith
      apply Finset.sum_eq_zero; intro k hk
      have hk_ne := Finset.ne_of_mem_erase hk
      by_cases hklt : k.val < jv
      · -- k < j: L_kj = 0 by lower triangularity
        rw [hLT k j (by simp [j]; exact hklt), mul_zero]
      · -- k > j: L_inv_ik = 0 by IH (i < j < k, and n - k < n - j)
        push_neg at hklt
        have hkgt : jv < k.val := by
          by_contra hc; push_neg at hc
          exact hk_ne (Fin.ext (by simp [j]; omega))
        rw [ih k.val k.isLt (by omega) i (by omega), zero_mul]
    exact (mul_eq_zero.mp this).elim id (fun h => absurd h (hL_diag _))

/-- Diagonal entries of the inverse of a lower triangular matrix: (L_inv)_ii = 1 / L_ii. -/
theorem inv_diag_entry_lower (n : ℕ) (L L_inv : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hInv : IsLeftInverse n L L_inv)
    (hInv_lt : ∀ i j : Fin n, i.val < j.val → L_inv i j = 0) :
    ∀ i : Fin n, L_inv i i = 1 / L i i := by
  intro i
  have h := hInv i i
  simp at h
  have honly : ∑ k : Fin n, L_inv i k * L k i = L_inv i i * L i i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    suffices ∑ k ∈ Finset.univ.erase i, L_inv i k * L k i = 0 by linarith
    apply Finset.sum_eq_zero; intro k hk
    have hki := Finset.ne_of_mem_erase hk
    by_cases hlt : i.val < k.val
    · rw [hInv_lt i k hlt, zero_mul]
    · push_neg at hlt
      rw [hLT k i (by omega), mul_zero]
  rw [honly] at h
  have hmul : L_inv i i * L i i = 1 := h
  have hne := hL_diag i
  field_simp [hne]
  linarith

/-- Recursive formula for off-diagonal entries of the inverse of a lower triangular
    matrix (right inverse form).
    For j < i: L_ii * L_inv_ij = -∑_{k: j ≤ k < i} L_ik * L_inv_kj. -/
theorem inv_recurrence_lower (n : ℕ) (L L_inv : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hRInv : IsRightInverse n L L_inv)
    (hInv_lt : ∀ i j : Fin n, i.val < j.val → L_inv i j = 0) :
    ∀ i j : Fin n, j.val < i.val →
      L i i * L_inv i j +
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
        L i k * L_inv k j = 0 := by
  intro i j hij
  have hR := hRInv i j
  simp [show i ≠ j from Fin.ne_of_val_ne (by omega)] at hR
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hR
  have hrest : ∑ k ∈ Finset.univ.erase i, L i k * L_inv k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
        L i k * L_inv k j := by
    symm; apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
    · intro k hk hknot
      rw [Finset.mem_erase] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hknot
      push_neg at hknot
      by_cases hlt : i.val ≤ k.val
      · rw [hLT i k (by omega), zero_mul]
      · push_neg at hlt
        rw [hInv_lt k j (by omega), mul_zero]
  rw [hrest] at hR; linarith

-- ============================================================
-- M-matrix inverse nonnegativity (lower triangular)
-- ============================================================

/-- The inverse of a lower triangular M-matrix has nonneg entries.

    Proof: by induction on i - j using the right-inverse recurrence.
    For i > j: L_ii * L_inv_ij = -∑ L_ik * L_inv_kj.
    Since L_ik ≤ 0 (off-diagonal, k < i) and L_inv_kj ≥ 0 (IH), the sum ≤ 0,
    so L_ii * L_inv_ij ≥ 0. With L_ii > 0, L_inv_ij ≥ 0. -/
theorem lower_tri_mmatrix_inv_nonneg (n : ℕ) (T T_inv : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, j.val < i.val → T i j ≤ 0)
    (hRInv : IsRightInverse n T T_inv)
    (hInv_lt : ∀ i j : Fin n, i.val < j.val → T_inv i j = 0) :
    ∀ i j : Fin n, 0 ≤ T_inv i j := by
  suffices h : ∀ (d : ℕ), ∀ i j : Fin n, i.val - j.val ≤ d → j.val ≤ i.val →
      0 ≤ T_inv i j from
    fun i j => by
      by_cases hij : j.val ≤ i.val
      · exact h (i.val - j.val) i j (le_refl _) hij
      · push_neg at hij; rw [hInv_lt i j (by omega)]
  intro d
  induction d with
  | zero =>
    intro i j hdiff hij
    have heq : i = j := Fin.ext (by omega)
    subst heq
    have hR := hRInv i i; simp at hR
    have hdiag : T i i * T_inv i i = 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hR
      suffices ∑ k ∈ Finset.univ.erase i, T i k * T_inv k i = 0 by linarith
      apply Finset.sum_eq_zero; intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      by_cases hlt : i.val < k.val
      · rw [hLT i k hlt, zero_mul]
      · rw [hInv_lt k i (by omega), mul_zero]
    have : 0 < T_inv i i := by
      by_contra hc; push_neg at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hT_diag_pos i)) hc]
    linarith
  | succ d' ih =>
    intro i j hdiff hij
    by_cases heq : i.val = j.val
    · exact ih i j (by omega) (by omega)
    · have hij' : j.val < i.val := by omega
      have hrec := inv_recurrence_lower n T T_inv hLT (fun k => ne_of_gt (hT_diag_pos k))
        hRInv hInv_lt i j hij'
      have hsum_neg : ∑ k ∈ Finset.univ.filter
          (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
          T i k * T_inv k j ≤ 0 := by
        apply Finset.sum_nonpos; intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact mul_nonpos_of_nonpos_of_nonneg (hT_offdiag i k (by omega))
          (ih k j (by omega) (by omega))
      have h_prod_nn : 0 ≤ T i i * T_inv i j := by linarith
      have h1 : 0 ≤ T i i * T_inv i j / T i i :=
        div_nonneg h_prod_nn (le_of_lt (hT_diag_pos i))
      rwa [mul_div_cancel_left₀ (T_inv i j) (ne_of_gt (hT_diag_pos i))] at h1

-- ============================================================
-- |L⁻¹| ≤ M(L)⁻¹ for lower triangular matrices
-- ============================================================

/-- **Theorem 8.12, first inequality, lower triangular analogue** (Higham §8.3).

    For a nonsingular lower triangular L with inverse L_inv, and M_inv the
    inverse of M(L), we have |L_inv_ij| ≤ M_inv_ij componentwise. -/
theorem abs_inv_le_compMatrix_inv_lowerTri (n : ℕ) (L L_inv M_inv : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hInv : IsInverse n L L_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n L) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0) :
    ∀ i j : Fin n, |L_inv i j| ≤ M_inv i j := by
  have hInv_lt := inv_lower_tri n L L_inv hLT hL_diag hInv.1
  -- M(L) is a lower triangular M-matrix
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n L i i := by
    intro i; simp [comparisonMatrix]; exact hL_diag i
  have hM_offdiag : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n L i j ≤ 0 := by
    intro i j _; simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_lt : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n L i j = 0 := by
    intro i j hij; unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hLT i j hij]
  have hM_nn := lower_tri_mmatrix_inv_nonneg n (comparisonMatrix n L) M_inv
    hM_lt hM_diag_pos hM_offdiag hM_RInv hM_inv_lt
  -- Prove |L_inv_ij| ≤ M_inv_ij by induction on i - j
  suffices h : ∀ (d : ℕ), ∀ i j : Fin n, i.val - j.val ≤ d → j.val ≤ i.val →
      |L_inv i j| ≤ M_inv i j from
    fun i j => by
      by_cases hij : j.val ≤ i.val
      · exact h (i.val - j.val) i j (le_refl _) hij
      · push_neg at hij
        rw [hInv_lt i j (by omega), hM_inv_lt i j (by omega), abs_zero]
  intro d
  induction d with
  | zero =>
    intro i j hdiff hij
    have heq : i = j := Fin.ext (by omega)
    subst heq
    rw [inv_diag_entry_lower n L L_inv hLT hL_diag hInv.1 hInv_lt, abs_div, abs_one]
    -- M_inv_ii = 1/|L_ii| from right inverse equation
    have hMR := hM_RInv i i; simp at hMR
    have hM_diag : comparisonMatrix n L i i * M_inv i i = 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hMR
      suffices ∑ k ∈ Finset.univ.erase i, comparisonMatrix n L i k * M_inv k i = 0 by
        linarith
      apply Finset.sum_eq_zero; intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      by_cases hlt : i.val < k.val
      · rw [hM_lt i k hlt, zero_mul]
      · rw [hM_inv_lt k i (by omega), mul_zero]
    simp [comparisonMatrix] at hM_diag
    have : M_inv i i = 1 / |L i i| := by
      field_simp [ne_of_gt (abs_pos.mpr (hL_diag i))]; linarith
    rw [this]
  | succ d' ih =>
    intro i j hdiff hij
    by_cases heq : i.val = j.val
    · exact ih i j (by omega) (by omega)
    · have hij' : j.val < i.val := by omega
      -- Recurrence for L_inv
      have hrec_L := inv_recurrence_lower n L L_inv hLT hL_diag hInv.2 hInv_lt i j hij'
      -- Recurrence for M(L)_inv
      have hrec_M := inv_recurrence_lower n (comparisonMatrix n L) M_inv hM_lt
        (fun k => ne_of_gt (hM_diag_pos k)) hM_RInv hM_inv_lt i j hij'
      have hLii_pos : 0 < |L i i| := abs_pos.mpr (hL_diag i)
      have hLii_ne : L i i ≠ 0 := hL_diag i
      -- |L_inv_ij| = |∑...| / |L_ii|
      have hL_prod : L i i * L_inv i j =
          -(∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
            L i k * L_inv k j) := by linarith
      have habs_eq : |L_inv i j| =
          |∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
            L i k * L_inv k j| / |L i i| := by
        have h1 : L_inv i j = -(∑ k ∈ Finset.univ.filter
            (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
            L i k * L_inv k j) / L i i := by
          field_simp [hLii_ne]; linarith
        rw [h1, abs_div, abs_neg]
      -- comparisonMatrix n L i i = |L i i|
      have hM_ii : comparisonMatrix n L i i = |L i i| := by simp [comparisonMatrix]
      -- For j < k < i: comparisonMatrix n L i k = -|L i k|
      have hM_ik : ∀ k : Fin n, k.val < i.val →
          comparisonMatrix n L i k = -|L i k| := by
        intro k hik; unfold comparisonMatrix
        simp [show i ≠ k from Fin.ne_of_val_ne (by omega)]
      -- From M recurrence: |L_ii| * M_inv_ij = ∑ |L_ik| * M_inv_kj
      have hM_prod : |L i i| * M_inv i j =
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
            |L i k| * M_inv k j := by
        have hsum_rw : ∑ k ∈ Finset.univ.filter
            (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
            comparisonMatrix n L i k * M_inv k j =
            -(∑ k ∈ Finset.univ.filter
            (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
            |L i k| * M_inv k j) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hM_ik k hk.2]; ring
        rw [hM_ii] at hrec_M; rw [hsum_rw] at hrec_M; linarith
      -- Main calc chain
      calc |L_inv i j|
          = |∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
              L i k * L_inv k j| / |L i i| := habs_eq
        _ ≤ (∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
              |L i k * L_inv k j|) / |L i i| :=
            div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (le_of_lt hLii_pos)
        _ = (∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
              |L i k| * |L_inv k j|) / |L i i| := by
            congr 1; apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ (∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val),
              |L i k| * M_inv k j) / |L i i| := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hLii_pos)
            apply Finset.sum_le_sum; intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            exact mul_le_mul_of_nonneg_left (ih k j (by omega) (by omega)) (abs_nonneg _)
        _ = M_inv i j := by
            rw [← hM_prod]; field_simp [ne_of_gt hLii_pos]

end NumStability
