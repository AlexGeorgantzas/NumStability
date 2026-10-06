import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.ForwardError
import NumStability.Analysis.PerturbationTheory
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

/-!
# Diagonal-dominance bounds for triangular solves

Reusable componentwise forward-error bounds for diagonally dominant
triangular systems.
-/

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Definitions
-- ============================================================

/-- Upper triangular with diagonal dominance:
    |U_ii| ≥ |U_ij| for all j > i (Higham condition (8.4)). -/
def IsDiagDominantUpper (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
  (∀ i : Fin n, U i i ≠ 0) ∧
  (∀ i j : Fin n, i.val < j.val → |U i j| ≤ |U i i|)

/-- A repository diagonally dominant upper-triangular matrix is nonsingular.

The definition `IsDiagDominantUpper` includes both upper-triangular shape and
nonzero diagonal entries, so this is just the shared triangular determinant
lemma in the local vocabulary. -/
theorem det_ne_zero_of_diagDominantUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U) :
    Matrix.det (U : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
  det_ne_zero_of_upper_triangular_diag_ne_zero n U hDD.1 hDD.2.1

/-- A concrete upper-triangular nonsingular-domain matrix that is not
    diagonally dominant: `[[1, 2], [0, 1]]`. -/
def diagDominanceCounterexample2 : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1
    else if i.val = 0 ∧ j.val = 1 then 2
    else if i.val = 1 ∧ j.val = 1 then 1
    else 0

theorem diagDominanceCounterexample2_upper :
    ∀ i j : Fin 2, j.val < i.val →
      diagDominanceCounterexample2 i j = 0 := by
  intro i j hji
  fin_cases i <;> fin_cases j <;>
    simp [diagDominanceCounterexample2] at hji ⊢

theorem diagDominanceCounterexample2_diag_nonzero :
    ∀ i : Fin 2, diagDominanceCounterexample2 i i ≠ 0 := by
  intro i
  fin_cases i <;> norm_num [diagDominanceCounterexample2]

theorem diagDominanceCounterexample2_det_ne_zero :
    Matrix.det
      (diagDominanceCounterexample2 : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  norm_num [diagDominanceCounterexample2, Matrix.det_fin_two]

theorem diagDominanceCounterexample2_not_diagDominant :
    ¬ IsDiagDominantUpper 2 diagDominanceCounterexample2 := by
  intro hDD
  have hbad := hDD.2.2 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by norm_num)
  norm_num [diagDominanceCounterexample2] at hbad

/-- Route elimination for QR bottleneck work: upper-triangular shape plus
    nonzero diagonal entries alone does not imply the repository's diagonal
    dominance hypothesis. -/
theorem not_forall_upper_tri_diag_nonzero_implies_diagDominant :
    ¬ (∀ U : Fin 2 → Fin 2 → ℝ,
      (∀ i j : Fin 2, j.val < i.val → U i j = 0) →
      (∀ i : Fin 2, U i i ≠ 0) →
      IsDiagDominantUpper 2 U) := by
  intro h
  exact diagDominanceCounterexample2_not_diagDominant
    (h diagDominanceCounterexample2
      diagDominanceCounterexample2_upper
      diagDominanceCounterexample2_diag_nonzero)

/-- Route elimination for QR bottleneck work: upper-triangular nonsingularity
    alone does not imply the repository's diagonal dominance hypothesis. -/
theorem not_forall_upper_tri_det_ne_zero_implies_diagDominant :
    ¬ (∀ U : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ i j : Fin 2, j.val < i.val → U i j = 0) →
      Matrix.det U ≠ 0 →
      IsDiagDominantUpper 2 U) := by
  intro h
  exact diagDominanceCounterexample2_not_diagDominant
    (h (diagDominanceCounterexample2 : Matrix (Fin 2) (Fin 2) ℝ)
      diagDominanceCounterexample2_upper
      diagDominanceCounterexample2_det_ne_zero)

/-- Route elimination for QR bottleneck work: an explicit finite
    `κ∞` certificate, upper-triangular shape, and nonsingularity still do not
    imply the repository's diagonal-dominance hypothesis.

    The witness is again `[[1, 2], [0, 1]]`; the condition-number budget is
    chosen to be the matrix's own local `κ∞` value, so the obstruction is not
    absence of a finite conditioning bound.  A positive QR route must supply a
    genuinely stronger invariant, or keep diagonal dominance visible. -/
theorem exists_upper_tri_det_ne_zero_kappaInf_bound_not_diagDominant :
    ∃ (U : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ),
      (∀ i j : Fin 2, j.val < i.val → U i j = 0) ∧
      Matrix.det U ≠ 0 ∧
      kappaInf 2 (by norm_num : 0 < 2) U (nonsingInv 2 U) ≤ κ ∧
      ¬ IsDiagDominantUpper 2 U := by
  let U : Matrix (Fin 2) (Fin 2) ℝ := diagDominanceCounterexample2
  let κ : ℝ := kappaInf 2 (by norm_num : 0 < 2) U (nonsingInv 2 U)
  exact ⟨U, κ, diagDominanceCounterexample2_upper,
    diagDominanceCounterexample2_det_ne_zero, le_rfl,
    diagDominanceCounterexample2_not_diagDominant⟩

/-- Universal-form companion to
    `exists_upper_tri_det_ne_zero_kappaInf_bound_not_diagDominant`. -/
theorem not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_diagDominant :
    ¬ (∀ (U : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ),
      (∀ i j : Fin 2, j.val < i.val → U i j = 0) →
      Matrix.det U ≠ 0 →
      kappaInf 2 (by norm_num : 0 < 2) U (nonsingInv 2 U) ≤ κ →
      IsDiagDominantUpper 2 U) := by
  intro h
  rcases exists_upper_tri_det_ne_zero_kappaInf_bound_not_diagDominant with
    ⟨U, κ, hupper, hdet, hκ, hnotDD⟩
  exact hnotDD (h U κ hupper hdet hκ)

/-- Route elimination for the rectangular QR bottleneck: an exact
    orthogonal-times-upper factorization with nonzero triangular diagonal does
    not imply the repository's diagonal-dominance hypothesis.  The witness is
    the same upper-triangular matrix `[[1, 2], [0, 1]]`, written as
    `A = I * R`.  Thus a positive unpivoted QR route cannot obtain diagonal
    dominance merely from the final exact QR shape; it needs a genuinely
    stronger computed-loop/off-diagonal-control invariant, or it must keep
    diagonal dominance visible as a domain hypothesis. -/
theorem exists_orthogonal_upper_factorization_not_diagDominant :
    ∃ (A Q R : Fin 2 → Fin 2 → ℝ),
      IsOrthogonal 2 Q ∧
      (∀ i j : Fin 2, j.val < i.val → R i j = 0) ∧
      (∀ i : Fin 2, R i i ≠ 0) ∧
      (∀ i j : Fin 2, matMul 2 Q R i j = A i j) ∧
      ¬ IsDiagDominantUpper 2 R := by
  refine ⟨diagDominanceCounterexample2, idMatrix 2,
    diagDominanceCounterexample2, IsOrthogonal.id 2,
    diagDominanceCounterexample2_upper,
    diagDominanceCounterexample2_diag_nonzero, ?_,
    diagDominanceCounterexample2_not_diagDominant⟩
  intro i j
  exact congrFun (congrFun
    (matMul_id_left 2 diagDominanceCounterexample2) i) j

/-- Universal-form companion to
    `exists_orthogonal_upper_factorization_not_diagDominant`. -/
theorem not_forall_orthogonal_upper_factorization_implies_diagDominant :
    ¬ (∀ (A Q R : Fin 2 → Fin 2 → ℝ),
      IsOrthogonal 2 Q →
      (∀ i j : Fin 2, j.val < i.val → R i j = 0) →
      (∀ i : Fin 2, R i i ≠ 0) →
      (∀ i j : Fin 2, matMul 2 Q R i j = A i j) →
      IsDiagDominantUpper 2 R) := by
  intro h
  rcases exists_orthogonal_upper_factorization_not_diagDominant with
    ⟨A, Q, R, hQ, hupper, hdiag, hfactor, hnotDD⟩
  exact hnotDD (h A Q R hQ hupper hdiag hfactor)

-- ============================================================
-- Properties of the inverse of an upper triangular matrix
-- ============================================================

/-- The left inverse of an upper triangular matrix is upper triangular.

    Proof by strong induction on j: for each j < i, the left inverse equation
    ∑_k U_inv_ik * U_kj = 0 reduces to U_inv_ij * U_jj = 0
    because all other terms vanish (by upper triangularity of U for k > j,
    and by induction hypothesis for k < j). Since U_jj ≠ 0, U_inv_ij = 0. -/
theorem inv_upper_tri (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsLeftInverse n U U_inv) :
    ∀ i j : Fin n, j.val < i.val → U_inv i j = 0 := by
  -- Prove: ∀ j_val < n, ∀ i with j_val < i, U_inv i j = 0
  -- by strong induction on j_val
  -- Strong induction on j.val: for all jv < n, U_inv i ⟨jv, _⟩ = 0 when jv < i.val
  suffices ∀ (jv : ℕ) (hjv : jv < n), ∀ i : Fin n, jv < i.val →
      U_inv i ⟨jv, hjv⟩ = 0 by
    intro i j hij; exact this j.val j.isLt i hij
  intro jv
  -- Strong induction: assume true for all jv' < jv
  exact Nat.strongRecOn jv (fun jv ih hjv i hi => by
    let j : Fin n := ⟨jv, hjv⟩
    have hij : i ≠ j := Fin.ne_of_val_ne (by simp [j]; omega)
    have h := hInv i j
    simp [hij] at h
    -- Isolate j-th term: U_inv_ij * U_jj = 0
    have : U_inv i j * U j j = 0 := by
      suffices ∑ k : Fin n, U_inv i k * U k j = U_inv i j * U j j by linarith
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      suffices ∑ k ∈ Finset.univ.erase j, U_inv i k * U k j = 0 by linarith
      apply Finset.sum_eq_zero; intro k hk
      have hk_ne := Finset.ne_of_mem_erase hk
      by_cases hklt : k.val < jv
      · -- k < j < i: U_inv_ik = 0 by strong IH
        have hki : k.val < i.val := by omega
        rw [ih k.val hklt (by omega) i hki, zero_mul]
      · -- k > j: U_kj = 0 by upper triangularity
        push_neg at hklt
        have : jv < k.val := by
          by_contra hc; push_neg at hc
          have := le_antisymm (by omega) hklt
          exact hk_ne (Fin.ext (by simp [j]; omega))
        rw [hUT k j (by simp [j]; exact this), mul_zero]
    exact (mul_eq_zero.mp this).elim id (fun h => absurd h (hU_diag _)))

/-- Diagonal entries of the inverse: (U_inv)_ii = 1 / U_ii. -/
theorem inv_diag_entry (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsLeftInverse n U U_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0) :
    ∀ i : Fin n, U_inv i i = 1 / U i i := by
  intro i
  have h := hInv i i
  simp at h
  -- Isolate k = i term
  have honly : ∑ k : Fin n, U_inv i k * U k i = U_inv i i * U i i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    suffices ∑ k ∈ Finset.univ.erase i, U_inv i k * U k i = 0 by linarith
    apply Finset.sum_eq_zero; intro k hk
    have hki := Finset.ne_of_mem_erase hk
    by_cases hlt : k.val < i.val
    · rw [hInv_ut i k hlt, zero_mul]
    · push_neg at hlt
      rw [hUT k i (by omega), mul_zero]
  rw [honly] at h
  have hmul : U_inv i i * U i i = 1 := h
  have hne := hU_diag i
  field_simp [hne]
  linarith

/-- Recursive formula for off-diagonal entries from the right inverse equation.
    For j > i: U_ii * U_inv_ij = -∑_{k: i < k ≤ j} U_ik * U_inv_kj. -/
theorem inv_recurrence (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hRInv : IsRightInverse n U U_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0) :
    ∀ i j : Fin n, i.val < j.val →
      U i i * U_inv i j +
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
        U i k * U_inv k j = 0 := by
  intro i j hij
  have hR := hRInv i j
  simp [show i ≠ j from Fin.ne_of_val_ne (by omega)] at hR
  -- ∑_k U_ik * U_inv_kj = 0. Split off k=i term.
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hR
  -- The remaining sum over k ≠ i: zero out terms outside {i < k ≤ j}
  have hrest : ∑ k ∈ Finset.univ.erase i, U i k * U_inv k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
        U i k * U_inv k j := by
    symm; apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
    · intro k hk hknot
      rw [Finset.mem_erase] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hknot
      push_neg at hknot
      by_cases hlt : k.val ≤ i.val
      · rw [hUT i k (by omega), zero_mul]
      · push_neg at hlt
        rw [hInv_ut k j (by omega), mul_zero]
  rw [hrest] at hR; linarith

-- ============================================================
-- Entry bound for inverse of unit upper triangular matrix
-- ============================================================

/-- Auxiliary: the sum ∑_{k: i≤k≤j} |V_inv k j| is bounded, where V_inv is
    the inverse of a unit upper triangular matrix with |V_ij| ≤ 1.
    Proved by the "double S" trick: S(i,j) = ∑_{k: i≤k≤j} |V_inv k j| ≤ 2^d.
    Then |V_inv i j| ≤ S(i+1,j) ≤ 2^{d-1}. -/
theorem inv_sum_bound (n : ℕ) (V V_inv : Fin n → Fin n → ℝ)
    (hVT : ∀ i j : Fin n, j.val < i.val → V i j = 0)
    (hV_unit : ∀ i : Fin n, V i i = 1)
    (hV_bound : ∀ i j : Fin n, i.val < j.val → |V i j| ≤ 1)
    (hRInv : IsRightInverse n V V_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → V_inv i j = 0)
    (hInv_diag : ∀ i : Fin n, V_inv i i = 1) :
    ∀ (d : ℕ), ∀ (i j : Fin n), j.val - i.val = d → i.val ≤ j.val →
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val),
        |V_inv k j| ≤ 2 ^ d := by
  intro d
  induction d with
  | zero =>
    intro i j hdiff hij
    have heq : i = j := Fin.ext (by omega)
    subst heq
    -- Filter contains only k = i
    have : Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ i.val) = {i} := by
      ext k; simp [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨h1, h2⟩; exact Fin.ext (by omega)
      · intro h; subst h; exact ⟨le_refl _, le_refl _⟩
    rw [this, Finset.sum_singleton, hInv_diag, abs_one]; norm_num
  | succ d' ih =>
    intro i j hdiff hij
    -- Split: ∑_{k: i≤k≤j} = |V_inv i j| + ∑_{k: i+1≤k≤j}
    -- = |V_inv i j| + S(i+1, j)
    -- where S(i+1, j) ≤ 2^d' by IH.
    -- Also |V_inv i j| ≤ ∑_{k: i<k≤j} |V_inv k j| = S(i+1, j) ≤ 2^d'.
    -- Total: 2^d' + 2^d' = 2^{d'+1}.
    by_cases heq : i.val = j.val
    · -- i = j contradicts d' + 1 > 0
      omega
    · -- i < j
      have hij' : i.val < j.val := by omega
      -- Step 1: Split off k = i from the sum
      have hi_mem : i ∈ Finset.univ.filter
          (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val) := by
        simp [Finset.mem_filter]; omega
      rw [← Finset.add_sum_erase _ _ hi_mem]
      -- Step 2: The remaining sum is S(i+1, j)
      have hfilt_eq : (Finset.univ.filter
            (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val)).erase i =
          Finset.univ.filter (fun k : Fin n => i.val + 1 ≤ k.val ∧ k.val ≤ j.val) := by
        ext k; simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hne, h1, h2⟩
          exact ⟨by omega, h2⟩
        · intro ⟨h1, h2⟩
          exact ⟨Fin.ne_of_val_ne (by omega), by omega, h2⟩
      rw [hfilt_eq]
      -- Step 3: The recurrence gives |V_inv i j| ≤ ∑_{k: i<k≤j} |V_inv k j|
      have hrec := inv_recurrence n V V_inv hVT
        (by intro i; rw [hV_unit]; exact one_ne_zero) hRInv hInv_ut i j hij'
      rw [hV_unit, one_mul] at hrec
      have hvinv_eq : V_inv i j = -(∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val < k.val ∧ k.val ≤ j.val), V i k * V_inv k j) := by linarith
      -- |V_inv i j| ≤ ∑_{k: i<k≤j} |V_inv k j|
      have hvinv_bound : |V_inv i j| ≤
          ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val < k.val ∧ k.val ≤ j.val), |V_inv k j| := by
        rw [hvinv_eq, abs_neg]
        calc |∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val < k.val ∧ k.val ≤ j.val), V i k * V_inv k j|
            ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val < k.val ∧ k.val ≤ j.val), |V i k * V_inv k j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val < k.val ∧ k.val ≤ j.val), |V i k| * |V_inv k j| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
          _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val < k.val ∧ k.val ≤ j.val), |V_inv k j| := by
              apply Finset.sum_le_sum; intro k hk
              simp [Finset.mem_filter] at hk
              calc |V i k| * |V_inv k j|
                  ≤ 1 * |V_inv k j| :=
                    mul_le_mul_of_nonneg_right (hV_bound i k hk.1) (abs_nonneg _)
                _ = |V_inv k j| := one_mul _
      -- The filter {i < k ≤ j} = {i+1 ≤ k ≤ j}
      have hfilt_eq2 : Finset.univ.filter (fun k : Fin n =>
            i.val < k.val ∧ k.val ≤ j.val) =
          Finset.univ.filter (fun k : Fin n =>
            i.val + 1 ≤ k.val ∧ k.val ≤ j.val) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [hfilt_eq2] at hvinv_bound
      -- Step 4: Apply IH to get S(i+1, j) ≤ 2^d'
      have hi1_lt : i.val + 1 < n := by omega
      have hS : ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j| ≤ 2 ^ d' := by
        exact ih ⟨i.val + 1, hi1_lt⟩ j (by simp; omega) (by simp; omega)
      -- Combine: |V_inv i j| + S(i+1,j) ≤ 2^d' + 2^d' = 2^{d'+1}
      have : |V_inv i j| + ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j|
          ≤ 2 ^ d' + 2 ^ d' := add_le_add (le_trans hvinv_bound hS) hS
      linarith [show (2 : ℝ) ^ d' + 2 ^ d' = 2 ^ (d' + 1) by ring]

theorem unitUpperTri_inv_entry_bound (n : ℕ) (V V_inv : Fin n → Fin n → ℝ)
    (hVT : ∀ i j : Fin n, j.val < i.val → V i j = 0)
    (hV_unit : ∀ i : Fin n, V i i = 1)
    (hV_bound : ∀ i j : Fin n, i.val < j.val → |V i j| ≤ 1)
    (hRInv : IsRightInverse n V V_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → V_inv i j = 0)
    (hInv_diag : ∀ i : Fin n, V_inv i i = 1) :
    ∀ i j : Fin n, i.val < j.val →
      |V_inv i j| ≤ 2 ^ (j.val - i.val - 1) := by
  intro i j hij
  -- |V_inv i j| ≤ S(i+1, j) ≤ 2^{j-i-1} from inv_sum_bound
  have hi1_lt : i.val + 1 < n := by omega
  -- From the recurrence, |V_inv i j| ≤ ∑_{k: i<k≤j} |V_inv k j|
  have hrec := inv_recurrence n V V_inv hVT
    (by intro i; rw [hV_unit]; exact one_ne_zero) hRInv hInv_ut i j hij
  rw [hV_unit, one_mul] at hrec
  have hvinv_eq : V_inv i j = -(∑ k ∈ Finset.univ.filter (fun k : Fin n =>
      i.val < k.val ∧ k.val ≤ j.val), V i k * V_inv k j) := by linarith
  have hvinv_bound : |V_inv i j| ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
        i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j| := by
    rw [hvinv_eq, abs_neg]
    calc |∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val < k.val ∧ k.val ≤ j.val), V i k * V_inv k j|
        ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val < k.val ∧ k.val ≤ j.val), |V i k| * |V_inv k j| := by
          calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
                i.val < k.val ∧ k.val ≤ j.val), |V i k * V_inv k j| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val < k.val ∧ k.val ≤ j.val), |V_inv k j| := by
          apply Finset.sum_le_sum; intro k hk
          simp [Finset.mem_filter] at hk
          calc |V i k| * |V_inv k j|
              ≤ 1 * |V_inv k j| :=
                mul_le_mul_of_nonneg_right (hV_bound i k hk.1) (abs_nonneg _)
            _ = |V_inv k j| := one_mul _
      _ = ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j| := by
          congr 1
  -- Apply inv_sum_bound with i' = ⟨i+1, _⟩
  have hS := inv_sum_bound n V V_inv hVT hV_unit hV_bound hRInv hInv_ut hInv_diag
    (j.val - (i.val + 1)) ⟨i.val + 1, hi1_lt⟩ j (by simp) (by simp; omega)
  have hconv : ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
        i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j| ≤
      2 ^ (j.val - i.val - 1) := by
    have : j.val - (i.val + 1) = j.val - i.val - 1 := by omega
    rw [this] at hS; exact hS
  linarith

/-- If `V` is unit upper triangular and each strict-upper row has absolute
    sum at most `1`, then every inverse entry on or above the diagonal has
    absolute value at most `1`. -/
theorem unitUpperTri_inv_entry_le_one_of_row_sum_le_one
    (n : ℕ) (V V_inv : Fin n → Fin n → ℝ)
    (hVT : ∀ i j : Fin n, j.val < i.val → V i j = 0)
    (hV_unit : ∀ i : Fin n, V i i = 1)
    (hV_row : ∀ i : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |V i j| ≤ 1)
    (hRInv : IsRightInverse n V V_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → V_inv i j = 0)
    (hInv_diag : ∀ i : Fin n, V_inv i i = 1) :
    ∀ i j : Fin n, i.val ≤ j.val → |V_inv i j| ≤ 1 := by
  suffices h : ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
      |V_inv i j| ≤ 1 from
    fun i j hij => h (j.val - i.val) i j (le_refl _) hij
  intro d
  induction d with
  | zero =>
      intro i j hdiff hij
      have heq : i = j := Fin.ext (by omega)
      subst heq
      rw [hInv_diag, abs_one]
  | succ d' ih =>
      intro i j hdiff hij
      by_cases heq : i.val = j.val
      · have heq' : i = j := Fin.ext heq
        subst heq'
        rw [hInv_diag, abs_one]
      · have hij' : i.val < j.val := by omega
        have hrec := inv_recurrence n V V_inv hVT
          (by intro k; rw [hV_unit]; exact one_ne_zero) hRInv hInv_ut i j hij'
        rw [hV_unit, one_mul] at hrec
        have hvinv_eq : V_inv i j = -(∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val < k.val ∧ k.val ≤ j.val), V i k * V_inv k j) := by
          linarith
        rw [hvinv_eq, abs_neg]
        calc
          |∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
              V i k * V_inv k j|
              ≤ ∑ k ∈ Finset.univ.filter
                  (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    |V i k * V_inv k j| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k ∈ Finset.univ.filter
                (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  |V i k| * |V_inv k j| := by
                apply Finset.sum_congr rfl
                intro k _
                exact abs_mul _ _
          _ ≤ ∑ k ∈ Finset.univ.filter
                (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  |V i k| * 1 := by
                apply Finset.sum_le_sum
                intro k hk
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
                exact mul_le_mul_of_nonneg_left
                  (ih k j (by omega) (by omega)) (abs_nonneg (V i k))
          _ = ∑ k ∈ Finset.univ.filter
                (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val), |V i k| := by
                apply Finset.sum_congr rfl
                intro k _
                rw [mul_one]
          _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val), |V i k| := by
                exact Finset.sum_le_sum_of_subset_of_nonneg
                  (by
                    intro k hk
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
                    exact hk.1)
                  (by
                    intro k _hk _hknot
                    exact abs_nonneg (V i k))
          _ ≤ 1 := hV_row i

-- ============================================================
-- Row-sum bound for inverse of unit upper triangular matrix
-- ============================================================

/-- Left-inverse recurrence: for j > i,
    ∑_{k: i≤k<j} U_inv_ik * U_kj + U_inv_ij * U_jj = 0. -/
theorem inv_left_recurrence (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hLInv : IsLeftInverse n U U_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0) :
    ∀ i j : Fin n, i.val < j.val →
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val < j.val),
        U_inv i k * U k j +
      U_inv i j * U j j = 0 := by
  intro i j hij
  have hL := hLInv i j
  simp [show i ≠ j from Fin.ne_of_val_ne (by omega)] at hL
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hL
  have hrest : ∑ k ∈ Finset.univ.erase j, U_inv i k * U k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val < j.val),
        U_inv i k * U k j := by
    symm; apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
    · intro k hk hknot
      rw [Finset.mem_erase] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hknot
      push_neg at hknot
      by_cases hlt : k.val < i.val
      · rw [hInv_ut i k hlt, zero_mul]
      · push_neg at hlt
        rw [hUT k j (by omega), mul_zero]
  rw [hrest] at hL; linarith

/-- Row-sum bound: ∑_{k: i≤k≤j} |V_inv_ik| ≤ 2^(j-i) for unit upper triangular V
    with |V_ij| ≤ 1. Uses left-inverse recurrence and the double-S trick. -/
theorem inv_row_sum_bound (n : ℕ) (V V_inv : Fin n → Fin n → ℝ)
    (hVT : ∀ i j : Fin n, j.val < i.val → V i j = 0)
    (hV_unit : ∀ i : Fin n, V i i = 1)
    (hV_bound : ∀ i j : Fin n, i.val < j.val → |V i j| ≤ 1)
    (hLInv : IsLeftInverse n V V_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → V_inv i j = 0)
    (hInv_diag : ∀ i : Fin n, V_inv i i = 1) :
    ∀ (d : ℕ), ∀ (i j : Fin n), j.val - i.val = d → i.val ≤ j.val →
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val),
        |V_inv i k| ≤ 2 ^ d := by
  intro d
  induction d with
  | zero =>
    intro i j hdiff hij
    have heq : i = j := Fin.ext (by omega)
    subst heq
    have : Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ i.val) = {i} := by
      ext k; simp [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨h1, h2⟩; exact Fin.ext (by omega)
      · intro h; subst h; exact ⟨le_refl _, le_refl _⟩
    rw [this, Finset.sum_singleton, hInv_diag, abs_one]; norm_num
  | succ d' ih =>
    intro i j hdiff hij
    by_cases heq : i.val = j.val
    · omega
    · have hij' : i.val < j.val := by omega
      -- Split off k = j from the sum
      have hj_mem : j ∈ Finset.univ.filter
          (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val) := by
        simp [Finset.mem_filter]; omega
      rw [← Finset.add_sum_erase _ _ hj_mem]
      -- The remaining sum is R(i, j-1)
      have hfilt_eq : (Finset.univ.filter
            (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val)).erase j =
          Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val < j.val) := by
        ext k; simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hne, h1, h2⟩; exact ⟨h1, by omega⟩
        · intro ⟨h1, h2⟩; exact ⟨Fin.ne_of_val_ne (by omega), h1, by omega⟩
      rw [hfilt_eq]
      -- The left recurrence gives |V_inv i j| ≤ ∑_{k: i≤k<j} |V_inv_ik|
      have hrec := inv_left_recurrence n V V_inv hVT
        (by intro i; rw [hV_unit]; exact one_ne_zero) hLInv hInv_ut i j hij'
      rw [hV_unit, mul_one] at hrec
      have hvinv_eq : V_inv i j = -(∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val ≤ k.val ∧ k.val < j.val), V_inv i k * V k j) := by linarith
      have hvinv_bound : |V_inv i j| ≤
          ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val ≤ k.val ∧ k.val < j.val), |V_inv i k| := by
        rw [hvinv_eq, abs_neg]
        calc |∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val ≤ k.val ∧ k.val < j.val), V_inv i k * V k j|
            ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val ≤ k.val ∧ k.val < j.val), |V_inv i k * V k j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val ≤ k.val ∧ k.val < j.val), |V_inv i k| * |V k j| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
          _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val ≤ k.val ∧ k.val < j.val), |V_inv i k| := by
              apply Finset.sum_le_sum; intro k hk
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
              have hVkj : |V k j| ≤ 1 := hV_bound k j (by omega)
              calc |V_inv i k| * |V k j|
                  ≤ |V_inv i k| * 1 :=
                    mul_le_mul_of_nonneg_left hVkj (abs_nonneg _)
                _ = |V_inv i k| := mul_one _
      -- Apply IH with j' = ⟨j.val - 1, _⟩
      have hj1_lt : j.val - 1 < n := by omega
      have hfilt_eq2 : Finset.univ.filter (fun k : Fin n =>
            i.val ≤ k.val ∧ k.val < j.val) =
          Finset.univ.filter (fun k : Fin n =>
            i.val ≤ k.val ∧ k.val ≤ j.val - 1) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [hfilt_eq2] at hvinv_bound ⊢
      have hR : ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val ≤ k.val ∧ k.val ≤ j.val - 1), |V_inv i k| ≤ 2 ^ d' := by
        exact ih i ⟨j.val - 1, hj1_lt⟩ (by simp; omega) (by simp; omega)
      have : |V_inv i j| + ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val ≤ k.val ∧ k.val ≤ j.val - 1), |V_inv i k|
          ≤ 2 ^ d' + 2 ^ d' := add_le_add (le_trans hvinv_bound hR) hR
      linarith [show (2 : ℝ) ^ d' + 2 ^ d' = 2 ^ (d' + 1) by ring]

-- ============================================================
-- Lemma 8.6: diagonal dominance bound on |U⁻¹||U|
-- ============================================================

/-- **Lemma 8.6** (Higham §8.2).

    If the upper triangular matrix U satisfies |U_ii| ≥ |U_ij| for all j > i,
    then W = |U⁻¹||U| satisfies w_ij ≤ 2^(j-i) for all j ≥ i.

    Proof: write V = D⁻¹U where D = diag(U_ii). Then V is unit upper triangular
    with |V_ij| ≤ 1, and (|U⁻¹||U|)_ij = (|V⁻¹||V|)_ij ≤ ∑_k |V⁻¹_ik| ≤ 2^(j-i). -/
theorem inv_abs_mul_bound_diagDom (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    ∀ i j : Fin n, i.val ≤ j.val →
      ∑ k : Fin n, |U_inv i k| * |U k j| ≤ 2 ^ (j.val - i.val) := by
  obtain ⟨hUT, hU_diag, hU_dom⟩ := hDD
  obtain ⟨hLInv, _hRInv⟩ := hInv
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hLInv
  intro i j hij
  -- Zero out terms outside [i, j]
  have hsum_reduce : ∑ k : Fin n, |U_inv i k| * |U k j| =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val),
        |U_inv i k| * |U k j| := by
    symm; apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hknot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hknot
    push_neg at hknot
    by_cases hlt : k.val < i.val
    · rw [hInv_ut i k hlt, abs_zero, zero_mul]
    · push_neg at hlt
      rw [hUT k j (by omega), abs_zero, mul_zero]
  rw [hsum_reduce]
  -- Define V = D⁻¹U: V_ij = U_ij / U_ii
  -- Key identity: |U_inv_ik| * |U_kj| = |V_inv_ik| * |V_kj|
  -- where V_inv_ij = U_inv_ij * U_jj
  -- Proof: |U_inv_ik| * |U_kj| = (|V_inv_ik| / |U_kk|) * (|U_kk| * |V_kj|) = |V_inv_ik| * |V_kj|
  -- Then: ∑ |V_inv_ik| * |V_kj| ≤ ∑ |V_inv_ik| (since |V_kj| ≤ 1)
  -- And: ∑ |V_inv_ik| ≤ 2^(j-i) by inv_row_sum_bound
  --
  -- We define V and V_inv locally and verify properties.
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
  -- Convert sum: |U_inv_ik| * |U_kj| = |V_inv_ik| * |V_kj|
  have hconv : ∀ k : Fin n, |U_inv i k| * |U k j| = |V_inv i k| * |V k j| := by
    intro k
    simp only [V, V_inv]
    have hk := hU_diag k
    rw [show U_inv i k * U k k = U k k * U_inv i k from mul_comm _ _]
    rw [abs_mul, abs_div]
    have hkpos : (0 : ℝ) < |U k k| := abs_pos.mpr hk
    field_simp [ne_of_gt hkpos]
  calc ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val),
        |U_inv i k| * |U k j|
      = ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val),
        |V_inv i k| * |V k j| := by
        apply Finset.sum_congr rfl; intro k _; exact hconv k
    _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val),
        |V_inv i k| := by
        apply Finset.sum_le_sum; intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        have hVkj : |V k j| ≤ 1 := by
          by_cases hkj : k.val < j.val
          · exact hV_bound k j hkj
          · have : k = j := Fin.ext (by omega)
            subst this; rw [hV_unit, abs_one]
        calc |V_inv i k| * |V k j|
            ≤ |V_inv i k| * 1 := mul_le_mul_of_nonneg_left hVkj (abs_nonneg _)
          _ = |V_inv i k| := mul_one _
    _ ≤ 2 ^ (j.val - i.val) :=
        inv_row_sum_bound n V V_inv hVT hV_unit hV_bound hVLInv hVinv_ut hVinv_diag
          (j.val - i.val) i j (by omega) hij

-- ============================================================
-- Theorem 8.7: componentwise forward error under diagonal dominance
-- ============================================================

/-- **Theorem 8.7** (Higham §8.2).

    Under the conditions of Lemma 8.6, the computed solution x̂ to Ux = b
    obtained by back substitution satisfies:
      |x_i - x̂_i| ≤ 2^(n-i) · γ(n) · max_{j≥i} |x̂_j|    (0-based indexing)

    This bound shows that later components of x are always computed to high
    accuracy relative to the elements already computed. -/
theorem backSub_forward_error_diagDom (fp : FPModel) (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv)
    (hTx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hn : gammaValid fp n) :
    let x_hat := fl_backSub fp n U b
    ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 ^ (n - i.val) * gamma fp n *
          Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val ≤ j.val))
            ⟨i, by simp [Finset.mem_filter]⟩ (fun j => |x_hat j|) := by
  intro x_hat
  have hUT := hDD.1
  have hU_diag := hDD.2.1
  have hLInv := hInv.1
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hLInv
  have hfwd := backSub_forward_error fp n U U_inv x b hU_diag hUT hLInv hTx hn
  intro i
  let M := Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val ≤ j.val))
    ⟨i, by simp [Finset.mem_filter]⟩ (fun j => |x_hat j|)
  -- Step 1: Rewrite the double sum via Fubini
  have hfubini : ∑ j : Fin n, |U_inv i j| * (∑ k : Fin n, |U j k| * |x_hat k|) =
      ∑ k : Fin n, (∑ j : Fin n, |U_inv i j| * |U j k|) * |x_hat k| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  -- Step 2: For k < i, the inner sum W_ik = 0
  have hW_zero : ∀ k : Fin n, k.val < i.val →
      ∑ j : Fin n, |U_inv i j| * |U j k| = 0 := by
    intro k hki
    apply Finset.sum_eq_zero; intro j _
    by_cases hjk : k.val < j.val
    · rw [hUT j k hjk, abs_zero, mul_zero]
    · push_neg at hjk
      rw [hInv_ut i j (by omega), abs_zero, zero_mul]
  -- Step 3: Factor out M from the weighted sum
  -- ∑_k W_ik * |x̂_k| ≤ M * ∑_k W_ik  (since W_ik ≥ 0 and |x̂_k| ≤ M for k ≥ i)
  have hfactor : ∑ k : Fin n, (∑ j : Fin n, |U_inv i j| * |U j k|) * |x_hat k| ≤
      M * ∑ k : Fin n, (∑ j : Fin n, |U_inv i j| * |U j k|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro k _
    by_cases hki : i.val ≤ k.val
    · have hW_nn : 0 ≤ ∑ j : Fin n, |U_inv i j| * |U j k| :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hM : |x_hat k| ≤ M :=
        Finset.le_sup' (fun j => |x_hat j|)
          (by simp [Finset.mem_filter]; exact hki)
      calc (∑ j : Fin n, |U_inv i j| * |U j k|) * |x_hat k|
          ≤ (∑ j : Fin n, |U_inv i j| * |U j k|) * M :=
            mul_le_mul_of_nonneg_left hM hW_nn
        _ = M * (∑ j : Fin n, |U_inv i j| * |U j k|) := by ring
    · push_neg at hki
      rw [hW_zero k hki, zero_mul, mul_zero]
  -- Step 4: Bound ∑_k W_ik ≤ 2^{n-i} using inv_abs_mul_bound_diagDom + geometric sum
  -- Helper: geometric sum bound ∑_{r=0}^{m-1} 2^r ≤ 2^m
  have geom_le : ∀ (m : ℕ), ∑ r ∈ Finset.range m, (2 : ℝ) ^ r ≤ 2 ^ m := by
    intro m; induction m with
    | zero => simp
    | succ m' ihm =>
      rw [Finset.sum_range_succ]
      linarith [show (2 : ℝ) ^ m' + 2 ^ m' = 2 ^ (m' + 1) from by ring]
  have hgeom : ∑ k : Fin n, (∑ j : Fin n, |U_inv i j| * |U j k|) ≤ 2 ^ (n - i.val) := by
    -- Replace full sum with filtered sum (k < i terms are 0)
    have hsplit : ∑ k : Fin n, (∑ j : Fin n, |U_inv i j| * |U j k|) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val),
          (∑ j : Fin n, |U_inv i j| * |U j k|) := by
      symm; apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k _ hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
      exact hW_zero k hk
    rw [hsplit]
    -- Bound each term by 2^{k-i} via inv_abs_mul_bound_diagDom
    have hbound : ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val),
        (∑ j : Fin n, |U_inv i j| * |U j k|) ≤
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val),
          (2 : ℝ) ^ (k.val - i.val) := by
      apply Finset.sum_le_sum; intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact inv_abs_mul_bound_diagDom n U U_inv hDD hInv i k hk
    -- Reindex via image: the filtered sum over Fin n maps to a subset of range(n-i)
    let S := Finset.univ.filter (fun k : Fin n => i.val ≤ k.val)
    have hinj : ∀ k1 ∈ S, ∀ k2 ∈ S, k1.val - i.val = k2.val - i.val → k1 = k2 := by
      intro k1 hk1 k2 hk2 heq
      have hk1' : i.val ≤ k1.val := (Finset.mem_filter.mp hk1).2
      have hk2' : i.val ≤ k2.val := (Finset.mem_filter.mp hk2).2
      exact Fin.ext (by omega)
    have himg_sub : S.image (fun k : Fin n => k.val - i.val) ⊆
        Finset.range (n - i.val) := by
      intro r hr
      rw [Finset.mem_image] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      have hk' : i.val ≤ k.val := (Finset.mem_filter.mp hk).2
      simp only [Finset.mem_range]; omega
    have hreindex : ∑ k ∈ S, (2 : ℝ) ^ (k.val - i.val) =
        ∑ r ∈ S.image (fun k : Fin n => k.val - i.val), (2 : ℝ) ^ r := by
      rw [Finset.sum_image (fun k1 hk1 k2 hk2 heq => hinj k1 hk1 k2 hk2 heq)]
    rw [hreindex] at hbound
    calc ∑ k ∈ S, (∑ j : Fin n, |U_inv i j| * |U j k|)
        ≤ ∑ r ∈ S.image (fun k : Fin n => k.val - i.val), (2 : ℝ) ^ r := hbound
      _ ≤ ∑ r ∈ Finset.range (n - i.val), (2 : ℝ) ^ r :=
          Finset.sum_le_sum_of_subset_of_nonneg himg_sub (fun r _ _ => by positivity)
      _ ≤ 2 ^ (n - i.val) := geom_le (n - i.val)
  -- M ≥ 0
  have hM_nn : (0 : ℝ) ≤ M :=
    le_trans (abs_nonneg (x_hat i))
      (Finset.le_sup' (fun j => |x_hat j|)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, le_refl i.val⟩))
  -- Combine everything
  calc |x i - x_hat i|
      ≤ gamma fp n * ∑ j : Fin n, |U_inv i j| *
          (∑ k : Fin n, |U j k| * |x_hat k|) := hfwd i
    _ = gamma fp n * ∑ k : Fin n, (∑ j : Fin n, |U_inv i j| * |U j k|) *
          |x_hat k| := by rw [hfubini]
    _ ≤ gamma fp n * (M * ∑ k : Fin n, (∑ j : Fin n, |U_inv i j| * |U j k|)) :=
        mul_le_mul_of_nonneg_left hfactor (gamma_nonneg fp hn)
    _ ≤ gamma fp n * (M * 2 ^ (n - i.val)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeom hM_nn)
          (gamma_nonneg fp hn)
    _ = 2 ^ (n - i.val) * gamma fp n * M := by ring

end NumStability
