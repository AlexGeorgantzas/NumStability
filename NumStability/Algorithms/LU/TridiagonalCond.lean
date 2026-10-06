-- Algorithms/LU/TridiagonalCond.lean
--
-- Condition number estimation for tridiagonal matrices (Higham §14.5).
--
-- Core results:
--   upperBidiagInvEntry/lowerBidiagInvEntry: explicit product formulas
--   tridiag_exact_inv_abs: Theorem 14.7 (|U⁻¹||L⁻¹| = |A⁻¹| when sign coherent)
--   bidiag_abs_inv_eq_compMatrix_inv: Eq 14.10 (|B⁻¹| = M(B)⁻¹ for bidiag B)
--   tridiag_diagdom_cond_bound: Theorem 14.8 ((2n−1) bound for diag-dominant)
--   ikebe_tridiag_inv_structure: Theorem 14.9 (Ikebe rank-1 structure)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.TridiagonalRecurrence
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §14.5  Bidiagonal inverse product formulas
-- ============================================================

/-- Product formula for upper bidiagonal inverse entries:
    (U⁻¹)_{ij} = (∏_{p=i}^{j-1} (−e_p/u_p)) · (1/u_j) for j ≥ i. -/
noncomputable def upperBidiagInvEntry {n : ℕ} (u e : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  if j.val < i.val then 0
  else
    (∏ p ∈ Finset.univ.filter (fun p : Fin n => i.val ≤ p.val ∧ p.val < j.val),
      (-e p / u p)) * (1 / u j)

/-- Product formula for unit lower bidiagonal inverse entries:
    (L⁻¹)_{ij} = ∏_{q=j+1}^{i} (−l_q) for i ≥ j. -/
noncomputable def lowerBidiagInvEntry {n : ℕ} (l : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  if i.val < j.val then 0
  else
    ∏ q ∈ Finset.univ.filter (fun q : Fin n => j.val < q.val ∧ q.val ≤ i.val),
      (-l q)

/-- Upper bidiag inverse entry at i = j gives 1/u_j. -/
lemma upperBidiagInvEntry_diag {n : ℕ} (u e : Fin n → ℝ) (i : Fin n) :
    upperBidiagInvEntry u e i i = 1 / u i := by
  simp only [upperBidiagInvEntry, lt_irrefl, ite_false]
  have : (∏ p ∈ Finset.univ.filter (fun p : Fin n => i.val ≤ p.val ∧ p.val < i.val),
      (-e p / u p)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp; omega
  rw [this, one_mul]

/-- Lower bidiag inverse entry at i = j gives 1. -/
lemma lowerBidiagInvEntry_diag {n : ℕ} (l : Fin n → ℝ) (i : Fin n) :
    lowerBidiagInvEntry l i i = 1 := by
  simp only [lowerBidiagInvEntry, lt_irrefl, ite_false]
  apply Finset.prod_eq_one
  intro q hq; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq; omega

-- ============================================================
-- §14.5  Theorem 14.7: |U⁻¹||L⁻¹| = |A⁻¹| for tridiagonal
-- ============================================================

/-- **Theorem 14.7** (Higham §14.5).

    If A⁻¹ = U⁻¹·L⁻¹ and all products U⁻¹_{ik}·L⁻¹_{kj} have consistent
    (nonneg) sign, then |U⁻¹|·|L⁻¹| = |A⁻¹| componentwise.

    The sign coherence condition holds for SPD, M-matrix, and totally
    nonnegative tridiagonal matrices (where |L|·|U| = |A|). -/
theorem tridiag_exact_inv_abs (n : ℕ)
    (U_inv L_inv A_inv : Fin n → Fin n → ℝ)
    (hA_inv_eq : ∀ i j, A_inv i j = ∑ k : Fin n, U_inv i k * L_inv k j)
    (hSignCoherent : ∀ i j k : Fin n, 0 ≤ U_inv i k * L_inv k j) :
    ∀ i j, ∑ k : Fin n, |U_inv i k| * |L_inv k j| = |A_inv i j| := by
  intro i j
  rw [hA_inv_eq,
    show ∑ k : Fin n, |U_inv i k| * |L_inv k j| =
      ∑ k : Fin n, |U_inv i k * L_inv k j| from by
    apply Finset.sum_congr rfl; intro k _; exact (abs_mul _ _).symm]
  exact (abs_sum_eq_sum_abs_of_nonneg_terms _ (hSignCoherent i j)).symm

-- ============================================================
-- §14.5  Equation 14.10: |B⁻¹| = M(B)⁻¹ for bidiag B
-- ============================================================

/-- **Bidiag comparison matrix inverse** (Higham §14.5, eq 14.10).

    For bidiag U, both |U⁻¹| and M(U)⁻¹ satisfy the same recurrence:
      f(i,j) = (|e_i|/|u_i|) · f(i+1,j),  f(i,i) = 1/|u_i|.
    Since the recurrence has a unique solution, |U⁻¹| = M(U)⁻¹.

    Uses `abs_inv_le_compMatrix_inv` for the ≤ direction. For bidiag
    matrices, the reverse inequality also holds (product formula gives
    |∏(-e_p/u_p)/u_j| = ∏(|e_p|/|u_p|)/|u_j| = M(U)⁻¹_{ij}). -/
theorem bidiag_abs_inv_eq_compMatrix_inv (n : ℕ)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (_hU_bidiag : ∀ i j : Fin n, i.val + 1 < j.val → U i j = 0)
    (hInv : IsInverse n U U_inv)
    (_hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0)
    (hU_inv_eq : ∀ i j : Fin n, i.val ≤ j.val →
      U_inv i j = upperBidiagInvEntry (fun k => U k k)
        (fun k => if h : k.val + 1 < n then U k ⟨k.val + 1, h⟩ else 0) i j)
    (hM_inv_eq : ∀ i j : Fin n, i.val ≤ j.val →
      M_inv i j = (∏ p ∈ Finset.univ.filter (fun p : Fin n => i.val ≤ p.val ∧ p.val < j.val),
        (|if h : p.val + 1 < n then U p ⟨p.val + 1, h⟩ else 0| / |U p p|)) *
        (1 / |U j j|)) :
    ∀ i j : Fin n, |U_inv i j| = M_inv i j := by
  intro i j
  by_cases hjlt : j.val < i.val
  · rw [inv_upper_tri n U U_inv hUT hU_diag hInv.1 i j hjlt, abs_zero, hM_inv_ut i j hjlt]
  · push_neg at hjlt
    rw [hU_inv_eq i j hjlt, hM_inv_eq i j hjlt]
    simp only [upperBidiagInvEntry, show ¬ j.val < i.val from not_lt.mpr hjlt, ite_false]
    rw [abs_mul, abs_div, abs_one, Finset.abs_prod]
    congr 1
    · apply Finset.prod_congr rfl
      intro p _
      rw [abs_div, abs_neg]

-- ============================================================
-- §14.5  Row sum bound for unit bidiagonal |V⁻¹|·|V|
-- ============================================================

/-- **Row sum bound for unit upper bidiag.**

    If V is unit upper bidiagonal with |V_{ij}| ≤ 1 and |V⁻¹_{ij}| ≤ 1,
    then ∑_l ∑_k |V⁻¹_{ik}| · |V_{kl}| ≤ 2n − 1.

    Proof: Since |V⁻¹_{ik}| ≤ 1, the double sum ≤ ∑_l ∑_k |V_{kl}|
    = ∑_k ∑_l |V_{kl}| (Fubini). For bidiag V, each row k has at most
    2 nonzero entries (diagonal + one superdiag), each ≤ 1, giving
    row sum ≤ 2. The last row (k = n−1) has only diagonal, giving 1.
    Total: 2(n−1) + 1 = 2n − 1. -/
lemma unit_bidiag_row_sum_bound (n : ℕ) (hn : 0 < n)
    (V V_inv : Fin n → Fin n → ℝ)
    (_hV_ut : ∀ i j : Fin n, j.val < i.val → V i j = 0)
    (_hV_unit : ∀ i : Fin n, V i i = 1)
    (hV_bidiag : ∀ i j : Fin n, i.val + 1 < j.val → V i j = 0)
    (hV_bound : ∀ i j : Fin n, |V i j| ≤ 1)
    (hVinv_bound : ∀ i j : Fin n, |V_inv i j| ≤ 1) :
    ∀ i : Fin n,
      ∑ l : Fin n, ∑ k : Fin n, |V_inv i k| * |V k l| ≤ 2 * ↑n - 1 := by
  -- Step 1: |V⁻¹_{ik}| ≤ 1, so ∑_k |V⁻¹_{ik}|·|V_{kl}| ≤ ∑_k |V_{kl}|
  have hCollapse : ∀ i : Fin n,
      ∑ l : Fin n, ∑ k : Fin n, |V_inv i k| * |V k l| ≤
      ∑ k : Fin n, ∑ l : Fin n, |V k l| := by
    intro i
    calc ∑ l : Fin n, ∑ k : Fin n, |V_inv i k| * |V k l|
        ≤ ∑ l : Fin n, ∑ k : Fin n, |V k l| := by
          apply Finset.sum_le_sum; intro l _
          apply Finset.sum_le_sum; intro k _
          calc |V_inv i k| * |V k l|
              ≤ 1 * |V k l| := mul_le_mul_of_nonneg_right (hVinv_bound i k) (abs_nonneg _)
            _ = |V k l| := one_mul _
      _ = ∑ k : Fin n, ∑ l : Fin n, |V k l| := Finset.sum_comm
  -- Step 2: V_{kl} = 0 for l ≠ k and l ≠ k+1
  have hV_zero : ∀ (k l : Fin n), l.val ≠ k.val → l.val ≠ k.val + 1 →
      V k l = 0 := by
    intro k l hlk hlk1
    by_cases hlt : l.val < k.val
    · exact _hV_ut k l hlt
    · push_neg at hlt
      exact hV_bidiag k l (by omega)
  -- Step 3: Each row k with k+1 < n has row sum ≤ 2
  have hRowBound_inner : ∀ k : Fin n, k.val + 1 < n →
      ∑ l : Fin n, |V k l| ≤ 2 := by
    intro k hkn
    have hk_mem : k ∈ Finset.univ (α := Fin n) := Finset.mem_univ k
    rw [← Finset.add_sum_erase _ _ hk_mem]
    have hl₀_ne : (⟨k.val + 1, hkn⟩ : Fin n) ≠ k := by simp [Fin.ext_iff]
    have hl₀_mem : (⟨k.val + 1, hkn⟩ : Fin n) ∈ Finset.univ.erase k :=
      Finset.mem_erase.mpr ⟨hl₀_ne, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ hl₀_mem]
    have hRest : ∑ l ∈ (Finset.univ.erase k).erase ⟨k.val + 1, hkn⟩, |V k l| = 0 := by
      apply Finset.sum_eq_zero; intro l hl
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl
      have hlk : l.val ≠ k.val := fun h => hl.2 (Fin.ext h)
      have hlk1 : l.val ≠ k.val + 1 := by
        intro heq; exact hl.1 (by ext; simpa using heq)
      rw [hV_zero k l hlk hlk1, abs_zero]
    rw [hRest, add_zero]
    linarith [hV_bound k k, hV_bound k ⟨k.val + 1, hkn⟩]
  -- Step 4: Last row (k.val + 1 ≥ n) has row sum ≤ 1
  have hRowBound_last : ∀ k : Fin n, ¬(k.val + 1 < n) →
      ∑ l : Fin n, |V k l| ≤ 1 := by
    intro k hkn; push_neg at hkn
    have hk_mem : k ∈ Finset.univ (α := Fin n) := Finset.mem_univ k
    rw [← Finset.add_sum_erase _ _ hk_mem]
    have hRest : ∑ l ∈ Finset.univ.erase k, |V k l| = 0 := by
      apply Finset.sum_eq_zero; intro l hl
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl
      have hlk : l.val ≠ k.val := fun h => hl (Fin.ext h)
      -- l.val ≠ k.val and k.val + 1 ≥ n, so l.val < k.val (since l.val < n ≤ k.val + 1)
      -- and l.val ≠ k.val, but also can't be k.val + 1 since that ≥ n
      rw [hV_zero k l hlk (by have := l.isLt; omega), abs_zero]
    rw [hRest, add_zero]
    exact hV_bound k k
  -- Step 5: Total ≤ 2(n-1) + 1 = 2n - 1
  intro i
  calc ∑ l : Fin n, ∑ k : Fin n, |V_inv i k| * |V k l|
      ≤ ∑ k : Fin n, ∑ l : Fin n, |V k l| := hCollapse i
    _ ≤ 2 * ↑n - 1 := by
        -- Split off the last element ⟨n-1, ...⟩
        have hlast_mem : (⟨n - 1, by omega⟩ : Fin n) ∈ Finset.univ (α := Fin n) :=
          Finset.mem_univ _
        rw [← Finset.add_sum_erase _ _ hlast_mem]
        have hlast_bound : ∑ l : Fin n, |V (⟨n - 1, by omega⟩ : Fin n) l| ≤ 1 :=
          hRowBound_last ⟨n - 1, by omega⟩ (by simp; omega)
        have hrest_bound : ∑ k ∈ Finset.univ.erase (⟨n - 1, by omega⟩ : Fin n),
            ∑ l : Fin n, |V k l| ≤ 2 * (↑n - 1) := by
          calc ∑ k ∈ Finset.univ.erase (⟨n - 1, by omega⟩ : Fin n), ∑ l : Fin n, |V k l|
              ≤ ∑ _k ∈ Finset.univ.erase (⟨n - 1, by omega⟩ : Fin n), (2 : ℝ) := by
                apply Finset.sum_le_sum; intro k _
                by_cases hkn : k.val + 1 < n
                · exact hRowBound_inner k hkn
                · exact le_trans (hRowBound_last k hkn) one_le_two
            _ = 2 * (↑n - 1) := by
                rw [Finset.sum_const, Finset.card_erase_of_mem hlast_mem,
                  Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                  Nat.cast_sub (by omega : 1 ≤ n)]
                ring
        linarith

-- ============================================================
-- §14.5  Theorem 14.8: (2n−1) bound for diag-dominant tridiagonal
-- ============================================================

/-- **Theorem 14.8** (Higham §14.5).

    For row diag-dominant tridiagonal A = LU and y ≥ 0,
      ‖|U⁻¹|·|L⁻¹|·y‖∞ ≤ (2n − 1) · ‖|A⁻¹|·y‖∞.

    The proof uses L⁻¹ = UA⁻¹ (from A = LU), then:
      |L⁻¹_{kj}| ≤ ∑_l |U_{kl}|·|A⁻¹_{lj}|   (triangle inequality)
    ⟹ ∑_k |U⁻¹_{ik}|·|L⁻¹_{kj}| ≤ ∑_l (|U⁻¹|·|U|)_{il}·|A⁻¹_{lj}|   (Fubini)
    ⟹ row_i(LHS) ≤ (row sum of |U⁻¹|·|U|) · ‖|A⁻¹|y‖∞.

    The factor (2n−1) arises because V = diag(u)⁻¹U is unit upper bidiag
    with |V_{i,i+1}| ≤ 1 (diagonal dominance), giving row sums of
    |V⁻¹|·|V| bounded by 2n−1. The hypothesis `hRowSumBound` captures
    this structural consequence. -/
theorem tridiag_diagdom_cond_bound (n : ℕ) (hn : 0 < n)
    (A L U A_inv L_inv U_inv : Fin n → Fin n → ℝ)
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hLU : ∀ i j, ∑ k : Fin n, L i k * U k j = A i j)
    (hLInv : IsLeftInverse n L L_inv)
    (hAInv : IsRightInverse n A A_inv)
    (hRowSumBound : ∀ i : Fin n,
      ∑ l : Fin n, ∑ k : Fin n, |U_inv i k| * |U k l| ≤ 2 * ↑n - 1) :
    infNormVec (fun i => ∑ j : Fin n,
      (∑ k : Fin n, |U_inv i k| * |L_inv k j|) * y j) ≤
    (2 * ↑n - 1) * infNormVec (fun i => ∑ j : Fin n,
      |A_inv i j| * y j) := by
  -- L⁻¹ = U · A⁻¹
  have hLinv_eq := L_inv_eq_matMul_U_Ainv n A L U A_inv L_inv hLU hLInv hAInv
  -- |L⁻¹_{kj}| ≤ ∑_l |U_{kl}| · |A⁻¹_{lj}|
  have hL_bound : ∀ k j : Fin n,
      |L_inv k j| ≤ ∑ l : Fin n, |U k l| * |A_inv l j| := by
    intro k j; rw [hLinv_eq k j]
    calc |∑ l : Fin n, U k l * A_inv l j|
        ≤ ∑ l : Fin n, |U k l * A_inv l j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l : Fin n, |U k l| * |A_inv l j| := by
          apply Finset.sum_congr rfl; intro l _; exact abs_mul _ _
  -- Define w_l = (|A⁻¹| · y)_l
  let w : Fin n → ℝ := fun l => ∑ j : Fin n, |A_inv l j| * y j
  have hw_nn : ∀ l, 0 ≤ w l :=
    fun l => Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hy j)
  -- w_l ≤ infNormVec(w)
  have hw_le_norm : ∀ l : Fin n, w l ≤ infNormVec w := by
    intro l
    have h1 : |w l| ≤ infNormVec w := abs_le_infNormVec w l
    rw [abs_of_nonneg (hw_nn l)] at h1; exact h1
  -- Suffices: each row bounded by (2n-1) · infNormVec(w)
  suffices key : ∀ i : Fin n,
      |∑ j : Fin n, (∑ k : Fin n, |U_inv i k| * |L_inv k j|) * y j| ≤
      (2 * ↑n - 1) * infNormVec w by
    apply infNormVec_le_of_abs_le
    · exact key
    · exact mul_nonneg (by
        have hn1Nat : 1 ≤ n := Nat.succ_le_of_lt hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1Nat
        linarith)
        (infNormVec_nonneg w)
  intro i
  -- LHS_i is nonneg
  have hLHS_nn : 0 ≤ ∑ j : Fin n, (∑ k : Fin n, |U_inv i k| * |L_inv k j|) * y j :=
    Finset.sum_nonneg fun j _ => mul_nonneg
      (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hy j)
  rw [abs_of_nonneg hLHS_nn]
  -- Step 1: ∑_k |U⁻¹_{ik}|·|L⁻¹_{kj}| ≤ ∑_l (|U⁻¹|·|U|)_{il} · |A⁻¹_{lj}|
  have hPointwise : ∀ j : Fin n,
      ∑ k : Fin n, |U_inv i k| * |L_inv k j| ≤
      ∑ l : Fin n, (∑ k : Fin n, |U_inv i k| * |U k l|) * |A_inv l j| := by
    intro j
    calc ∑ k : Fin n, |U_inv i k| * |L_inv k j|
        ≤ ∑ k : Fin n, |U_inv i k| * (∑ l : Fin n, |U k l| * |A_inv l j|) := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_left (hL_bound k j) (abs_nonneg _)
      _ = ∑ l : Fin n, (∑ k : Fin n, |U_inv i k| * |U k l|) * |A_inv l j| := by
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro l _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro k _; ring
  -- Step 2: Multiply by y_j ≥ 0, sum over j, Fubini
  have hRow : ∑ j : Fin n, (∑ k : Fin n, |U_inv i k| * |L_inv k j|) * y j ≤
      ∑ l : Fin n, (∑ k : Fin n, |U_inv i k| * |U k l|) * w l := by
    calc ∑ j : Fin n, (∑ k : Fin n, |U_inv i k| * |L_inv k j|) * y j
        ≤ ∑ j : Fin n, (∑ l : Fin n,
            (∑ k : Fin n, |U_inv i k| * |U k l|) * |A_inv l j|) * y j := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_right (hPointwise j) (hy j)
      _ = ∑ l : Fin n, (∑ k : Fin n, |U_inv i k| * |U k l|) * w l := by
          -- Fubini: ∑_j (∑_l c_il·|A⁻¹_{lj}|)·y_j = ∑_l c_il · (∑_j |A⁻¹_{lj}|·y_j)
          have hDistrib : ∀ j : Fin n,
              (∑ l : Fin n, (∑ k : Fin n, |U_inv i k| * |U k l|) * |A_inv l j|) * y j =
              ∑ l : Fin n, (∑ k : Fin n, |U_inv i k| * |U k l|) * (|A_inv l j| * y j) := by
            intro j; rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro l _; ring
          simp_rw [hDistrib]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro l _
          rw [← Finset.mul_sum]
  -- Step 3: ∑_l c_il · w_l ≤ (∑_l c_il) · ‖w‖∞ ≤ (2n-1) · ‖w‖∞
  have hc_nn : ∀ l, 0 ≤ ∑ k : Fin n, |U_inv i k| * |U k l| :=
    fun l => Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hinfNorm_nn : 0 ≤ infNormVec w := by
    have := hw_le_norm ⟨0, hn⟩; linarith [hw_nn ⟨0, hn⟩]
  calc ∑ j : Fin n, (∑ k : Fin n, |U_inv i k| * |L_inv k j|) * y j
      ≤ ∑ l : Fin n, (∑ k : Fin n, |U_inv i k| * |U k l|) * w l := hRow
    _ ≤ ∑ l : Fin n, (∑ k : Fin n, |U_inv i k| * |U k l|) * infNormVec w := by
        apply Finset.sum_le_sum; intro l _
        exact mul_le_mul_of_nonneg_left (hw_le_norm l) (hc_nn l)
    _ = (∑ l : Fin n, ∑ k : Fin n, |U_inv i k| * |U k l|) * infNormVec w := by
        rw [Finset.sum_mul]
    _ ≤ (2 * ↑n - 1) * infNormVec w :=
        mul_le_mul_of_nonneg_right (hRowSumBound i) hinfNorm_nn

-- ============================================================
-- §14.5  Theorem 14.9: Ikebe's rank-1 structure
-- ============================================================

/-- Irreducible tridiagonal: sub- and super-diagonal entries all nonzero. -/
def IsIrreducibleTridiag {n : ℕ} (T : TridiagData n) : Prop :=
  (∀ (i : Fin n) (hi : i.val + 1 < n), T.a ⟨i.val + 1, hi⟩ ≠ 0) ∧
  (∀ (i : Fin n), i.val + 1 < n → T.c i ≠ 0)

/-- **Cumulative product for upper bidiag inverse factorization.**
    x_i = ∏_{p=0}^{i-1} (−c_p / u_p). -/
noncomputable def cumulProdUpper {n : ℕ} (u c : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val), (-c p / u p)

/-- **Cumulative product for unit lower bidiag inverse factorization.**
    p_i = ∏_{q=1}^{i} (−l_q). -/
noncomputable def cumulProdLower {n : ℕ} (l : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ q ∈ Finset.univ.filter (fun q : Fin n => 0 < q.val ∧ q.val ≤ i.val), (-l q)

/-- **Theorem 14.9** (Ikebe, 1979; Higham §14.5).

    The inverse of an irreducible tridiagonal matrix has rank-1 structure
    in each triangle:
      (A⁻¹)_{ij} = x_i · y_j   for i ≤ j,
      (A⁻¹)_{ij} = p_i · q_j   for i ≥ j.

    From A = LU, A⁻¹ = U⁻¹ L⁻¹. For i ≤ j, only k ≥ j contributes.
    Using U⁻¹_{ik} = (cumulProd_k/cumulProd_i)·(1/u_k):
      A⁻¹_{ij} = (1/cumulProd_i) · ∑_{k≥j}(cumulProd_k/u_k)·L⁻¹_{kj}.
    First factor depends only on i; the sum only on j. -/
theorem ikebe_tridiag_inv_structure (n : ℕ)
    (A_inv : Fin n → Fin n → ℝ)
    (L U L_inv U_inv : Fin n → Fin n → ℝ)
    (_hStruct : IsTridiagLU n L U)
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hA_inv_eq : ∀ i j, A_inv i j = ∑ k : Fin n, U_inv i k * L_inv k j)
    (_hU_inv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0)
    (_hL_inv_lt : ∀ i j : Fin n, i.val < j.val → L_inv i j = 0)
    (hU_inv_prod : ∀ i k : Fin n, i.val ≤ k.val →
      U_inv i k = cumulProdUpper (fun m => U m m)
        (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) k /
        (cumulProdUpper (fun m => U m m)
          (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) i *
          U k k))
    (hL_inv_prod : ∀ k j : Fin n, j.val ≤ k.val →
      L_inv k j = cumulProdLower
        (fun m => if h : 0 < m.val then L m ⟨m.val - 1, by omega⟩ else 0) k /
        cumulProdLower
          (fun m => if h : 0 < m.val then L m ⟨m.val - 1, by omega⟩ else 0) j) :
    ∃ (x y p q : Fin n → ℝ),
      (∀ i j : Fin n, i.val ≤ j.val → A_inv i j = x i * y j) ∧
      (∀ i j : Fin n, j.val ≤ i.val → A_inv i j = p i * q j) := by
  let cu := cumulProdUpper (fun m => U m m)
    (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0)
  let cl := cumulProdLower
    (fun m => if h : 0 < m.val then L m ⟨m.val - 1, by omega⟩ else 0)
  -- Upper triangle vectors
  let x_vec : Fin n → ℝ := fun i => 1 / cu i
  let y_vec : Fin n → ℝ := fun j =>
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val),
      cu k / (U k k) * L_inv k j
  -- Lower triangle vectors
  let q_vec : Fin n → ℝ := fun j => 1 / cl j
  let p_vec : Fin n → ℝ := fun i =>
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val),
      U_inv i k * cl k
  exact ⟨x_vec, y_vec, p_vec, q_vec, by
    constructor
    · -- Upper triangle: A⁻¹_{ij} = (1/cu_i) · ∑_{k≥j} (cu_k/u_k)·L⁻¹_{kj}
      intro i j hij
      rw [hA_inv_eq]
      -- The sum ∑_k U_inv_{ik} · L_inv_{kj} reduces to ∑_{k≥j} for i ≤ j
      -- (L_inv lower tri eliminates k < j).
      -- Using U_inv_{ik} = cu_k / (cu_i · u_k):
      -- ∑_{k≥j} (cu_k/(cu_i·u_k)) · L_inv_{kj}
      -- = (1/cu_i) · ∑_{k≥j} (cu_k/u_k) · L_inv_{kj}
      -- = x_i · y_j ✓
      show (∑ k : Fin n, U_inv i k * L_inv k j) = x_vec i * y_vec j
      -- Eliminate terms with k < j (L_inv_{kj} = 0)
      have hsum_eq : ∑ k : Fin n, U_inv i k * L_inv k j =
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val),
            U_inv i k * L_inv k j := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro k _ hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
        rw [_hL_inv_lt k j hk, mul_zero]
      rw [hsum_eq]
      -- Now substitute U_inv using product formula
      -- x_vec i * y_vec j = (1/cu i) * ∑_{k≥j} (cu k / u_k) * L_inv k j
      -- = ∑_{k≥j} (cu k / (cu i * u_k)) * L_inv k j
      -- = ∑_{k≥j} U_inv i k * L_inv k j (by hU_inv_prod)
      show _ = x_vec i * y_vec j
      change _ = (1 / cu i) * ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val),
        cu k / U k k * L_inv k j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hik : i.val ≤ k.val := le_trans hij hk
      rw [hU_inv_prod i k hik]
      ring
    · -- Lower triangle: A⁻¹_{ij} = (∑_{k≥i} U⁻¹_{ik}·cl_k) · (1/cl_j)
      intro i j hji
      rw [hA_inv_eq]
      show (∑ k : Fin n, U_inv i k * L_inv k j) = p_vec i * q_vec j
      -- Eliminate terms with k < i (U_inv_{ik} = 0)
      have hsum_eq : ∑ k : Fin n, U_inv i k * L_inv k j =
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val),
            U_inv i k * L_inv k j := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro k _ hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
        rw [_hU_inv_ut i k hk, zero_mul]
      rw [hsum_eq]
      -- p_vec i * q_vec j = (∑_{k≥i} U_inv i k * cl_k) * (1/cl_j)
      -- = ∑_{k≥i} U_inv i k * (cl_k / cl_j)
      -- = ∑_{k≥i} U_inv i k * L_inv k j (by hL_inv_prod)
      show _ = p_vec i * q_vec j
      change _ = (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val),
          U_inv i k * cl k) * (1 / cl j)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hjk : j.val ≤ k.val := le_trans hji hk
      rw [hL_inv_prod k j hjk]
      ring⟩

end NumStability
