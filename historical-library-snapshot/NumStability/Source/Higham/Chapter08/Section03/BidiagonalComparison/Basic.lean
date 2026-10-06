import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsUpper
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter08 Section03 BidiagonalComparison Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- An upper-triangular matrix is upper bidiagonal when entries more than one
place above the diagonal vanish. -/
def IsUpperBidiagonal (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i.val + 1 < j.val → U i j = 0

/-- Higham, 2nd ed., section 8.3, p. 148: for a nonsingular upper bidiagonal
matrix `U`, the absolute value of its inverse is exactly the inverse of its
comparison matrix, `|U⁻¹| = M(U)⁻¹`.

The proof strengthens the first inequality of Theorem 8.12.  In the inverse
recurrence every row has at most one off-diagonal contribution, so the triangle
inequality used for a general triangular matrix is an equality. -/
theorem higham8_bidiagonal_abs_inv_eq_comparison_inv
    (n : ℕ) (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUB : IsUpperBidiagonal n U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hMInv : IsInverse n (comparisonMatrix n U) M_inv) :
    ∀ i j : Fin n, |U_inv i j| = M_inv i j := by
  have hU_inv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    have hne : i ≠ j := by
      intro h
      subst j
      omega
    simp [comparisonMatrix, hne, hUT i j hij]
  have hM_diag : ∀ i : Fin n, comparisonMatrix n U i i ≠ 0 := by
    intro i
    simpa [comparisonMatrix] using hU_diag i
  have hM_inv_ut := inv_upper_tri n (comparisonMatrix n U) M_inv
    hM_ut hM_diag hMInv.1
  have hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j := by
    apply upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
    · exact hM_ut
    · intro i
      simpa [comparisonMatrix] using (abs_pos.mpr (hU_diag i))
    · intro i j hij
      have hne : i ≠ j := by
        intro h
        subst j
        omega
      simp [comparisonMatrix, hne]
    · exact hMInv.2
    · exact hM_inv_ut
  suffices h : ∀ d : ℕ, ∀ i j : Fin n,
      j.val - i.val ≤ d → i.val ≤ j.val → |U_inv i j| = M_inv i j by
    intro i j
    by_cases hij : i.val ≤ j.val
    · exact h (j.val - i.val) i j le_rfl hij
    · have hji : j.val < i.val := by omega
      rw [hU_inv_ut i j hji, hM_inv_ut i j hji, abs_zero]
  intro d
  induction d with
  | zero =>
      intro i j hdist hij
      have hij_eq : i = j := Fin.ext (by omega)
      subst j
      have hUdiag := inv_diag_entry n U U_inv hUT hU_diag hInv.1 hU_inv_ut i
      have hMdiag := inv_diag_entry n (comparisonMatrix n U) M_inv
        hM_ut hM_diag hMInv.1 hM_inv_ut i
      rw [hUdiag, hMdiag, abs_div, abs_one]
      simp [comparisonMatrix]
  | succ d ih =>
      intro i j hdist hij
      by_cases heq : i = j
      · subst j
        exact ih i i (by omega) le_rfl
      · have hij_lt : i.val < j.val := by omega
        let ip1 : Fin n := ⟨i.val + 1, by omega⟩
        let S : Finset (Fin n) :=
          Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val)
        have hip1_mem : ip1 ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · simp [ip1]
          · change i.val + 1 ≤ j.val
            exact Nat.succ_le_iff.mpr hij_lt
        have hsumU :
            (∑ k ∈ S, U i k * U_inv k j) = U i ip1 * U_inv ip1 j := by
          apply Finset.sum_eq_single ip1
          · intro k hk hki
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
            have hfar : i.val + 1 < k.val := by
              have hneval : k.val ≠ i.val + 1 := by
                intro hkval
                apply hki
                exact Fin.ext hkval
              omega
            rw [hUB i k hfar, zero_mul]
          · exact fun hnot => (hnot hip1_mem).elim
        have hsumM :
            (∑ k ∈ S, comparisonMatrix n U i k * M_inv k j) =
              comparisonMatrix n U i ip1 * M_inv ip1 j := by
          apply Finset.sum_eq_single ip1
          · intro k hk hki
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
            have hfar : i.val + 1 < k.val := by
              have hneval : k.val ≠ i.val + 1 := by
                intro hkval
                apply hki
                exact Fin.ext hkval
              omega
            have hzero := hUB i k hfar
            have hik : i ≠ k := by
              intro h
              subst k
              omega
            simp [comparisonMatrix, hik, hzero]
          · exact fun hnot => (hnot hip1_mem).elim
        have hrecU := inv_recurrence n U U_inv hUT hU_diag hInv.2
          hU_inv_ut i j hij_lt
        have hrecM := inv_recurrence n (comparisonMatrix n U) M_inv hM_ut
          hM_diag hMInv.2 hM_inv_ut i j hij_lt
        change U i i * U_inv i j + (∑ k ∈ S, U i k * U_inv k j) = 0 at hrecU
        change comparisonMatrix n U i i * M_inv i j +
          (∑ k ∈ S, comparisonMatrix n U i k * M_inv k j) = 0 at hrecM
        rw [hsumU] at hrecU
        rw [hsumM] at hrecM
        have hipdist : j.val - ip1.val ≤ d := by
          change j.val - (i.val + 1) ≤ d
          omega
        have hip_le : ip1.val ≤ j.val := by
          dsimp [ip1]
          omega
        have ih_abs : |U_inv ip1 j| = M_inv ip1 j :=
          ih ip1 j hipdist hip_le
        have hUii_abs_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
        have hUeq : U_inv i j = -(U i ip1 * U_inv ip1 j) / U i i := by
          field_simp [hU_diag i]
          linarith
        have hMeq : M_inv i j =
            |U i ip1| * M_inv ip1 j / |U i i| := by
          have hii : comparisonMatrix n U i i = |U i i| := by
            simp [comparisonMatrix]
          have hip : comparisonMatrix n U i ip1 = -|U i ip1| := by
            have hne : i ≠ ip1 := by
              intro h
              have hval := congrArg Fin.val h
              dsimp [ip1] at hval
              omega
            simp [comparisonMatrix, hne]
          rw [hii, hip] at hrecM
          field_simp [ne_of_gt hUii_abs_pos]
          linarith
        rw [hUeq, abs_div, abs_neg, abs_mul, ih_abs, hMeq]

/-- Matrix form of `higham8_bidiagonal_abs_inv_eq_comparison_inv`. -/
theorem higham8_bidiagonal_absMatrix_inv_eq_comparison_inv
    (n : ℕ) (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUB : IsUpperBidiagonal n U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hMInv : IsInverse n (comparisonMatrix n U) M_inv) :
    absMatrix n U_inv = M_inv := by
  funext i j
  exact higham8_bidiagonal_abs_inv_eq_comparison_inv
    n U U_inv M_inv hUT hUB hU_diag hInv hMInv i j

/-- For an upper bidiagonal matrix, Algorithm 8.13 is exact rather than merely
an upper bound: its comparison-inverse output is `‖U⁻¹‖∞` itself. -/
theorem higham8_bidiagonal_algorithm8_13_mu_eq_inverse_infNorm
    (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUB : IsUpperBidiagonal n U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hMInv : IsInverse n (comparisonMatrix n U) M_inv) :
    higham8_13_mu M_inv = infNorm U_inv := by
  unfold higham8_13_mu
  rw [← higham8_bidiagonal_absMatrix_inv_eq_comparison_inv
    n U U_inv M_inv hUT hUB hU_diag hInv hMInv]
  exact infNorm_absMatrix hn U_inv

/-- In the bidiagonal case the comparison solve used by Algorithm 8.13 has
only one dependency per row.  This is the exact descending two-term
recurrence that gives the source's `O(n)` computation. -/
theorem higham8_bidiagonal_algorithm8_13_two_term_recurrence
    (n : ℕ) (U M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUB : IsUpperBidiagonal n U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (i : Fin n) :
    |U i i| * higham8_13_y M_inv i =
      1 + if hi : i.val + 1 < n then
        |U i ⟨i.val + 1, hi⟩| * higham8_13_y M_inv ⟨i.val + 1, hi⟩
      else 0 := by
  have hrec := higham8_13_comparison_inverse_row_recurrence
    n U M_inv hUT hU_diag hM_RInv i
  rw [hrec]
  split_ifs with hi
  · let ip1 : Fin n := ⟨i.val + 1, hi⟩
    let S : Finset (Fin n) :=
      Finset.univ.filter (fun j : Fin n => i.val < j.val)
    have hip1_mem : ip1 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      change i.val < i.val + 1
      omega
    have hsum :
        (∑ j ∈ S, |U i j| * higham8_13_y M_inv j) =
          |U i ip1| * higham8_13_y M_inv ip1 := by
      apply Finset.sum_eq_single ip1
      · intro j hj hne
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hfar : i.val + 1 < j.val := by
          have hval : j.val ≠ i.val + 1 := by
            intro h
            apply hne
            exact Fin.ext h
          omega
        rw [hUB i j hfar, abs_zero, zero_mul]
      · exact fun hnot => (hnot hip1_mem).elim
    simpa [S, ip1] using hsum
  · have hfilter_empty :
        Finset.univ.filter (fun j : Fin n => i.val < j.val) = ∅ := by
      ext j
      simp
      omega
    rw [hfilter_empty]
    simp

end NumStability
