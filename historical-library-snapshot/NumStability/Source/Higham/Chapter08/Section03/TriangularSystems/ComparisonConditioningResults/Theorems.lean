-- NumStability/Source/Higham/Chapter08/Section03/TriangularSystems/ComparisonConditioningResults/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Algorithms.HighamChapter8`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Interval.Finset.Fin
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.Triangular
import NumStability.Algorithms.MMatrix
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ArbitraryOrder
import NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.All
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ForwardErrorKernels
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Exact
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem04
import NumStability.Source.Higham.Chapter08.Equation14.FanInExecutor.Executor
import NumStability.Source.Higham.Chapter08.Lemma08.CorrectedCondition.RowDominance
import NumStability.Source.Higham.Chapter08.Lemma08.Entrywise.Basic
import NumStability.Source.Higham.Chapter08.Problem01.NoGuardSubstitution.Aliases
import NumStability.Source.Higham.Chapter08.Problem02.ComparisonMatrixWitness.RatioWitness
import NumStability.Source.Higham.Chapter08.Problem03.UnitTriangularSubstitution.Bound
import NumStability.Source.Higham.Chapter08.Problem04.MMatrixSubstitution.Comparison
import NumStability.Source.Higham.Chapter08.Problem05.InverseNormBounds.ZInverse
import NumStability.Source.Higham.Chapter08.Problem06.ComparisonInverseBounds.VectorBounds
import NumStability.Source.Higham.Chapter08.Problem07.DiagonalScaling.Bounds
import NumStability.Source.Higham.Chapter08.Problem08.SingleEntrySingularity.RankOne
import NumStability.Source.Higham.Chapter08.Problem09.KahanSingularValues.KahanMatrix
import NumStability.Source.Higham.Chapter08.Section01.BackwardErrorAnalysis.Core
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBounds
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.NormBounds
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsLower
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsUpper
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.AllOrdersEnvelope
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.Factors
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.ResidualForwardBounds

/-!
# Theorems

Relocated from `NumStability.Algorithms.HighamChapter8` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


-- Algorithms/HighamChapter8.lean
--
-- Source-facing entry points for Higham Chapter 8, "Triangular Systems".
-- The detailed proofs remain in the focused triangular-system modules; this
-- file provides stable chapter labels and light wrappers around those results.















namespace NumStability

open scoped BigOperators

/-! ## §8.1 Backward Error Analysis -/

















































































































/-! ## §8.2 Forward Error Analysis -/



































































































































































































































/-- The absolute value of the comparison matrix agrees entrywise with `|T|`. -/
private lemma comparisonMatrix_abs_apply (n : ℕ) (T : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    |comparisonMatrix n T i j| = |T i j| := by
  by_cases hij : i = j
  · subst hij
    simp [comparisonMatrix]
  · simp [comparisonMatrix, hij]


/-- Entrywise decomposition of `|M(T)|` as `2 diag(|t_ii|) - M(T)`. -/
private lemma comparisonMatrix_abs_eq_two_diag_sub (n : ℕ) (T : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    |comparisonMatrix n T i j| =
      2 * diagMatrix (fun k : Fin n => |T k k|) i j - comparisonMatrix n T i j := by
  by_cases hij : i = j
  · subst hij
    simp [comparisonMatrix, diagMatrix]
    ring
  · simp [comparisonMatrix, diagMatrix, hij]








/-- **Lemma 8.9**, equality part for the comparison matrix:
`cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_comparisonMatrix_condAtSolution_eq (n : ℕ) (hn : 0 < n)
    (T M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j)
    (hM_left : IsLeftInverse n (comparisonMatrix n T) M_inv) :
    ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x =
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have hdiagMul :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k =
          M_inv i k * |T k k| := by
    intro i k
    simpa [matMul] using
      matMul_diagMatrix_right M_inv (fun l : Fin n => |T l l|) i k
  have hleftEntry :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * comparisonMatrix n T j k = idMatrix n i k := by
    intro i k
    simpa [idMatrix] using hM_left i k
  have hcomparisonEntry :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k| =
          2 * (M_inv i k * |T k k|) - idMatrix n i k := by
    intro i k
    calc
      ∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k|
          = ∑ j : Fin n,
              (2 * (M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k) -
                M_inv i j * comparisonMatrix n T j k) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [comparisonMatrix_abs_eq_two_diag_sub n T j k]
              ring
      _ = 2 * ∑ j : Fin n, M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k -
            ∑ j : Fin n, M_inv i j * comparisonMatrix n T j k := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * (M_inv i k * |T k k|) - idMatrix n i k := by
            rw [hdiagMul i k, hleftEntry i k]
  have happly :
      ∀ i : Fin n,
        ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
            (fun _ => 0) x i =
          higham8_9_comparisonImage n T M_inv x i := by
    intro i
    unfold ch7AmplifiedRhsEF higham8_9_comparisonImage
    calc
      ∑ j : Fin n, |M_inv i j| *
          (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0)
          = ∑ j : Fin n, M_inv i j *
              ∑ k : Fin n, |comparisonMatrix n T j k| * |x k| := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_of_nonneg (hM_nonneg i j)]
              simp
      _ = ∑ k : Fin n,
            (∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k|) * |x k| := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ k : Fin n,
            (2 * (M_inv i k * |T k k|) - idMatrix n i k) * |x k| := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hcomparisonEntry i k]
      _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| -
            ∑ k : Fin n, idMatrix n i k * |x k| := by
            calc
              ∑ k : Fin n, (2 * (M_inv i k * |T k k|) - idMatrix n i k) * |x k|
                  = ∑ k : Fin n,
                      (2 * (M_inv i k * |T k k| * |x k|) -
                        idMatrix n i k * |x k|) := by
                        apply Finset.sum_congr rfl
                        intro k _
                        ring
              _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| -
                    ∑ k : Fin n, idMatrix n i k * |x k| := by
                      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| - |x i| := by
            simp [idMatrix]
  have hnonneg :
      ∀ i : Fin n, 0 ≤ higham8_9_comparisonImage n T M_inv x i := by
    intro i
    rw [← happly i]
    exact
      ch7AmplifiedRhsEF_nonneg n M_inv
        (fun a b => |comparisonMatrix n T a b|) (fun _ => 0) x
        (by
          intro a b
          exact abs_nonneg _)
        (by
          intro a
          simp)
        i
  have hforward :
      ch7ForwardBoundEF n hn M_inv (fun a b => |comparisonMatrix n T a b|)
          (fun _ => 0) x =
        infNormVec (higham8_9_comparisonImage n T M_inv x) := by
    unfold ch7ForwardBoundEF
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      rw [happly i, ← abs_of_nonneg (hnonneg i)]
      exact abs_le_infNormVec (higham8_9_comparisonImage n T M_inv x) i
    · apply infNormVec_le_of_abs_le
      · intro i
        rw [abs_of_nonneg (hnonneg i), ← happly i]
        exact
          Finset.le_sup'
            (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
              (fun _ => 0) x)
            (Finset.mem_univ i)
      · exact
          ch7ForwardBoundEF_nonneg n hn M_inv
            (fun a b => |comparisonMatrix n T a b|) (fun _ => 0) x
            (by
              intro a b
              exact abs_nonneg _)
            (by
              intro a
              simp)
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
  rw [hforward]


/-- **Lemma 8.9**, inequality part:
`cond(T,x) ≤ cond(M(T),x)` once `|T⁻¹| ≤ M(T)⁻¹` and `M(T)⁻¹ ≥ 0` are known. -/
theorem higham8_9_condAtSolution_le_comparisonMatrix (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (habsInv : ∀ i j : Fin n, |T_inv i j| ≤ M_inv i j)
    (hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := by
  have hnum :
      ch7ForwardBoundEF n hn T_inv (fun a b => |T a b|) (fun _ => 0) x ≤
        ch7ForwardBoundEF n hn M_inv (fun a b => |comparisonMatrix n T a b|)
          (fun _ => 0) x := by
    unfold ch7ForwardBoundEF
    apply Finset.sup'_le
    intro i _
    unfold ch7AmplifiedRhsEF
    calc
      ∑ j : Fin n, |T_inv i j| * (∑ k : Fin n, |T j k| * |x k| + 0)
          ≤ ∑ j : Fin n, M_inv i j * (∑ k : Fin n, |T j k| * |x k| + 0) := by
              apply Finset.sum_le_sum
              intro j _
              have hinner_nonneg : 0 ≤ ∑ k : Fin n, |T j k| * |x k| + 0 := by
                positivity
              exact mul_le_mul_of_nonneg_right (habsInv i j) hinner_nonneg
      _ = ∑ j : Fin n, M_inv i j *
            (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0) := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            have hsumEq :
                ∑ k : Fin n, |T j k| * |x k| =
                  ∑ k : Fin n, |comparisonMatrix n T j k| * |x k| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [comparisonMatrix_abs_apply]
            rw [hsumEq]
      _ = ∑ j : Fin n, |M_inv i j| *
            (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hM_nonneg i j)]
      _ = ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
            (fun _ => 0) x i := by
            rfl
      _ ≤ Finset.sup' Finset.univ
            (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
            (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
              (fun _ => 0) x) := by
            exact
              Finset.le_sup'
                (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
                  (fun _ => 0) x)
                (Finset.mem_univ i)
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
  exact div_le_div_of_nonneg_right hnum (infNormVec_nonneg x)


/-- **Lemma 8.9**, upper-triangular source wrapper:
`cond(T,x) ≤ cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_upperTriangular_condAtSolution_le_comparison_eq (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag : ∀ i : Fin n, T i i ≠ 0)
    (hInv : IsInverse n T T_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n T) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have habsInv :=
    abs_inv_le_compMatrix_inv n T T_inv M_inv
      hUT hT_diag hInv hM_RInv hM_inv_ut
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n T i i := by
    intro i
    simp [comparisonMatrix]
    exact hT_diag i
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n T i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n T i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n T) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hle :=
    higham8_9_condAtSolution_le_comparisonMatrix n hn T T_inv M_inv x habsInv hM_nonneg
  have heq :=
    higham8_9_comparisonMatrix_condAtSolution_eq n hn T M_inv x
      hM_nonneg (ch7_isLeftInverse_of_isRightInverse hM_RInv)
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := hle
    _ = infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := heq


/-- **Lemma 8.9**, lower-triangular source wrapper:
`cond(T,x) ≤ cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_lowerTriangular_condAtSolution_le_comparison_eq (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → T i j = 0)
    (hT_diag : ∀ i : Fin n, T i i ≠ 0)
    (hInv : IsInverse n T T_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n T) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have habsInv :=
    abs_inv_le_compMatrix_inv_lowerTri n T T_inv M_inv
      hLT hT_diag hInv hM_RInv hM_inv_lt
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n T i i := by
    intro i
    simp [comparisonMatrix]
    exact hT_diag i
  have hM_offdiag : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n T i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_lt : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n T i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hLT i j hij]
  have hM_nonneg :=
    lower_tri_mmatrix_inv_nonneg n (comparisonMatrix n T) M_inv
      hM_lt hM_diag_pos hM_offdiag hM_RInv hM_inv_lt
  have hle :=
    higham8_9_condAtSolution_le_comparisonMatrix n hn T T_inv M_inv x habsInv hM_nonneg
  have heq :=
    higham8_9_comparisonMatrix_condAtSolution_eq n hn T M_inv x
      hM_nonneg (ch7_isLeftInverse_of_isRightInverse hM_RInv)
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := hle
    _ = infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := heq





































































































































































/-- An upper-triangular row sum over `univ.erase i` only sees the strict-upper
entries. -/
private lemma higham8_upperTriangular_erase_sum_eq_strictUpper (n : ℕ)
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


/-- For an upper triangular M-matrix, the comparison matrix equals the matrix
itself. -/
private theorem higham8_comparisonMatrix_eq_self_upper (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0) :
    comparisonMatrix n T = T := by
  funext i j
  unfold comparisonMatrix
  by_cases hij : i = j
  · subst hij
    simp [abs_of_pos (hT_diag_pos i)]
  · by_cases hij' : i.val < j.val
    · rw [abs_of_nonpos (hT_offdiag i j hij')]
      simp [hij]
    · have hji : j.val < i.val := by omega
      simp [hij, hUT i j hji]


/-- Exact solutions of upper-triangular M-matrix systems with nonnegative
right-hand side are nonnegative. -/
private theorem higham8_upperTriangularMMatrix_solution_nonneg (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i) :
    ∀ i, 0 ≤ x i := by
  have hT_diag : ∀ i : Fin n, T i i ≠ 0 := fun i => ne_of_gt (hT_diag_pos i)
  have hInv_ut := inv_upper_tri n T T_inv hUT hT_diag hInv.1
  have hTinv_nonneg :=
    upper_tri_mmatrix_inv_nonneg n T T_inv
      hUT hT_diag_pos hT_offdiag hInv.2 hInv_ut
  have hx_eq : ∀ i : Fin n, x i = ∑ j : Fin n, T_inv i j * b j := by
    intro i
    have hLI := hInv.1 i
    have hsum :
        ∑ j : Fin n, T_inv i j * b j =
          ∑ j : Fin n, T_inv i j * (∑ k : Fin n, T j k * x k) := by
      congr 1
      funext j
      rw [hTx j]
    rw [hsum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have hsimp : ∀ k : Fin n,
        (∑ j : Fin n, T_inv i j * T j k) * x k = (if i = k then 1 else 0) * x k := by
      intro k
      congr 1
      exact hLI k
    simp_rw [hsimp]
    simp [Finset.mem_univ]
  intro i
  rw [hx_eq i]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hTinv_nonneg i j) (hb j))


/-- Problem 8.4 row identity for the comparison-image vector under the
upper-triangular M-matrix assumptions. -/
private theorem higham8_problem8_4_comparisonImage_row_eq (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (_hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    let y := higham8_9_comparisonImage n T T_inv x
    ∀ i : Fin n,
      T i i * y i =
        T i i * x i +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j := by
  intro y i
  have hy_simp : ∀ j : Fin n,
      y j = 2 * ∑ k : Fin n, T_inv j k * T k k * x k - x j := by
    intro j
    unfold y higham8_9_comparisonImage
    rw [abs_of_nonneg (hx_nonneg j)]
    apply congrArg (fun z => 2 * z - x j)
    apply Finset.sum_congr rfl
    intro k _
    rw [abs_of_pos (hT_diag_pos k), abs_of_nonneg (hx_nonneg k)]
  have hTy : ∀ i : Fin n, ∑ j : Fin n, T i j * y j = 2 * T i i * x i - b i := by
    intro i
    calc
      ∑ j : Fin n, T i j * y j
          = ∑ j : Fin n, T i j * (2 * ∑ k : Fin n, T_inv j k * T k k * x k - x j) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hy_simp j]
      _ = ∑ j : Fin n,
            (2 * (T i j * ∑ k : Fin n, T_inv j k * T k k * x k) - T i j * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = 2 * ∑ j : Fin n, T i j * ∑ k : Fin n, T_inv j k * T k k * x k -
            ∑ j : Fin n, T i j * x j := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k -
            ∑ j : Fin n, T i j * x j := by
              have hswap :
                  ∑ j : Fin n, T i j * ∑ k : Fin n, T_inv j k * T k k * x k
                    = ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k := by
                calc
                  ∑ j : Fin n, T i j * ∑ k : Fin n, T_inv j k * T k k * x k
                      = ∑ k : Fin n, ∑ j : Fin n, T i j * (T_inv j k * T k k * x k) := by
                          simp_rw [Finset.mul_sum]
                          rw [Finset.sum_comm]
                  _ = ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k := by
                        apply Finset.sum_congr rfl
                        intro k _
                        calc
                          ∑ j : Fin n, T i j * (T_inv j k * T k k * x k)
                              = ∑ j : Fin n, (T i j * T_inv j k) * (T k k * x k) := by
                                  apply Finset.sum_congr rfl
                                  intro j _
                                  ring
                          _ = (∑ j : Fin n, T i j * T_inv j k) * (T k k * x k) := by
                                  rw [Finset.sum_mul]
                          _ = (∑ j : Fin n, T i j * T_inv j k) * T k k * x k := by
                                  ring
              rw [hswap]
      _ = 2 * ∑ k : Fin n, idMatrix n i k * T k k * x k -
            ∑ j : Fin n, T i j * x j := by
              have hid :
                  ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k
                    = ∑ k : Fin n, idMatrix n i k * T k k * x k := by
                apply Finset.sum_congr rfl
                intro k _
                have hright := congrArg (fun z => z * (T k k * x k)) (hInv.2 i k)
                simpa [idMatrix, mul_assoc] using hright
              rw [hid]
      _ = 2 * (T i i * x i) - b i := by
              rw [hTx i]
              simp [idMatrix]
      _ = 2 * T i i * x i - b i := by
              ring
  have hTx_split :
      T i i * x i +
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * x j = b i := by
    have h := hTx i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    rw [higham8_upperTriangular_erase_sum_eq_strictUpper n T hUT i x] at h
    simpa using h
  have hTy_split :
      T i i * y i +
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * y j =
          2 * T i i * x i - b i := by
    have h := hTy i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    rw [higham8_upperTriangular_erase_sum_eq_strictUpper n T hUT i y] at h
    simpa using h
  have hTx_pos :
      T i i * x i =
        b i +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j := by
    have hsum :
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * x j =
          -∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum] at hTx_split
    linarith
  have hTy_pos :
      T i i * y i =
        2 * T i i * x i - b i +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j := by
    have hsum :
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * y j =
          -∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum] at hTy_split
    linarith
  linarith


/-- Problem 8.4 componentwise bound for the comparison-image vector:
`(2T⁻¹ diag(t_ii) - I)x ≤ (2(n-i)-1) x`. -/
private theorem higham8_problem8_4_comparisonImage_nonneg_bound (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    let y := higham8_9_comparisonImage n T T_inv x
    ∀ i : Fin n,
      0 ≤ y i ∧
      y i ≤ (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) * x i := by
  intro y
  have hrow :=
    higham8_problem8_4_comparisonImage_row_eq n T T_inv x b
      hUT hT_diag_pos hT_offdiag hInv hTx hx_nonneg
  suffices h :
      ∀ d : ℕ, ∀ i : Fin n, n - 1 - i.val ≤ d →
        0 ≤ y i ∧ y i ≤ (((2 * d + 1 : ℕ) : ℝ)) * x i by
    intro i
    simpa using h (n - 1 - i.val) i (le_refl _)
  intro d
  induction d with
  | zero =>
      intro i hi
      have hi_last : i.val = n - 1 := by omega
      have hsumx_zero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        omega
      have hsumy_zero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        omega
      have hy_eq : y i = x i := by
        have hscaled : T i i * y i = T i i * x i := by
          have hrowi := hrow i
          rw [hsumx_zero, hsumy_zero, add_zero, add_zero] at hrowi
          simpa [y] using hrowi
        exact mul_left_cancel₀ (ne_of_gt (hT_diag_pos i)) hscaled
      refine ⟨?_, ?_⟩
      · simpa [hy_eq] using hx_nonneg i
      · rw [hy_eq]
        simp
  | succ d ih =>
      intro i hi
      by_cases htail : n - 1 - i.val ≤ d
      · rcases ih i htail with ⟨hy_nonneg, hy_le⟩
        refine ⟨hy_nonneg, ?_⟩
        calc
          y i ≤ (((2 * d + 1 : ℕ) : ℝ)) * x i := hy_le
          _ ≤ (((2 * (d + 1) + 1 : ℕ) : ℝ)) * x i := by
                have hcoef :
                    (((2 * d + 1 : ℕ) : ℝ)) ≤ (((2 * (d + 1) + 1 : ℕ) : ℝ)) := by
                  norm_num
                exact mul_le_mul_of_nonneg_right hcoef (hx_nonneg i)
      · let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => i.val < j.val)
        let sx : ℝ := ∑ j ∈ S, (-T i j) * x j
        let sy : ℝ := ∑ j ∈ S, (-T i j) * y j
        have hrowi : T i i * y i = T i i * x i + sx + sy := by
          simpa [S, sx, sy, add_assoc, add_left_comm, add_comm] using hrow i
        have hsx_nonneg : 0 ≤ sx := by
          unfold sx S
          apply Finset.sum_nonneg
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact mul_nonneg (by linarith [hT_offdiag i j hj]) (hx_nonneg j)
        have hsy_nonneg : 0 ≤ sy := by
          unfold sy S
          apply Finset.sum_nonneg
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hj_tail : n - 1 - j.val ≤ d := by omega
          exact mul_nonneg (by linarith [hT_offdiag i j hj]) (ih j hj_tail).1
        have hsx_le : sx ≤ T i i * x i := by
          have hTx_pos :
              T i i * x i = b i + sx := by
            have hTxi := hTx i
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hTxi
            rw [higham8_upperTriangular_erase_sum_eq_strictUpper n T hUT i x] at hTxi
            unfold sx S
            have hsum :
                ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * x j =
                  -∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    (-T i j) * x j := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
            rw [hsum] at hTxi
            linarith
          linarith [hb i, hTx_pos]
        have hsy_le : sy ≤ (((2 * d + 1 : ℕ) : ℝ)) * sx := by
          unfold sy sx S
          calc
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j
                ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    (((2 * d + 1 : ℕ) : ℝ)) * ((-T i j) * x j) := by
                    apply Finset.sum_le_sum
                    intro j hj
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                    have hj_tail : n - 1 - j.val ≤ d := by omega
                    have hy_le : y j ≤ (((2 * d + 1 : ℕ) : ℝ)) * x j := (ih j hj_tail).2
                    have hcoef_nonneg : 0 ≤ -T i j := by linarith [hT_offdiag i j hj]
                    calc
                      (-T i j) * y j ≤ (-T i j) * ((((2 * d + 1 : ℕ) : ℝ)) * x j) :=
                        mul_le_mul_of_nonneg_left hy_le hcoef_nonneg
                      _ = (((2 * d + 1 : ℕ) : ℝ)) * ((-T i j) * x j) := by ring
            _ = (((2 * d + 1 : ℕ) : ℝ)) *
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j := by
                    rw [← Finset.mul_sum]
        have hy_nonneg : 0 ≤ y i := by
          have hprod_nonneg : 0 ≤ T i i * y i := by
            linarith [hrowi, hsx_nonneg, hsy_nonneg, hx_nonneg i, hT_diag_pos i]
          by_contra hyneg
          push_neg at hyneg
          linarith [mul_neg_of_pos_of_neg (hT_diag_pos i) hyneg]
        have hc_nonneg : 0 ≤ (((2 * d + 1 : ℕ) : ℝ)) := by
          positivity
        have hsy_le' : sy ≤ (((2 * d + 1 : ℕ) : ℝ)) * (T i i * x i) := by
          exact le_trans hsy_le (mul_le_mul_of_nonneg_left hsx_le hc_nonneg)
        have hcoef_eq :
            (2 : ℝ) + (((2 * d + 1 : ℕ) : ℝ)) = (((2 * (d + 1) + 1 : ℕ) : ℝ)) := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_mul]
          norm_num
          ring
        have hscaled :
            T i i * y i ≤
              T i i * ((((2 * (d + 1) + 1 : ℕ) : ℝ)) * x i) := by
          calc
            T i i * y i = T i i * x i + sx + sy := hrowi
            _ ≤ T i i * x i + T i i * x i + (((2 * d + 1 : ℕ) : ℝ)) * (T i i * x i) := by
                  linarith
            _ = (T i i * x i) * ((2 : ℝ) + (((2 * d + 1 : ℕ) : ℝ))) := by
                  ring
            _ = (T i i * x i) * (((2 * (d + 1) + 1 : ℕ) : ℝ)) := by
                  rw [hcoef_eq]
            _ = T i i * (x i * (((2 * (d + 1) + 1 : ℕ) : ℝ))) := by
                  rw [mul_assoc]
            _ = T i i * ((((2 * (d + 1) + 1 : ℕ) : ℝ)) * x i) := by
                  congr 1
                  rw [mul_comm]
        refine ⟨hy_nonneg, ?_⟩
        exact le_of_mul_le_mul_left hscaled (hT_diag_pos i)


/-- **Problem 8.4**: if `T` is an upper triangular M-matrix and `b = Tx ≥ 0`,
then `cond(T,x) ≤ 2n-1`. -/
theorem higham8_4_upperTriangularMMatrix_condAtSolution_le (n : ℕ) (hn : 0 < n)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hx : 0 < infNormVec x) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤ 2 * (n : ℝ) - 1 := by
  have hx_nonneg :=
    higham8_upperTriangularMMatrix_solution_nonneg n T T_inv x b
      hUT hT_diag_pos hT_offdiag hInv hTx hb
  have hComp :
      comparisonMatrix n T = T :=
    higham8_comparisonMatrix_eq_self_upper n T hUT hT_diag_pos hT_offdiag
  have hInv_ut :=
    inv_upper_tri n T T_inv hUT (fun i => ne_of_gt (hT_diag_pos i)) hInv.1
  have hy_bound :=
    higham8_problem8_4_comparisonImage_nonneg_bound n T T_inv x b
      hUT hT_diag_pos hT_offdiag hInv hTx hb hx_nonneg
  have hcoef_nonneg : 0 ≤ 2 * (n : ℝ) - 1 := by
    have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr hn
    linarith
  have hy_norm :
      infNormVec (higham8_9_comparisonImage n T T_inv x) ≤
        (2 * (n : ℝ) - 1) * infNormVec x := by
    apply infNormVec_le_of_abs_le
    · intro i
      rcases hy_bound i with ⟨hy_nonneg, hy_le⟩
      rw [abs_of_nonneg hy_nonneg]
      have hcoef_nat : 2 * (n - 1 - i.val) + 1 ≤ 2 * n - 1 := by omega
      have hcoef :
          (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) - 1 := by
        have hcoef' :
            (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) ≤ (((2 * n - 1 : ℕ) : ℝ)) := by
          exact_mod_cast hcoef_nat
        have htarget : (((2 * n - 1 : ℕ) : ℝ)) = 2 * (n : ℝ) - 1 := by
          have htwo : 1 ≤ 2 * n := by
            have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
            omega
          rw [Nat.cast_sub htwo, Nat.cast_mul, Nat.cast_one]
          ring
        rw [htarget] at hcoef'
        exact hcoef'
      have hxi_le : x i ≤ infNormVec x := by
        simpa [abs_of_nonneg (hx_nonneg i)] using abs_le_infNormVec x i
      calc
        higham8_9_comparisonImage n T T_inv x i
            ≤ (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) * x i := hy_le
        _ ≤ (2 * (n : ℝ) - 1) * x i :=
              mul_le_mul_of_nonneg_right hcoef (hx_nonneg i)
        _ ≤ (2 * (n : ℝ) - 1) * infNormVec x :=
              mul_le_mul_of_nonneg_left hxi_le hcoef_nonneg
    ·
      exact mul_nonneg hcoef_nonneg (infNormVec_nonneg x)
  have hcond_le :=
    higham8_9_upperTriangular_condAtSolution_le_comparison_eq n hn T T_inv T_inv x
      hUT (fun i => ne_of_gt (hT_diag_pos i)) hInv
      (by simpa [hComp] using hInv.2) hInv_ut
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ infNormVec (higham8_9_comparisonImage n T T_inv x) / infNormVec x := hcond_le
    _ ≤ ((2 * (n : ℝ) - 1) * infNormVec x) / infNormVec x :=
          div_le_div_of_nonneg_right hy_norm (infNormVec_nonneg x)
    _ = 2 * (n : ℝ) - 1 := by
          field_simp [ne_of_gt hx]

end NumStability
