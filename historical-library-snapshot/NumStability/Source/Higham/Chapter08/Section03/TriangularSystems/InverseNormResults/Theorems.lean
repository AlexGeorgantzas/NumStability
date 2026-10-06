-- NumStability/Source/Higham/Chapter08/Section03/TriangularSystems/InverseNormResults/Theorems.lean
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


/-! ## §8.3 Bounds for the Inverse -/

















































































































































































































































private lemma higham8_12_WMatrix_offdiag_nonpos (n : ℕ)
    (U : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, i.val < j.val → higham8_12_WMatrix n U i j ≤ 0 := by
  intro i j hij
  rw [higham8_12_WMatrix_strictUpper n U hij]
  exact neg_nonpos.mpr (higham8_12_rowMaxStrictUpper_nonneg n U i)


private lemma higham8_12_ZMatrix_upper (n : ℕ) (α β : ℝ) :
    ∀ i j : Fin n, j.val < i.val → higham8_12_ZMatrix n α β i j = 0 := by
  intro i j hij
  have hneq : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hnotlt : ¬ i.val < j.val := by omega
  simp [higham8_12_ZMatrix, higham8_3_stressUpper, hneq, hnotlt]


private lemma higham8_12_ZInvFormula_upper (n : ℕ) (α β : ℝ) :
    ∀ i j : Fin n, j.val < i.val → higham8_12_ZInvFormula n α β i j = 0 := by
  intro i j hij
  have hneq : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hnotlt : ¬ i.val < j.val := by omega
  simp [higham8_12_ZInvFormula, higham8_4_stressUpperInvFormula, hneq, hnotlt]


private lemma higham8_12_ZInvFormula_diag (n : ℕ) (α β : ℝ) (i : Fin n) :
    higham8_12_ZInvFormula n α β i i = 1 / α := by
  simp [higham8_12_ZInvFormula, higham8_4_stressUpperInvFormula]


/-- **Theorem 8.12**, middle inverse-chain step `M(U)⁻¹ ≤ W(U)⁻¹`. -/
theorem higham8_12_comparisonInv_le_WInv (n : ℕ)
    (U M_inv W_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i j : Fin n, M_inv i j ≤ W_inv i j := by
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i
    simp [comparisonMatrix, hU_diag i]
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_ut :=
    inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut
      (fun i => ne_of_gt (hM_diag_pos i)) hM_LInv
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hW_diag_pos : ∀ i : Fin n, 0 < higham8_12_WMatrix n U i i := by
    intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_pos.mpr (hU_diag i)
  have hW_LInv := ch7_isLeftInverse_of_isRightInverse hW_RInv
  have hW_inv_ut :=
    inv_upper_tri n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U)
      (fun i => ne_of_gt (hW_diag_pos i)) hW_LInv
  have hW_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U) hW_diag_pos
      (higham8_12_WMatrix_offdiag_nonpos n U) hW_RInv hW_inv_ut
  suffices h :
      ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
        M_inv i j ≤ W_inv i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij
        rw [hM_inv_ut i j (by omega), hW_inv_ut i j (by omega)]
  intro d
  induction d with
  | zero =>
      intro i j hdiff hij
      have heq : i = j := Fin.ext (by omega)
      subst heq
      have hM_diag :
          M_inv i i = 1 / |U i i| := by
        simpa [comparisonMatrix] using
          inv_diag_entry n (comparisonMatrix n U) M_inv
            hM_ut (fun k => ne_of_gt (hM_diag_pos k)) hM_LInv hM_inv_ut i
      have hW_diag :
          W_inv i i = 1 / |U i i| := by
        simpa [higham8_12_WMatrix] using
          inv_diag_entry n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_LInv hW_inv_ut i
      rw [hM_diag, hW_diag]
  | succ d ih =>
      intro i j hdiff hij
      by_cases heq : i.val = j.val
      · exact ih i j (by omega) (by omega)
      · have hij' : i.val < j.val := by omega
        have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
        have hrec_M :=
          inv_recurrence n (comparisonMatrix n U) M_inv hM_ut
            (fun k => ne_of_gt (hM_diag_pos k)) hM_RInv hM_inv_ut i j hij'
        have hrec_W :=
          inv_recurrence n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_RInv hW_inv_ut i j hij'
        have hM_prod :
            |U i i| * M_inv i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                |U i k| * M_inv k j := by
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  comparisonMatrix n U i k * M_inv k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    |U i k| * M_inv k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            simp [comparisonMatrix, show i ≠ k from Fin.ne_of_val_ne (by omega)]
          have hM_ii : comparisonMatrix n U i i = |U i i| := by
            simp [comparisonMatrix]
          rw [hM_ii] at hrec_M
          rw [hsum_rw] at hrec_M
          linarith
        have hW_prod :
            |U i i| * W_inv i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j := by
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_WMatrix n U i k * W_inv k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    higham8_12_rowMaxStrictUpper n U i * W_inv k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            rw [higham8_12_WMatrix_strictUpper n U hk.1]
            ring
          rw [higham8_12_WMatrix_diag] at hrec_W
          rw [hsum_rw] at hrec_W
          linarith
        have hsum_le :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                |U i k| * M_inv k j ≤
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have hrow_le :
              |U i k| * M_inv k j ≤
                higham8_12_rowMaxStrictUpper n U i * M_inv k j :=
            mul_le_mul_of_nonneg_right
              (higham8_12_abs_le_rowMaxStrictUpper n U i k hk.1)
              (hM_nonneg k j)
          have hih :
              higham8_12_rowMaxStrictUpper n U i * M_inv k j ≤
                higham8_12_rowMaxStrictUpper n U i * W_inv k j :=
            mul_le_mul_of_nonneg_left
              (ih k j (by omega) (by omega))
              (higham8_12_rowMaxStrictUpper_nonneg n U i)
          exact hrow_le.trans hih
        calc
          M_inv i j =
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  |U i k| * M_inv k j) / |U i i| := by
              rw [← hM_prod]
              field_simp [ne_of_gt hUii_pos]
          _ ≤
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_rowMaxStrictUpper n U i * W_inv k j) / |U i i| :=
                div_le_div_of_nonneg_right hsum_le (le_of_lt hUii_pos)
          _ = W_inv i j := by
              rw [← hW_prod]
              field_simp [ne_of_gt hUii_pos]


/-- **Theorem 8.12**, last middle inverse-chain step `W(U)⁻¹ ≤ Z(U)⁻¹`. -/
theorem higham8_12_WInv_le_ZInvFormula (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i j : Fin n, W_inv i j ≤ higham8_12_ZInvFormula n α β i j := by
  have hW_diag_pos : ∀ i : Fin n, 0 < higham8_12_WMatrix n U i i := by
    intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_pos.mpr (hU_diag i)
  have hW_LInv := ch7_isLeftInverse_of_isRightInverse hW_RInv
  have hW_inv_ut :=
    inv_upper_tri n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U)
      (fun i => ne_of_gt (hW_diag_pos i)) hW_LInv
  have hW_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U) hW_diag_pos
      (higham8_12_WMatrix_offdiag_nonpos n U) hW_RInv hW_inv_ut
  have hZ_RInv := higham8_12_ZInvFormula_isRightInverse n α β (ne_of_gt hα)
  suffices h :
      ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
        W_inv i j ≤ higham8_12_ZInvFormula n α β i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij
        rw [hW_inv_ut i j (by omega), higham8_12_ZInvFormula_upper n α β i j (by omega)]
  intro d
  induction d with
  | zero =>
      intro i j hdiff hij
      have heq : i = j := Fin.ext (by omega)
      subst heq
      have hW_diag :
          W_inv i i = 1 / |U i i| := by
        simpa [higham8_12_WMatrix] using
          inv_diag_entry n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_LInv hW_inv_ut i
      have hdiag_le : 1 / |U i i| ≤ 1 / α := by
        exact one_div_le_one_div_of_le hα (hα_le_diag i)
      rw [hW_diag, higham8_12_ZInvFormula_diag]
      exact hdiag_le
  | succ d ih =>
      intro i j hdiff hij
      by_cases heq : i.val = j.val
      · exact ih i j (by omega) (by omega)
      · have hij' : i.val < j.val := by omega
        have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
        have hrec_W :=
          inv_recurrence n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_RInv hW_inv_ut i j hij'
        have hZ_prod :
            α * higham8_12_ZInvFormula n α β i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                (α * β) * higham8_12_ZInvFormula n α β k j := by
          have hZ_diag_pos : ∀ i : Fin n, 0 < higham8_12_ZMatrix n α β i i := by
            intro k
            simpa [higham8_12_ZMatrix, higham8_3_stressUpper] using hα
          have hrec_Z :=
            inv_recurrence n (higham8_12_ZMatrix n α β) (higham8_12_ZInvFormula n α β)
              (higham8_12_ZMatrix_upper n α β)
              (fun k => ne_of_gt (hZ_diag_pos k)) hZ_RInv
              (higham8_12_ZInvFormula_upper n α β) i j hij'
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_ZMatrix n α β i k * higham8_12_ZInvFormula n α β k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    (α * β) * higham8_12_ZInvFormula n α β k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            have hneq : i ≠ k := Fin.ne_of_val_ne (by omega)
            simp [higham8_12_ZMatrix, higham8_3_stressUpper, hneq, hk.1]
          have hZ_ii : higham8_12_ZMatrix n α β i i = α := by
            simp [higham8_12_ZMatrix, higham8_3_stressUpper]
          rw [hZ_ii] at hrec_Z
          rw [hsum_rw] at hrec_Z
          linarith
        have hW_prod :
            |U i i| * W_inv i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j := by
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_WMatrix n U i k * W_inv k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    higham8_12_rowMaxStrictUpper n U i * W_inv k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            rw [higham8_12_WMatrix_strictUpper n U hk.1]
            ring
          rw [higham8_12_WMatrix_diag] at hrec_W
          rw [hsum_rw] at hrec_W
          linarith
        have hsum_le :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j ≤
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                (β * |U i i|) * higham8_12_ZInvFormula n α β k j := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have hrow_le :
              higham8_12_rowMaxStrictUpper n U i * W_inv k j ≤
                (β * |U i i|) * W_inv k j :=
            mul_le_mul_of_nonneg_right
              (higham8_12_rowMaxStrictUpper_le_beta_mul_diag n U hβ hβ_bound i)
              (hW_nonneg k j)
          have hih :
              (β * |U i i|) * W_inv k j ≤
                (β * |U i i|) * higham8_12_ZInvFormula n α β k j :=
            mul_le_mul_of_nonneg_left
              (ih k j (by omega) (by omega))
              (mul_nonneg hβ (abs_nonneg _))
          exact hrow_le.trans hih
        have hZ_beta_sum :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                β * higham8_12_ZInvFormula n α β k j =
              higham8_12_ZInvFormula n α β i j := by
          have hsum_factor :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  (α * β) * higham8_12_ZInvFormula n α β k j =
                α *
                  (∑ k ∈ Finset.univ.filter
                      (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                      β * higham8_12_ZInvFormula n α β k j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
          calc
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                β * higham8_12_ZInvFormula n α β k j
                =
              (α *
                (∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    β * higham8_12_ZInvFormula n α β k j)) / α := by
                  field_simp [ne_of_gt hα]
            _ =
              (α * higham8_12_ZInvFormula n α β i j) / α := by
                rw [← hsum_factor, hZ_prod]
            _ = higham8_12_ZInvFormula n α β i j := by
                field_simp [ne_of_gt hα]
        calc
          W_inv i j =
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_rowMaxStrictUpper n U i * W_inv k j) / |U i i| := by
              rw [← hW_prod]
              field_simp [ne_of_gt hUii_pos]
          _ ≤
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  (β * |U i i|) * higham8_12_ZInvFormula n α β k j) / |U i i| :=
                div_le_div_of_nonneg_right hsum_le (le_of_lt hUii_pos)
          _ =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                β * higham8_12_ZInvFormula n α β k j := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro k hk
              field_simp [ne_of_gt hUii_pos]
          _ = higham8_12_ZInvFormula n α β i j := hZ_beta_sum


private theorem higham8_12_comparisonInv_nonneg (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv) :
    ∀ i j : Fin n, 0 ≤ M_inv i j := by
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i
    simp [comparisonMatrix, hU_diag i]
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_ut :=
    inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut
      (fun i => ne_of_gt (hM_diag_pos i)) hM_LInv
  exact upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
    hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut


private theorem higham8_12_WInv_nonneg (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i j : Fin n, 0 ≤ W_inv i j := by
  have hW_diag_pos : ∀ i : Fin n, 0 < higham8_12_WMatrix n U i i := by
    intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_pos.mpr (hU_diag i)
  have hW_LInv := ch7_isLeftInverse_of_isRightInverse hW_RInv
  have hW_inv_ut :=
    inv_upper_tri n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U)
      (fun i => ne_of_gt (hW_diag_pos i)) hW_LInv
  exact upper_tri_mmatrix_inv_nonneg n (higham8_12_WMatrix n U) W_inv
    (higham8_12_WMatrix_upper n U) hW_diag_pos
    (higham8_12_WMatrix_offdiag_nonpos n U) hW_RInv hW_inv_ut


private theorem higham8_infNorm_le_of_abs_le_nonneg {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, |A i j| ≤ B i j) :
    infNorm A ≤ infNorm B := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |A i j| ≤ ∑ j : Fin n, B i j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact hAB i j
      _ = ∑ j : Fin n, |B i j| := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact (abs_of_nonneg (hB_nonneg i j)).symm
      _ ≤ infNorm B := row_sum_le_infNorm B i
  · exact infNorm_nonneg B


private theorem higham8_oneNorm_le_of_abs_le_nonneg {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, |A i j| ≤ B i j) :
    oneNorm A ≤ oneNorm B := by
  apply oneNorm_le_of_col_sum_le
  · intro j
    calc
      ∑ i : Fin n, |A i j| ≤ ∑ i : Fin n, B i j := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hAB i j
      _ = ∑ i : Fin n, |B i j| := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (abs_of_nonneg (hB_nonneg i j)).symm
      _ ≤ oneNorm B := col_sum_le_oneNorm B j
  · exact oneNorm_nonneg B


private theorem higham8_infNorm_le_of_nonneg_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) :
    infNorm A ≤ infNorm B := by
  apply higham8_infNorm_le_of_abs_le_nonneg A B hB_nonneg
  intro i j
  rw [abs_of_nonneg (hA_nonneg i j)]
  exact hAB i j


private theorem higham8_oneNorm_le_of_nonneg_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) :
    oneNorm A ≤ oneNorm B := by
  apply higham8_oneNorm_le_of_abs_le_nonneg A B hB_nonneg
  intro i j
  rw [abs_of_nonneg (hA_nonneg i j)]
  exact hAB i j


private theorem higham8_opNorm2_le_of_abs_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hAB : ∀ i j : Fin n, |A i j| ≤ B i j) :
    complexMatrixOp2 (realRectToCMatrix A) ≤
      complexMatrixOp2 (realRectToCMatrix B) := by
  have hB_rect :
      rectOpNorm2Le B (complexMatrixOp2 (realRectToCMatrix B)) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le B le_rfl
  have hA_rect :
      rectOpNorm2Le A (complexMatrixOp2 (realRectToCMatrix B)) :=
    rectOpNorm2Le_of_abs_entry_le hAB hB_rect
  exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le A
    (complexMatrixOp2_nonneg (realRectToCMatrix B)) hA_rect


private theorem higham8_opNorm2_le_of_nonneg_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) :
    complexMatrixOp2 (realRectToCMatrix A) ≤
      complexMatrixOp2 (realRectToCMatrix B) := by
  apply higham8_opNorm2_le_of_abs_le A B
  intro i j
  rw [abs_of_nonneg (hA_nonneg i j)]
  exact hAB i j


private theorem higham8_nonneg_real_matrix_absVec_mul_norm {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (z : CVec n) (i : Fin n) :
    ‖complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z) i‖ =
      ∑ j : Fin n, A i j * ‖z j‖ := by
  have hA_abs_eq : absMatrixRect A = A := by
    ext i j
    simp [absMatrixRect, hA_nonneg i j]
  have hA_abs :
      complexAbsMatrix (realRectToCMatrix A) = realRectToCMatrix A := by
    simpa [hA_abs_eq] using (realRectToCMatrix_absMatrixRect A).symm
  calc
    ‖complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z) i‖
        = ‖complexMatrixVecMul (complexAbsMatrix (realRectToCMatrix A))
            (complexAbsVec z) i‖ := by
              rw [hA_abs]
    _ = ∑ j : Fin n, ‖realRectToCMatrix A i j‖ * ‖z j‖ := by
          exact
            complexMatrixVecMul_absMatrix_absVec_norm_apply
              (realRectToCMatrix A) z i
    _ = ∑ j : Fin n, A i j * ‖z j‖ := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [realRectToCMatrix, hA_nonneg i j]


private theorem higham8_absolute_norm_vec_le_of_nonneg_le {n : ℕ}
    {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    (habs : IsAbsoluteComplexVectorNorm ν)
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) (z : CVec n) :
    ν (complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z)) ≤
      ν (complexMatrixVecMul (realRectToCMatrix B) (complexAbsVec z)) := by
  have hmono : IsMonotoneComplexVectorNorm ν :=
    (absolute_norm_iff_monotone_norm hν).mp habs
  apply hmono
  intro i
  calc
    ‖complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z) i‖
        = ∑ j : Fin n, A i j * ‖z j‖ :=
          higham8_nonneg_real_matrix_absVec_mul_norm A hA_nonneg z i
    _ ≤ ∑ j : Fin n, B i j * ‖z j‖ := by
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul_of_nonneg_right (hAB i j) (norm_nonneg (z j))
    _ = ‖complexMatrixVecMul (realRectToCMatrix B) (complexAbsVec z) i‖ := by
          symm
          exact higham8_nonneg_real_matrix_absVec_mul_norm B hB_nonneg z i


/-- **Theorem 8.12**, `∞`-norm chain induced by the entrywise inverse chain. -/
theorem higham8_12_infNorm_chain (n : ℕ)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    infNorm U_inv ≤ infNorm M_inv ∧
      infNorm M_inv ≤ infNorm W_inv ∧
      infNorm W_inv ≤ infNorm (higham8_12_ZInvFormula n α β) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hZ_nonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  have hUM :
      infNorm U_inv ≤ infNorm M_inv :=
    higham8_infNorm_le_of_abs_le_nonneg U_inv M_inv hM_nonneg
      (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
        hUT hU_diag hInv hM_RInv
        (inv_upper_tri n (comparisonMatrix n U) M_inv
          (by
            intro i j hij
            unfold comparisonMatrix
            simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
          (by
            intro i
            simp [comparisonMatrix, hU_diag i])
          (ch7_isLeftInverse_of_isRightInverse hM_RInv)))
  have hMW :
      infNorm M_inv ≤ infNorm W_inv :=
    higham8_infNorm_le_of_nonneg_le M_inv W_inv hM_nonneg hW_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv hUT hU_diag hM_RInv hW_RInv)
  have hWZ :
      infNorm W_inv ≤ infNorm (higham8_12_ZInvFormula n α β) :=
    higham8_infNorm_le_of_nonneg_le W_inv (higham8_12_ZInvFormula n α β)
      hW_nonneg hZ_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv)
  exact ⟨hUM, hMW, hWZ⟩


/-- **Theorem 8.12**, `1`-norm chain induced by the entrywise inverse chain. -/
theorem higham8_12_oneNorm_chain (n : ℕ)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    oneNorm U_inv ≤ oneNorm M_inv ∧
      oneNorm M_inv ≤ oneNorm W_inv ∧
      oneNorm W_inv ≤ oneNorm (higham8_12_ZInvFormula n α β) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hZ_nonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  have hUM :
      oneNorm U_inv ≤ oneNorm M_inv :=
    higham8_oneNorm_le_of_abs_le_nonneg U_inv M_inv hM_nonneg
      (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
        hUT hU_diag hInv hM_RInv
        (inv_upper_tri n (comparisonMatrix n U) M_inv
          (by
            intro i j hij
            unfold comparisonMatrix
            simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
          (by
            intro i
            simp [comparisonMatrix, hU_diag i])
          (ch7_isLeftInverse_of_isRightInverse hM_RInv)))
  have hMW :
      oneNorm M_inv ≤ oneNorm W_inv :=
    higham8_oneNorm_le_of_nonneg_le M_inv W_inv hM_nonneg hW_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv hUT hU_diag hM_RInv hW_RInv)
  have hWZ :
      oneNorm W_inv ≤ oneNorm (higham8_12_ZInvFormula n α β) :=
    higham8_oneNorm_le_of_nonneg_le W_inv (higham8_12_ZInvFormula n α β)
      hW_nonneg hZ_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv)
  exact ⟨hUM, hMW, hWZ⟩


/-- **Theorem 8.12**, `2`-norm chain induced by the entrywise inverse chain. -/
theorem higham8_12_opNorm2_chain (n : ℕ)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    complexMatrixOp2 (realRectToCMatrix U_inv) ≤
        complexMatrixOp2 (realRectToCMatrix M_inv) ∧
      complexMatrixOp2 (realRectToCMatrix M_inv) ≤
        complexMatrixOp2 (realRectToCMatrix W_inv) ∧
      complexMatrixOp2 (realRectToCMatrix W_inv) ≤
        complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hUM :
      complexMatrixOp2 (realRectToCMatrix U_inv) ≤
        complexMatrixOp2 (realRectToCMatrix M_inv) :=
    higham8_opNorm2_le_of_abs_le U_inv M_inv
      (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
        hUT hU_diag hInv hM_RInv
        (inv_upper_tri n (comparisonMatrix n U) M_inv
          (by
            intro i j hij
            unfold comparisonMatrix
            simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
          (by
            intro i
            simp [comparisonMatrix, hU_diag i])
          (ch7_isLeftInverse_of_isRightInverse hM_RInv)))
  have hMW :
      complexMatrixOp2 (realRectToCMatrix M_inv) ≤
        complexMatrixOp2 (realRectToCMatrix W_inv) :=
    higham8_opNorm2_le_of_nonneg_le M_inv W_inv hM_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv
        hUT hU_diag hM_RInv hW_RInv)
  have hWZ :
      complexMatrixOp2 (realRectToCMatrix W_inv) ≤
        complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) :=
    higham8_opNorm2_le_of_nonneg_le W_inv (higham8_12_ZInvFormula n α β)
      hW_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv)
  exact ⟨hUM, hMW, hWZ⟩


/-- **Theorem 8.12**, absolute-norm vector chain induced by the entrywise
inverse chain. -/
theorem higham8_12_absolute_norm_vector_chain (n : ℕ)
    {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    (habs : IsAbsoluteComplexVectorNorm ν)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|)
    (z : CVec n) :
    ν (complexMatrixVecMul (complexAbsMatrix (realRectToCMatrix U_inv))
          (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) ∧
      ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) ∧
      ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix (higham8_12_ZInvFormula n α β))
          (complexAbsVec z)) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hZ_nonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  have hUM :
      ν (complexMatrixVecMul (complexAbsMatrix (realRectToCMatrix U_inv))
            (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) := by
    have hA :
        ∀ i j : Fin n, absMatrixRect U_inv i j ≤ M_inv i j := by
      intro i j
      simpa [absMatrixRect] using
        (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
          hUT hU_diag hInv hM_RInv
          (inv_upper_tri n (comparisonMatrix n U) M_inv
            (by
              intro i j hij
              unfold comparisonMatrix
              simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
            (by
              intro i
              simp [comparisonMatrix, hU_diag i])
            (ch7_isLeftInverse_of_isRightInverse hM_RInv))) i j
    simpa [realRectToCMatrix_absMatrixRect] using
      (higham8_absolute_norm_vec_le_of_nonneg_le hν habs
        (absMatrixRect U_inv) M_inv
        (by intro i j; exact abs_nonneg _)
        hM_nonneg hA z)
  have hMW :
      ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) :=
    higham8_absolute_norm_vec_le_of_nonneg_le hν habs
      M_inv W_inv hM_nonneg hW_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv
        hUT hU_diag hM_RInv hW_RInv) z
  have hWZ :
      ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix (higham8_12_ZInvFormula n α β))
          (complexAbsVec z)) :=
    higham8_absolute_norm_vec_le_of_nonneg_le hν habs
      W_inv (higham8_12_ZInvFormula n α β) hW_nonneg hZ_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv) z
  exact ⟨hUM, hMW, hWZ⟩










































































































































/-- **Theorem 8.14 support**: under `β ≤ 1`, the source `1`-norm of `U⁻¹`
is bounded by the same `Z(U)` endpoint. -/
theorem higham8_14_oneNorm_upperBound (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    oneNorm U_inv ≤ (1 / α) * (2 : ℝ) ^ (n - 1) := by
  have honeChain :=
    higham8_12_oneNorm_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  exact honeChain.1.trans
    (honeChain.2.1.trans
      (honeChain.2.2.trans
        (higham8_14_ZInvFormula_oneNorm_upperBound n hn hα hβ hβ1)))


/-- **Theorem 8.14 support**: under `β ≤ 1`, the source `2`-norm of `U⁻¹`
is bounded by the same `Z(U)` endpoint. -/
theorem higham8_14_opNorm2_upperBound (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    complexMatrixOp2 (realRectToCMatrix U_inv) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  have hchain :=
    higham8_12_opNorm2_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  exact hchain.1.trans
    (hchain.2.1.trans
      (hchain.2.2.trans
        (higham8_14_ZInvFormula_opNorm2_upperBound n hn hα hβ hβ1)))
























































































































































private theorem higham8_6_comparisonInverseAbsVec_nonneg (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (i : Fin n) :
    0 ≤ higham8_6_comparisonInverseAbsVec M_inv z i := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  unfold higham8_6_comparisonInverseAbsVec
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hM_nonneg i j) (abs_nonneg _))


private theorem higham8_6_WInverseAbsVec_nonneg (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (i : Fin n) :
    0 ≤ higham8_6_WInverseAbsVec W_inv z i := by
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  unfold higham8_6_WInverseAbsVec
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hW_nonneg i j) (abs_nonneg _))


/-- **Problem 8.6**, the `M(U)` bound vector is componentwise bounded by the
`W(U)` bound vector from Theorem 8.12. -/
theorem higham8_6_comparisonInverseAbsVec_le_WInverseAbsVec (n : ℕ)
    (U M_inv W_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i : Fin n,
      higham8_6_comparisonInverseAbsVec M_inv z i ≤
        higham8_6_WInverseAbsVec W_inv z i := by
  have hMW :=
    higham8_12_comparisonInv_le_WInv n U M_inv W_inv hUT hU_diag hM_RInv hW_RInv
  intro i
  unfold higham8_6_comparisonInverseAbsVec higham8_6_WInverseAbsVec
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hMW i j) (abs_nonneg _)


/-- **Problem 8.6**, the displayed `∞`-norm quantity obtained from `M(U)` is
bounded by the corresponding `W(U)` quantity.  The source flop counts are cost
claims; this theorem records the mathematical correctness of the two exact
triangular-solve quantities. -/
theorem higham8_6_comparisonInverseAbsVecInfNorm_le_WInverseAbsVecInfNorm (n : ℕ)
    (U M_inv W_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    higham8_6_comparisonInverseAbsVecInfNorm M_inv z ≤
      higham8_6_WInverseAbsVecInfNorm W_inv z := by
  unfold higham8_6_comparisonInverseAbsVecInfNorm higham8_6_WInverseAbsVecInfNorm
  apply infNormVec_le_of_abs_le
  · intro i
    have hM_nonneg :=
      higham8_6_comparisonInverseAbsVec_nonneg n U M_inv z hUT hU_diag hM_RInv i
    have hW_nonneg :=
      higham8_6_WInverseAbsVec_nonneg n U W_inv z hU_diag hW_RInv i
    calc
      |higham8_6_comparisonInverseAbsVec M_inv z i|
          = higham8_6_comparisonInverseAbsVec M_inv z i :=
            abs_of_nonneg hM_nonneg
      _ ≤ higham8_6_WInverseAbsVec W_inv z i :=
            higham8_6_comparisonInverseAbsVec_le_WInverseAbsVec n U M_inv W_inv z
              hUT hU_diag hM_RInv hW_RInv i
      _ = |higham8_6_WInverseAbsVec W_inv z i| := by
            rw [abs_of_nonneg hW_nonneg]
      _ ≤ infNormVec (higham8_6_WInverseAbsVec W_inv z) :=
            abs_le_infNormVec (higham8_6_WInverseAbsVec W_inv z) i
  · exact infNormVec_nonneg (higham8_6_WInverseAbsVec W_inv z)






































































































/-- **Theorem 8.14**, packaged `∞/1/2` norm chains in the source notation
using the minimum diagonal magnitude. -/
theorem higham8_14_full_norm_chain (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n) {β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    let α : ℝ :=
      Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
        (fun k : Fin n => |U k k|)
    (1 / α ≤ infNorm U_inv ∧
        infNorm U_inv ≤ infNorm M_inv ∧
        infNorm M_inv ≤ infNorm W_inv ∧
        infNorm W_inv ≤ infNorm (higham8_12_ZInvFormula n α β) ∧
        infNorm (higham8_12_ZInvFormula n α β) ≤
          (1 / α) * (2 : ℝ) ^ (n - 1)) ∧
      (1 / α ≤ oneNorm U_inv ∧
        oneNorm U_inv ≤ oneNorm M_inv ∧
        oneNorm M_inv ≤ oneNorm W_inv ∧
        oneNorm W_inv ≤ oneNorm (higham8_12_ZInvFormula n α β) ∧
        oneNorm (higham8_12_ZInvFormula n α β) ≤
          (1 / α) * (2 : ℝ) ^ (n - 1)) ∧
      (1 / α ≤ complexMatrixOp2 (realRectToCMatrix U_inv) ∧
        complexMatrixOp2 (realRectToCMatrix U_inv) ≤
          complexMatrixOp2 (realRectToCMatrix M_inv) ∧
        complexMatrixOp2 (realRectToCMatrix M_inv) ≤
          complexMatrixOp2 (realRectToCMatrix W_inv) ∧
        complexMatrixOp2 (realRectToCMatrix W_inv) ≤
          complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ∧
        complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
          (1 / α) * (2 : ℝ) ^ (n - 1)) := by
  classical
  let α : ℝ :=
    Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|)
  rcases Finset.exists_mem_eq_inf'
      (s := Finset.univ) ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|) with
    ⟨k, _hk_mem, hα_eq⟩
  have hα : 0 < α := by
    dsimp [α]
    rw [hα_eq]
    exact abs_pos.mpr (hU_diag k)
  have hα_le_diag : ∀ i : Fin n, α ≤ |U i i| := by
    intro i
    simpa [α] using
      (Finset.inf'_le (s := Finset.univ)
        (f := fun k : Fin n => |U k k|) (b := i) (Finset.mem_univ i))
  have hDD : IsDiagDominantUpper n U := by
    refine ⟨hUT, hU_diag, ?_⟩
    intro i j hij
    have hdiag_nonneg : 0 ≤ |U i i| := abs_nonneg (U i i)
    calc
      |U i j| ≤ β * |U i i| := hβ_bound i j hij
      _ ≤ |U i i| := by nlinarith
  have hInfChain :=
    higham8_12_infNorm_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  have hOneChain :=
    higham8_12_oneNorm_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  have hOp2Chain :=
    higham8_12_opNorm2_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  have hInfLower :
      1 / α ≤ infNorm U_inv :=
    higham8_14_infNorm_lowerBound n U U_inv i0 hDD hInv
  have hOneLower :
      1 / α ≤ oneNorm U_inv := by
    calc
      1 / α = 1 / |U k k| := by
        simpa [α] using congrArg (fun x : ℝ => 1 / x) hα_eq
      _ ≤ oneNorm U_inv :=
        higham8_14_oneNorm_lowerBound n U U_inv k hUT hU_diag hInv
  have hOp2Lower :
      1 / α ≤ complexMatrixOp2 (realRectToCMatrix U_inv) := by
    calc
      1 / α = 1 / |U k k| := by
        simpa [α] using congrArg (fun x : ℝ => 1 / x) hα_eq
      _ ≤ complexMatrixOp2 (realRectToCMatrix U_inv) :=
        higham8_14_opNorm2_lowerBound n U U_inv k hUT hU_diag hInv
  have hInfUpperZ :
      infNorm (higham8_12_ZInvFormula n α β) ≤
        (1 / α) * (2 : ℝ) ^ (n - 1) :=
    higham8_14_ZInvFormula_infNorm_upperBound n hn hα hβ hβ1
  have hOneUpperZ :
      oneNorm (higham8_12_ZInvFormula n α β) ≤
        (1 / α) * (2 : ℝ) ^ (n - 1) :=
    higham8_14_ZInvFormula_oneNorm_upperBound n hn hα hβ hβ1
  have hOp2UpperZ :
      complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
        (1 / α) * (2 : ℝ) ^ (n - 1) :=
    higham8_14_ZInvFormula_opNorm2_upperBound n hn hα hβ hβ1
  exact ⟨⟨hInfLower, hInfChain.1, hInfChain.2.1, hInfChain.2.2, hInfUpperZ⟩,
    ⟨⟨hOneLower, hOneChain.1, hOneChain.2.1, hOneChain.2.2, hOneUpperZ⟩,
      ⟨hOp2Lower, hOp2Chain.1, hOp2Chain.2.1, hOp2Chain.2.2, hOp2UpperZ⟩⟩⟩

end NumStability
