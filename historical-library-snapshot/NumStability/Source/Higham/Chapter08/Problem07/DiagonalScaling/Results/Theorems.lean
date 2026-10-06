-- NumStability/Source/Higham/Chapter08/Problem07/DiagonalScaling/Results/Theorems.lean
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































































































































































































































































































































































































































































































































































private theorem higham8_7_nonneg_sup_eq_infNormVec {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx_nonneg : ∀ i : Fin n, 0 ≤ x i) :
    Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x = infNormVec x := by
  let δ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x
  have hδ_nonneg : 0 ≤ δ := by
    exact le_trans (hx_nonneg ⟨0, hn⟩) (Finset.le_sup' x (Finset.mem_univ _))
  apply le_antisymm
  · rcases Finset.exists_mem_eq_sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x with
      ⟨i0, _, hδ⟩
    rw [hδ]
    simpa [abs_of_nonneg (hx_nonneg i0)] using abs_le_infNormVec x i0
  · apply infNormVec_le_of_abs_le
    · intro i
      have hle : x i ≤ δ := Finset.le_sup' x (Finset.mem_univ i)
      simpa [δ, abs_of_nonneg (hx_nonneg i)] using hle
    · exact hδ_nonneg


private theorem higham8_7_scaled_vector_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (d x : Fin n → ℝ)
    (hd_pos : ∀ i : Fin n, 0 < d i)
    (hβ_pos : ∀ i : Fin n, 0 < higham8_7_scaledRowDiagMargin A d i) :
    infNormVec x ≤
      ((Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d) /
        (Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
          (higham8_7_scaledRowDiagMargin A d))) *
        infNormVec (matMulVec n A x) := by
  let δ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d
  let β := Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (higham8_7_scaledRowDiagMargin A d)
  let ρ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (fun i : Fin n => |x i| / d i)
  have hδ_nonneg : 0 ≤ δ := by
    exact le_trans (le_of_lt (hd_pos ⟨0, hn⟩)) (Finset.le_sup' d (Finset.mem_univ _))
  have hρ_nonneg : 0 ≤ ρ := by
    have hterm : 0 ≤ |x ⟨0, hn⟩| / d ⟨0, hn⟩ := by
      exact div_nonneg (abs_nonneg _) (le_of_lt (hd_pos _))
    exact le_trans hterm (Finset.le_sup' (fun i : Fin n => |x i| / d i) (Finset.mem_univ _))
  have hβ_pos' : 0 < β := by
    rcases Finset.exists_mem_eq_inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_scaledRowDiagMargin A d) with
      ⟨i0, _, hβ⟩
    dsimp [β]
    rw [hβ]
    exact hβ_pos i0
  have hx_le : ∀ i : Fin n, |x i| ≤ d i * ρ := by
    intro i
    have hi : |x i| / d i ≤ ρ :=
      Finset.le_sup' (fun j : Fin n => |x j| / d j) (Finset.mem_univ i)
    have hmul := (div_le_iff₀ (hd_pos i)).mp hi
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hx_norm_le : infNormVec x ≤ δ * ρ := by
    apply infNormVec_le_of_abs_le
    · intro i
      have hiδ : d i ≤ δ := Finset.le_sup' d (Finset.mem_univ i)
      calc
        |x i| ≤ d i * ρ := hx_le i
        _ ≤ δ * ρ := mul_le_mul_of_nonneg_right hiδ hρ_nonneg
    · exact mul_nonneg hδ_nonneg hρ_nonneg
  rcases Finset.exists_mem_eq_sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i : Fin n => |x i| / d i) with
    ⟨i0, _, hρ⟩
  have hx_i0 : |x i0| = d i0 * ρ := by
    have hmul : ρ * d i0 = |x i0| :=
      (eq_div_iff (show d i0 ≠ 0 from (hd_pos i0).ne')).mp hρ
    simpa [mul_comm] using hmul.symm
  have hsplit :
      ∑ j : Fin n, A i0 j * x j =
        A i0 i0 * x i0 + ∑ j ∈ Finset.univ.erase i0, A i0 j * x j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
  have habs_diag :
      |A i0 i0| * |x i0| ≤
        |matMulVec n A x i0| +
          ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j| := by
    calc
      |A i0 i0| * |x i0| = |A i0 i0 * x i0| := by rw [abs_mul]
      _ = |matMulVec n A x i0 - ∑ j ∈ Finset.univ.erase i0, A i0 j * x j| := by
          unfold matMulVec
          rw [hsplit]
          ring_nf
      _ ≤ |matMulVec n A x i0| + |∑ j ∈ Finset.univ.erase i0, A i0 j * x j| := by
          simpa using (abs_sub (matMulVec n A x i0)
            (∑ j ∈ Finset.univ.erase i0, A i0 j * x j))
      _ ≤ |matMulVec n A x i0| +
            ∑ j ∈ Finset.univ.erase i0, |A i0 j * x j| := by
          have hsumabs :
              |∑ j ∈ Finset.univ.erase i0, A i0 j * x j| ≤
                ∑ j ∈ Finset.univ.erase i0, |A i0 j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
          linarith
      _ = |matMulVec n A x i0| +
            ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j| := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul]
  have hoff :
      ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j| ≤
        (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
    calc
      ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j|
          ≤ ∑ j ∈ Finset.univ.erase i0, |A i0 j| * (d j * ρ) := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left (hx_le j) (abs_nonneg _)
      _ = ∑ j ∈ Finset.univ.erase i0, (|A i0 j| * d j) * ρ := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
            symm
            exact Finset.sum_mul (Finset.univ.erase i0) (fun j => |A i0 j| * d j) ρ
  have hmargin_i0 :
      higham8_7_scaledRowDiagMargin A d i0 * ρ ≤ |matMulVec n A x i0| := by
    have hlin :
        |A i0 i0| * |x i0| -
            (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ ≤
          |matMulVec n A x i0| := by
      have hbound :
          |A i0 i0| * |x i0| ≤
            |matMulVec n A x i0| +
              (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ :=
        by nlinarith [habs_diag, hoff]
      linarith
    unfold higham8_7_scaledRowDiagMargin
    calc
      (|A i0 i0| * d i0 - ∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ
          = |A i0 i0| * (d i0 * ρ) -
              (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
              ring
      _ = |A i0 i0| * |x i0| -
            (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
              rw [hx_i0]
      _ ≤ |matMulVec n A x i0| := hlin
  have hβρ :
      β * ρ ≤ infNormVec (matMulVec n A x) := by
    calc
      β * ρ
          ≤ higham8_7_scaledRowDiagMargin A d i0 * ρ := by
              exact mul_le_mul_of_nonneg_right
                (Finset.inf'_le (higham8_7_scaledRowDiagMargin A d) (Finset.mem_univ i0))
                hρ_nonneg
      _ ≤ |matMulVec n A x i0| := hmargin_i0
      _ ≤ infNormVec (matMulVec n A x) := abs_le_infNormVec _ i0
  have hρ_le : ρ ≤ infNormVec (matMulVec n A x) / β := by
    exact (le_div_iff₀ hβ_pos').2 (by simpa [mul_comm] using hβρ)
  calc
    infNormVec x ≤ δ * ρ := hx_norm_le
    _ ≤ δ * (infNormVec (matMulVec n A x) / β) := by
          exact mul_le_mul_of_nonneg_left hρ_le hδ_nonneg
    _ = (δ / β) * infNormVec (matMulVec n A x) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring


/-- **Problem 8.7(b)**: a positive diagonal row scaling `D = diag(d)` with
strictly diagonally dominant rows bounds `‖A⁻¹‖∞` by `‖D‖∞ / min_i β_i`. -/
theorem higham8_7_scaledStrictRowDiagDominant_invInfNorm_le (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (hInv : IsInverse n A A_inv)
    (hd_pos : ∀ i : Fin n, 0 < d i)
    (hβ_pos : ∀ i : Fin n, 0 < higham8_7_scaledRowDiagMargin A d i) :
    infNorm A_inv ≤
      (Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d) /
        (Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
          (higham8_7_scaledRowDiagMargin A d)) := by
  let δ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d
  let β := Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (higham8_7_scaledRowDiagMargin A d)
  have hδ_nonneg : 0 ≤ δ := by
    exact le_trans (le_of_lt (hd_pos ⟨0, hn⟩)) (Finset.le_sup' d (Finset.mem_univ _))
  have hβ_pos' : 0 < β := by
    rcases Finset.exists_mem_eq_inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_scaledRowDiagMargin A d) with
      ⟨i0, _, hβ⟩
    dsimp [β]
    rw [hβ]
    exact hβ_pos i0
  have hprod_nonneg : 0 ≤ δ / β := div_nonneg hδ_nonneg (le_of_lt hβ_pos')
  apply infNorm_le_of_row_sum_le
  · intro i
    let s : Fin n → ℝ := fun j => SignType.sign (A_inv i j)
    have hs_norm : infNormVec s ≤ 1 := by
      apply infNormVec_le_of_abs_le
      · intro j
        cases hsgn : SignType.sign (A_inv i j) <;> simp [s, hsgn]
      · norm_num
    have hrow_eq : matMulVec n A_inv s i = ∑ j : Fin n, |A_inv i j| := by
      unfold matMulVec s
      apply Finset.sum_congr rfl
      intro j _
      simp [self_mul_sign (A_inv i j)]
    have hprod : matMul n A A_inv = idMatrix n := by
      ext r c
      simpa [matMul, idMatrix] using hInv.2 r c
    have hAx : matMulVec n A (matMulVec n A_inv s) = s := by
      ext r
      calc
        matMulVec n A (matMulVec n A_inv s) r
            = matMulVec n (matMul n A A_inv) s r := by
                symm
                exact matMulVec_matMul n A A_inv s r
        _ = matMulVec n (idMatrix n) s r := by rw [hprod]
        _ = s r := by rw [matMulVec_id]
    have hvec :=
      higham8_7_scaled_vector_bound hn A d (matMulVec n A_inv s) hd_pos hβ_pos
    have hvec' : infNormVec (matMulVec n A_inv s) ≤ (δ / β) * infNormVec s := by
      simpa [δ, β, hAx] using hvec
    have hrow_abs : |matMulVec n A_inv s i| = ∑ j : Fin n, |A_inv i j| := by
      rw [hrow_eq]
      exact abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))
    calc
      ∑ j : Fin n, |A_inv i j| = |matMulVec n A_inv s i| := by
          symm
          exact hrow_abs
      _ ≤ infNormVec (matMulVec n A_inv s) := abs_le_infNormVec _ i
      _ ≤ (δ / β) * infNormVec s := hvec'
      _ ≤ (δ / β) * 1 := mul_le_mul_of_nonneg_left hs_norm hprod_nonneg
      _ = δ / β := by ring
  · exact hprod_nonneg


/-- **Problem 8.7(a)**: a strictly row diagonally dominant matrix satisfies
`‖A⁻¹‖∞ ≤ 1 / min_i α_i`. -/
theorem higham8_7_strictRowDiagDominant_invInfNorm_le (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A A_inv)
    (hα_pos : ∀ i : Fin n, 0 < higham8_7_rowDiagMargin A i) :
    infNorm A_inv ≤
      1 / (Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_rowDiagMargin A)) := by
  simpa [higham8_7_scaledRowDiagMargin, higham8_7_rowDiagMargin]
    using
      (higham8_7_scaledStrictRowDiagDominant_invInfNorm_le n hn A A_inv
        (fun _ => 1) hInv (fun _ => by norm_num)
        (by
          intro i
          simpa [higham8_7_scaledRowDiagMargin, higham8_7_rowDiagMargin]
            using hα_pos i))


/-- **Problem 8.7(c)**: taking `D = diag(M(U)⁻¹ e)` rederives the Algorithm
8.13 upper bound `‖M(U)⁻¹ e‖∞ ≥ ‖U⁻¹‖∞`. -/
theorem higham8_7_comparisonInverseOnes_infNorm_ge_inverseInfNorm (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    infNorm U_inv ≤ infNormVec (higham8_13_y M_inv) := by
  let y : Fin n → ℝ := higham8_13_y M_inv
  have habs :=
    abs_inv_le_compMatrix_inv n U U_inv M_inv hUT hU_diag hInv hM_RInv hM_inv_ut
  have hU_bound : infNorm U_inv ≤ infNorm M_inv := by
    simpa [higham8_13_mu] using higham8_13_inverse_bound_from_comparison U_inv M_inv habs
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i
    simp [comparisonMatrix]
    exact hU_diag i
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_diag : ∀ i : Fin n, M_inv i i = 1 / |U i i| := by
    intro i
    have hM_inv_ut :=
      inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut
        (fun k => by simpa [comparisonMatrix] using hU_diag k) hM_LInv
    simpa [comparisonMatrix] using
      inv_diag_entry n (comparisonMatrix n U) M_inv hM_ut
        (fun k => by simpa [comparisonMatrix] using hU_diag k) hM_LInv hM_inv_ut i
  have hy_pos : ∀ i : Fin n, 0 < y i := by
    intro i
    unfold y higham8_13_y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hdiag_pos : 0 < M_inv i i := by
      rw [hM_inv_diag]
      exact one_div_pos.mpr (abs_pos.mpr (hU_diag i))
    have hrest_nonneg :
        0 ≤ ∑ j ∈ Finset.univ.erase i, M_inv i j := by
      exact Finset.sum_nonneg (fun j _ => hM_nonneg i j)
    linarith
  have hy_nonneg : ∀ i : Fin n, 0 ≤ y i := by
    intro i
    exact (hy_pos i).le
  have hβ_eq_one :
      ∀ i : Fin n, higham8_7_scaledRowDiagMargin (comparisonMatrix n U) y i = 1 := by
    intro i
    unfold higham8_7_scaledRowDiagMargin y higham8_13_y
    have herase_eq :
        ∑ j ∈ Finset.univ.erase i, |comparisonMatrix n U i j| * (∑ k : Fin n, M_inv j k) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
            |U i j| * (∑ k : Fin n, M_inv j k) := by
      calc
        ∑ j ∈ Finset.univ.erase i, |comparisonMatrix n U i j| * (∑ k : Fin n, M_inv j k)
            = ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                |comparisonMatrix n U i j| * (∑ k : Fin n, M_inv j k) := by
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
                    have hlt : k.val < i.val := by omega
                    unfold comparisonMatrix
                    simp [show i ≠ k from Fin.ne_of_val_ne (by omega), hUT i k hlt, zero_mul]
        _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
              |U i j| * (∑ k : Fin n, M_inv j k) := by
                apply Finset.sum_congr rfl
                intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                unfold comparisonMatrix
                simp [show i ≠ j from Fin.ne_of_val_ne (by omega)]
    have hrow :=
      higham8_13_comparison_inverse_row_recurrence n U M_inv hUT hU_diag hM_RInv i
    unfold higham8_13_y at hrow
    rw [herase_eq]
    have hmain :
        |U i i| * (∑ j : Fin n, M_inv i j) -
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
              |U i j| * (∑ k : Fin n, M_inv j k) = 1 := by
      linarith [hrow]
    simpa [comparisonMatrix] using hmain
  have hM_bound :=
    higham8_7_scaledStrictRowDiagDominant_invInfNorm_le n hn
      (comparisonMatrix n U) M_inv y ⟨hM_LInv, hM_RInv⟩ hy_pos
      (by
        intro i
        rw [hβ_eq_one i]
        norm_num)
  have hy_sup :
      Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ y = infNormVec y :=
    higham8_7_nonneg_sup_eq_infNormVec hn y hy_nonneg
  have hβ_one :
      Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_scaledRowDiagMargin (comparisonMatrix n U) y) = 1 := by
    apply Finset.inf'_eq_of_forall
    intro i _
    exact hβ_eq_one i
  have hM_bound' : infNorm M_inv ≤ infNormVec y := by
    simpa [y, hy_sup, hβ_one] using hM_bound
  exact le_trans hU_bound hM_bound'

end NumStability
