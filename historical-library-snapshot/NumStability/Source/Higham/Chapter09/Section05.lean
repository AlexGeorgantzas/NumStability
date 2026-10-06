import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import NumStability.Source.Higham.Chapter08.Lemma08.CorrectedCondition.RowDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LU.SpecialMatrices
import NumStability.Algorithms.LU.Tridiagonal
import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Algorithms.LU.TridiagonalRecurrence
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section04

/-!
# Higham Chapter 9: Section05

Canonical source-correspondence owner from Chapter 9 destination-DAG layer 4.
-/

namespace NumStability

open scoped BigOperators
open ComplexConjugate
open Matrix

/-- **Equation (9.17)** / corrected Lemma-8.8 route, exposed as a reusable
source-facing predicate for Chapter 9 wrappers. -/
def higham9_17_rowDiagDom_absLU_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) : Prop :=
  infNorm (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) ≤
    (2 * (n : ℝ) - 1) * infNorm A

/-- **Equation (9.17)**, exact-LU algebraic bridge to the Skeel condition of
the final upper factor.

If `A = L U` and `U_inv` is an exact inverse of `U`, then
`‖|L||U|‖∞ ≤ condSkeel(U) ‖A‖∞`.  This is the local Chapter 9 algebra behind
the source step `|L||U| = |A U⁻¹| |U| ≤ |A||U⁻¹||U|`. -/
theorem higham9_17_absLU_infNorm_le_condSkeel_of_LUFactSpec {n : ℕ}
    (hn : 0 < n)
    (A L U U_inv : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hUInv : IsInverse n U U_inv) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤
      condSkeel n hn U U_inv * infNorm A := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  let κrow : Fin n → ℝ :=
    fun s => ∑ k : Fin n, |U_inv s k| * (∑ j : Fin n, |U k j|)
  have hprod : matMul n L U = A := by
    ext i j
    exact hLU.product_eq i j
  have hUright : matMul n U U_inv = idMatrix n := by
    ext i j
    exact hUInv.2 i j
  have hAUinv : matMul n A U_inv = L := by
    calc
      matMul n A U_inv = matMul n (matMul n L U) U_inv := by rw [hprod]
      _ = matMul n L (matMul n U U_inv) := matMul_assoc n L U U_inv
      _ = matMul n L (idMatrix n) := by rw [hUright]
      _ = L := matMul_id_right n L
  have hL_entry : ∀ i k : Fin n, L i k = ∑ s : Fin n, A i s * U_inv s k := by
    intro i k
    simpa [matMul] using (congrFun (congrFun hAUinv i) k).symm
  have hκrow_le : ∀ s : Fin n, κrow s ≤ condSkeel n hn U U_inv := by
    intro s
    unfold κrow condSkeel
    exact Finset.le_sup'
      (fun i => ∑ k : Fin n, |U_inv i k| * (∑ j : Fin n, |U k j|))
      (Finset.mem_univ s)
  have hcond_nonneg : 0 ≤ condSkeel n hn U U_inv := by
    let i0 : Fin n := ⟨0, hn⟩
    have hrow0_nonneg :
        0 ≤ ∑ k : Fin n, |U_inv i0 k| * (∑ j : Fin n, |U k j|) := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun j _ => abs_nonneg _))
    exact le_trans hrow0_nonneg (hκrow_le i0)
  have hW_nonneg : ∀ i j : Fin n, 0 ≤ W i j := by
    intro i j
    unfold W matMul absMatrix
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |W i j| = ∑ j : Fin n, W i j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg (hW_nonneg i j)]
      _ = ∑ j : Fin n, ∑ k : Fin n, |L i k| * |U k j| := by
        simp [W, matMul, absMatrix]
      _ ≤ ∑ j : Fin n, ∑ k : Fin n,
            (∑ s : Fin n, |A i s| * |U_inv s k|) * |U k j| := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro k _
          have hLik :
              |L i k| ≤ ∑ s : Fin n, |A i s| * |U_inv s k| := by
            rw [hL_entry i k]
            calc
              |∑ s : Fin n, A i s * U_inv s k|
                  ≤ ∑ s : Fin n, |A i s * U_inv s k| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ = ∑ s : Fin n, |A i s| * |U_inv s k| := by
                    apply Finset.sum_congr rfl
                    intro s _
                    rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hLik (abs_nonneg _)
      _ = ∑ k : Fin n,
            (∑ s : Fin n, |A i s| * |U_inv s k|) * (∑ j : Fin n, |U k j|) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [← Finset.mul_sum]
      _ = ∑ k : Fin n, ∑ s : Fin n,
            (|A i s| * |U_inv s k|) * (∑ j : Fin n, |U k j|) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
      _ = ∑ s : Fin n, ∑ k : Fin n,
            |A i s| * (|U_inv s k| * (∑ j : Fin n, |U k j|)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = ∑ s : Fin n, |A i s| * κrow s := by
          unfold κrow
          apply Finset.sum_congr rfl
          intro s _
          rw [← Finset.mul_sum]
      _ ≤ ∑ s : Fin n, |A i s| * condSkeel n hn U U_inv := by
          apply Finset.sum_le_sum
          intro s _
          exact mul_le_mul_of_nonneg_left (hκrow_le s) (abs_nonneg _)
      _ = (∑ s : Fin n, |A i s|) * condSkeel n hn U U_inv := by
          rw [Finset.sum_mul]
      _ ≤ infNorm A * condSkeel n hn U U_inv := by
          exact mul_le_mul_of_nonneg_right (row_sum_le_infNorm A i) hcond_nonneg
      _ = condSkeel n hn U U_inv * infNorm A := by ring
  · exact mul_nonneg hcond_nonneg (infNorm_nonneg A)

/-- **Equation (9.17)**, source-facing norm bound from the corrected
Chapter-8 Lemma-8.8 hypothesis on the final upper factor.

If `A = L U` and the exact upper factor `U` satisfies the corrected strict-upper
row-sum dominance condition from Lemma 8.8, then
`‖|L||U|‖∞ ≤ (2n - 1) ‖A‖∞`. -/
theorem higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec {n : ℕ}
    (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hURow : higham8_8_rowDiagDominantUpper n U) :
    higham9_17_rowDiagDom_absLU_bound n A L U := by
  have hURow' := hURow
  rcases hURow with ⟨hUT, hUdiag, _⟩
  have hdetU :
      Matrix.det (U : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    det_ne_zero_of_upper_triangular_diag_ne_zero n U hUT hUdiag
  let U_inv : Fin n → Fin n → ℝ := nonsingInv n U
  have hUInv : IsInverse n U U_inv :=
    isInverse_nonsingInv_of_det_ne_zero n U hdetU
  calc
    infNorm (matMul n (absMatrix n L) (absMatrix n U))
        ≤ condSkeel n hn U U_inv * infNorm A :=
      higham9_17_absLU_infNorm_le_condSkeel_of_LUFactSpec
        hn A L U U_inv hLU hUInv
    _ ≤ (2 * (n : ℝ) - 1) * infNorm A := by
      exact mul_le_mul_of_nonneg_right
        (higham8_8_rowDiagDominantUpper_condSkeel_bound n hn U U_inv hURow' hUInv)
        (infNorm_nonneg A)

/-- **Problem 9.9 / equation (9.17)**, no-pivot reduced-growth bound in
Skeel-condition form.

The exact-LU algebraic bridge `‖|L||U|‖∞ ≤ condSkeel(U) ‖A‖∞` is composed
with the Problem 9.9 reduced-matrix growth theorem; nonsingularity supplies
the positive source denominator. -/
theorem higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_condSkeel_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    (A L U U_inv : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hUInv : IsInverse n U U_inv)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤
        1 + (n : ℝ) * condSkeel n hn U U_inv := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  have hAinf : 0 < infNorm A :=
    higham9_infNorm_pos_of_det_ne_zero hn A hdetA
  have hbase :
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤
        1 + (n : ℝ) * infNorm W / infNorm A := by
    simpa [W] using
      higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div
        hn A L U hAmax hAinf
  have hdiv : infNorm W / infNorm A ≤ condSkeel n hn U U_inv := by
    rw [div_le_iff₀ hAinf]
    simpa [W] using
      higham9_17_absLU_infNorm_le_condSkeel_of_LUFactSpec hn A L U U_inv hLU hUInv
  have hscaled :
      (n : ℝ) * infNorm W / infNorm A ≤
        (n : ℝ) * condSkeel n hn U U_inv := by
    calc
      (n : ℝ) * infNorm W / infNorm A
          = (n : ℝ) * (infNorm W / infNorm A) := by ring
      _ ≤ (n : ℝ) * condSkeel n hn U U_inv :=
          mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg n)
  exact ⟨hAmax, by linarith⟩

/-- **Problem 9.9 / equation (9.17)**, exact no-pivot final-`U` growth bound
in Skeel-condition form. -/
theorem higham_problem9_9_growthFactorEntry_le_one_add_card_mul_condSkeel_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    (A L U U_inv : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hUInv : IsInverse n U U_inv)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U hAmax ≤
        1 + (n : ℝ) * condSkeel n hn U U_inv := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  have hAinf : 0 < infNorm A :=
    higham9_infNorm_pos_of_det_ne_zero hn A hdetA
  have hbase :
      growthFactorEntry hn A U hAmax ≤
        1 + (n : ℝ) * infNorm W / infNorm A := by
    simpa [W] using
      higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div
        hn hLU hAmax hAinf
  have hdiv : infNorm W / infNorm A ≤ condSkeel n hn U U_inv := by
    rw [div_le_iff₀ hAinf]
    simpa [W] using
      higham9_17_absLU_infNorm_le_condSkeel_of_LUFactSpec hn A L U U_inv hLU hUInv
  have hscaled :
      (n : ℝ) * infNorm W / infNorm A ≤
        (n : ℝ) * condSkeel n hn U U_inv := by
    calc
      (n : ℝ) * infNorm W / infNorm A
          = (n : ℝ) * (infNorm W / infNorm A) := by ring
      _ ≤ (n : ℝ) * condSkeel n hn U U_inv :=
          mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg n)
  exact ⟨hAmax, by linarith⟩

/-- **Problem 9.9 / equation (9.17)**, no-pivot reduced-growth bound in the
printed row-dominant-upper form.

This composes the exact reduced-matrix growth theorem with the corrected
equation (9.17) bridge `‖|L||U|‖∞ <= (2n - 1) ‖A‖∞` when the final upper
factor satisfies the Chapter 8 row-dominant-upper hypothesis. -/
theorem higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_two_card_sub_one_of_rowDiagDomUpper_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hURow : higham8_8_rowDiagDominantUpper n U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤
        1 + (n : ℝ) * (2 * (n : ℝ) - 1) := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  have hAinf : 0 < infNorm A :=
    higham9_infNorm_pos_of_det_ne_zero hn A hdetA
  have hbase :
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤
        1 + (n : ℝ) * infNorm W / infNorm A := by
    simpa [W] using
      higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div
        hn A L U hAmax hAinf
  have hdiv : infNorm W / infNorm A ≤ 2 * (n : ℝ) - 1 := by
    rw [div_le_iff₀ hAinf]
    simpa [W] using
      higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec hn A L U hLU hURow
  have hscaled :
      (n : ℝ) * infNorm W / infNorm A ≤
        (n : ℝ) * (2 * (n : ℝ) - 1) := by
    calc
      (n : ℝ) * infNorm W / infNorm A
          = (n : ℝ) * (infNorm W / infNorm A) := by ring
      _ ≤ (n : ℝ) * (2 * (n : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg n)
  exact ⟨hAmax, by linarith⟩

/-- **Problem 9.9 / equation (9.17)**, exact no-pivot final-`U` growth bound
in the printed row-dominant-upper form. -/
theorem higham_problem9_9_growthFactorEntry_le_one_add_card_mul_two_card_sub_one_of_rowDiagDomUpper_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hURow : higham8_8_rowDiagDominantUpper n U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U hAmax ≤
        1 + (n : ℝ) * (2 * (n : ℝ) - 1) := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  have hAinf : 0 < infNorm A :=
    higham9_infNorm_pos_of_det_ne_zero hn A hdetA
  have hbase :
      growthFactorEntry hn A U hAmax ≤
        1 + (n : ℝ) * infNorm W / infNorm A := by
    simpa [W] using
      higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div
        hn hLU hAmax hAinf
  have hdiv : infNorm W / infNorm A ≤ 2 * (n : ℝ) - 1 := by
    rw [div_le_iff₀ hAinf]
    simpa [W] using
      higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec hn A L U hLU hURow
  have hscaled :
      (n : ℝ) * infNorm W / infNorm A ≤
        (n : ℝ) * (2 * (n : ℝ) - 1) := by
    calc
      (n : ℝ) * infNorm W / infNorm A
          = (n : ℝ) * (infNorm W / infNorm A) := by ring
      _ ≤ (n : ℝ) * (2 * (n : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg n)
  exact ⟨hAmax, by linarith⟩

/-- **Theorem 9.9**, source side condition: for a row diagonally dominant
matrix, a zero diagonal entry forces the whole row to be zero. -/
theorem higham9_9_rowDiagDominant_zero_diag_row_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsRowDiagDominant n A)
    {i : Fin n} (hdiag : A i i = 0) :
  ∀ j : Fin n, A i j = 0 := by
  have hsum_le_zero :
      (∑ j : Fin n, (if i = j then 0 else |A i j|)) ≤ 0 := by
    simpa [hdiag] using hDD i
  have hterm_nonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (if i = j then 0 else |A i j|) := by
    intro j _
    by_cases hij : i = j <;> simp [hij, abs_nonneg]
  have hsum_eq_zero :
      (∑ j : Fin n, (if i = j then 0 else |A i j|)) = 0 := by
    exact le_antisymm hsum_le_zero (Finset.sum_nonneg hterm_nonneg)
  have hterms :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum_eq_zero
  intro j
  by_cases hij : i = j
  · simpa [hij] using hdiag
  · have hterm : (if i = j then 0 else |A i j|) = 0 :=
      hterms j (Finset.mem_univ j)
    exact abs_eq_zero.mp (by simpa [hij] using hterm)

/-- **Theorem 9.9**, source side condition: for a column diagonally dominant
matrix, a zero diagonal entry forces the whole column to be zero. -/
theorem higham9_9_colDiagDominant_zero_diag_col_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsDiagDominant n A)
    {j : Fin n} (hdiag : A j j = 0) :
    ∀ i : Fin n, A i j = 0 := by
  have hsum_le_zero :
      (∑ i : Fin n, (if i = j then 0 else |A i j|)) ≤ 0 := by
    simpa [hdiag] using hDD j
  have hterm_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (if i = j then 0 else |A i j|) := by
    intro i _
    by_cases hij : i = j <;> simp [hij, abs_nonneg]
  have hsum_eq_zero :
      (∑ i : Fin n, (if i = j then 0 else |A i j|)) = 0 := by
    exact le_antisymm hsum_le_zero (Finset.sum_nonneg hterm_nonneg)
  have hterms :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum_eq_zero
  intro i
  by_cases hij : i = j
  · simpa [hij] using hdiag
  · have hterm : (if i = j then 0 else |A i j|) = 0 :=
      hterms i (Finset.mem_univ i)
    exact abs_eq_zero.mp (by simpa [hij] using hterm)

/-- **Theorem 9.9**, source side condition: a nonsingular row diagonally
dominant matrix has nonzero diagonal entries. -/
theorem higham9_9_rowDiagDominant_diag_ne_zero_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hDD : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ i : Fin n, A i i ≠ 0 := by
  intro i hdiag
  have hrow := higham9_9_rowDiagDominant_zero_diag_row_zero hDD hdiag
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i
    (fun j => by simpa [Matrix.of_apply] using hrow j))

/-- **Theorem 9.9**, source side condition: a nonsingular column diagonally
dominant matrix has nonzero diagonal entries. -/
theorem higham9_9_colDiagDominant_diag_ne_zero_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hDD : IsDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ i : Fin n, A i i ≠ 0 := by
  intro i hdiag
  have hcol := higham9_9_colDiagDominant_zero_diag_col_zero hDD hdiag
  exact hdet (Matrix.det_eq_zero_of_column_eq_zero i
    (fun j => by simpa [Matrix.of_apply] using hcol j))

/-- **Theorem 9.9**, row diagonal dominance bounds each off-diagonal row
entry by the corresponding diagonal entry. -/
theorem higham9_9_rowDiagDominant_offdiag_abs_le_diag {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsRowDiagDominant n A)
    {i j : Fin n} (hij : j ≠ i) :
    |A i j| ≤ |A i i| := by
  have hterm :
      |A i j| ≤ ∑ k : Fin n, (if i = k then 0 else |A i k|) := by
    have hj :
        (fun k : Fin n => if i = k then (0 : ℝ) else |A i k|) j =
          |A i j| := by
      simp [Ne.symm hij]
    rw [← hj]
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun k : Fin n => if i = k then (0 : ℝ) else |A i k|)
      (by intro k _; by_cases hik : i = k <;> simp [hik, abs_nonneg])
      (Finset.mem_univ j)
  exact le_trans hterm (hDD i)

/-- **Theorem 9.9**, column diagonal dominance bounds each off-diagonal
column entry by the corresponding diagonal entry. -/
theorem higham9_9_colDiagDominant_offdiag_abs_le_diag {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsDiagDominant n A)
    {i j : Fin n} (hij : i ≠ j) :
    |A i j| ≤ |A j j| := by
  have hterm :
      |A i j| ≤ ∑ k : Fin n, (if k = j then 0 else |A k j|) := by
    have hi :
        (fun k : Fin n => if k = j then (0 : ℝ) else |A k j|) i =
          |A i j| := by
      simp [hij]
    rw [← hi]
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun k : Fin n => if k = j then (0 : ℝ) else |A k j|)
      (by intro k _; by_cases hkj : k = j <;> simp [hkj, abs_nonneg])
      (Finset.mem_univ i)
  exact le_trans hterm (hDD j)

/-- **Theorem 9.9**, row diagonal dominance gives a unit bound for the
off-diagonal row ratio `aᵢⱼ / aᵢᵢ` when the diagonal entry is nonzero. -/
theorem higham9_9_rowDiagDominant_entry_ratio_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsRowDiagDominant n A)
    {i j : Fin n} (hij : j ≠ i) (hdiag : A i i ≠ 0) :
    |A i j / A i i| ≤ 1 := by
  have hle : |A i j| ≤ |A i i| :=
    higham9_9_rowDiagDominant_offdiag_abs_le_diag hDD hij
  have hden_pos : 0 < |A i i| := abs_pos.mpr hdiag
  calc
    |A i j / A i i| = |A i j| / |A i i| := by rw [abs_div]
    _ ≤ |A i i| / |A i i| :=
        div_le_div_of_nonneg_right hle (abs_nonneg _)
    _ = 1 := div_self (ne_of_gt hden_pos)

/-- **Theorem 9.9**, column diagonal dominance gives the source first-step
unit multiplier bound `|aᵢⱼ / aⱼⱼ| <= 1` when the diagonal entry is nonzero. -/
theorem higham9_9_colDiagDominant_entry_ratio_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsDiagDominant n A)
    {i j : Fin n} (hij : i ≠ j) (hdiag : A j j ≠ 0) :
    |A i j / A j j| ≤ 1 := by
  have hle : |A i j| ≤ |A j j| :=
    higham9_9_colDiagDominant_offdiag_abs_le_diag hDD hij
  have hden_pos : 0 < |A j j| := abs_pos.mpr hdiag
  calc
    |A i j / A j j| = |A i j| / |A j j| := by rw [abs_div]
    _ ≤ |A j j| / |A j j| :=
        div_le_div_of_nonneg_right hle (abs_nonneg _)
    _ = 1 := div_self (ne_of_gt hden_pos)

/-- **Theorem 9.9**, nonsingular row diagonal dominance gives the row-ratio
unit bound without a separate diagonal-nonzero hypothesis. -/
theorem higham9_9_rowDiagDominant_entry_ratio_abs_le_one_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hDD : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {i j : Fin n} (hij : j ≠ i) :
    |A i j / A i i| ≤ 1 :=
  higham9_9_rowDiagDominant_entry_ratio_abs_le_one hDD hij
    ((higham9_9_rowDiagDominant_diag_ne_zero_of_det_ne_zero hDD hdet) i)

/-- **Theorem 9.9**, nonsingular column diagonal dominance gives the
source first-step unit multiplier bound without a separate diagonal-nonzero
hypothesis. -/
theorem higham9_9_colDiagDominant_entry_ratio_abs_le_one_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hDD : IsDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {i j : Fin n} (hij : i ≠ j) :
    |A i j / A j j| ≤ 1 :=
  higham9_9_colDiagDominant_entry_ratio_abs_le_one hDD hij
    ((higham9_9_colDiagDominant_diag_ne_zero_of_det_ne_zero hDD hdet) j)

/-- **Theorem 9.9**, column diagonal dominance bounds the sum of the first
column no-pivot multipliers by one.  This is the finite-sum form of the
source statement that column diagonal dominance gives `|lᵢ₁| <= 1` at the
first elimination step. -/
theorem higham9_9_colDiagDominant_first_column_multiplier_sum_le_one {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0) :
    (∑ i : Fin m, |A i.succ 0 / A 0 0|) ≤ 1 := by
  have hden_pos : 0 < |A 0 0| := abs_pos.mpr hdiag
  have hcol0 : (∑ i : Fin m, |A i.succ 0|) ≤ |A 0 0| := by
    have h := hDD (0 : Fin (m + 1))
    rw [Fin.sum_univ_succ] at h
    simpa using h
  have hsum_div :
      (∑ i : Fin m, |A i.succ 0 / A 0 0|) =
        (∑ i : Fin m, |A i.succ 0|) / |A 0 0| := by
    calc
      (∑ i : Fin m, |A i.succ 0 / A 0 0|)
          = ∑ i : Fin m, |A i.succ 0| / |A 0 0| := by
              apply Finset.sum_congr rfl
              intro i _
              rw [abs_div]
      _ = (∑ i : Fin m, |A i.succ 0|) / |A 0 0| := by
              rw [Finset.sum_div]
  calc
    (∑ i : Fin m, |A i.succ 0 / A 0 0|)
        = (∑ i : Fin m, |A i.succ 0|) / |A 0 0| := hsum_div
    _ ≤ |A 0 0| / |A 0 0| :=
        div_le_div_of_nonneg_right hcol0 (abs_nonneg _)
    _ = 1 := div_self (ne_of_gt hden_pos)

/-- **Theorem 9.9**, column diagonal dominance bounds the first-column
multiplier sum with one selected trailing row removed.  This is the sharp
finite-sum form consumed by the first Schur-complement diagonal-dominance
proof. -/
theorem higham9_9_colDiagDominant_first_column_multiplier_sum_except_le
    {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0) (j : Fin m) :
    (∑ i : Fin m, (if i = j then 0 else |A i.succ 0 / A 0 0|)) ≤
      1 - |A j.succ 0 / A 0 0| := by
  classical
  let f : Fin m → ℝ := fun i => |A i.succ 0 / A 0 0|
  have htotal : (∑ i : Fin m, f i) ≤ 1 := by
    simpa [f] using
      higham9_9_colDiagDominant_first_column_multiplier_sum_le_one hDD hdiag
  have hsplit :
      (∑ i : Fin m, f i) =
        f j + ∑ i : Fin m, (if i = j then 0 else f i) := by
    calc
      (∑ i : Fin m, f i)
          = ∑ i : Fin m,
              ((if i = j then f i else 0) + (if i = j then 0 else f i)) := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hij : i = j <;> simp [hij]
      _ = (∑ i : Fin m, if i = j then f i else 0) +
            ∑ i : Fin m, (if i = j then 0 else f i) := by
              rw [Finset.sum_add_distrib]
      _ = f j + ∑ i : Fin m, (if i = j then 0 else f i) := by
              congr 1
              rw [Finset.sum_eq_single j]
              · simp
              · intro i _ hij
                simp [hij]
              · intro hj
                exact (hj (Finset.mem_univ j)).elim
  have hbound : f j + ∑ i : Fin m, (if i = j then 0 else f i) ≤ 1 := by
    simpa [hsplit] using htotal
  have hrest : ∑ i : Fin m, (if i = j then 0 else f i) ≤ 1 - f j := by
    linarith
  simpa [f] using hrest

/-- **Theorem 9.9**, column diagonal dominance is preserved by the first
no-pivot Schur-complement step.  This is the local Split-2 Schur-complement
dependency behind the column-dominant half of Wilkinson's diagonal-dominance
growth theorem; it does not invoke the row-dominant Lemma 8.8 route. -/
theorem higham9_9_colDiagDominant_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0) :
    IsDiagDominant m (higham9_1_firstSchurComplement A) := by
  classical
  intro j
  let S : Fin m → Fin m → ℝ := higham9_1_firstSchurComplement A
  let aoff : ℝ := ∑ i : Fin m, if i = j then 0 else |A i.succ j.succ|
  let rsum : ℝ := ∑ i : Fin m, if i = j then 0 else |A i.succ 0 / A 0 0|
  let rj : ℝ := |A j.succ 0 / A 0 0|
  let a0j : ℝ := |A 0 j.succ|
  have hcolj : a0j + aoff ≤ |A j.succ j.succ| := by
    have h := hDD j.succ
    rw [Fin.sum_univ_succ] at h
    simpa [aoff, a0j, Fin.succ_inj] using h
  have hratio : rsum ≤ 1 - rj := by
    simpa [rsum, rj] using
      higham9_9_colDiagDominant_first_column_multiplier_sum_except_le hDD hdiag j
  have hsum_le :
      (∑ i : Fin m, (if i = j then 0 else |S i j|)) ≤
        aoff + rsum * a0j := by
    calc
      (∑ i : Fin m, (if i = j then 0 else |S i j|))
          ≤ ∑ i : Fin m,
              ((if i = j then 0 else |A i.succ j.succ|) +
                (if i = j then 0 else |A i.succ 0 / A 0 0| * a0j)) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hij : i = j
              · simp [hij]
              · simp only [hij, if_false]
                have htri :
                    |S i j| ≤
                      |A i.succ j.succ| + |A i.succ 0 / A 0 0| * a0j := by
                  have habs :
                      |A i.succ 0 * A 0 j.succ / A 0 0| =
                        |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
                    have hden_abs : |A 0 0| ≠ 0 := abs_ne_zero.mpr hdiag
                    calc
                      |A i.succ 0 * A 0 j.succ / A 0 0|
                          = |A i.succ 0| * |A 0 j.succ| / |A 0 0| := by
                              rw [abs_div, abs_mul]
                      _ = (|A i.succ 0| / |A 0 0|) * |A 0 j.succ| := by
                              field_simp [hden_abs]
                      _ = |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
                              rw [abs_div]
                  calc
                    |S i j|
                        = |A i.succ j.succ -
                            A i.succ 0 * A 0 j.succ / A 0 0| := by
                            simp [S, higham9_1_firstSchurComplement,
                              luFirstSchurComplement]
                    _ ≤ |A i.succ j.succ| +
                          |A i.succ 0 * A 0 j.succ / A 0 0| :=
                        by
                          simpa [abs_neg] using
                            (abs_sub_le (A i.succ j.succ) 0
                              (A i.succ 0 * A 0 j.succ / A 0 0))
                    _ = |A i.succ j.succ| +
                          |A i.succ 0 / A 0 0| * a0j := by
                        rw [habs]
                exact htri
      _ = aoff + rsum * a0j := by
              simp [aoff, rsum, Finset.sum_add_distrib, Finset.sum_mul]
  have hratio_mul : rsum * a0j ≤ (1 - rj) * a0j :=
    mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
  have hsource_to_diag :
      aoff + (1 - rj) * a0j ≤ |A j.succ j.succ| - rj * a0j := by
    nlinarith [hcolj]
  have hdiag_lower :
      |A j.succ j.succ| - rj * a0j ≤ |S j j| := by
    have hb_abs :
        |A j.succ 0 * A 0 j.succ / A 0 0| =
          rj * a0j := by
      have hden_abs : |A 0 0| ≠ 0 := abs_ne_zero.mpr hdiag
      calc
        |A j.succ 0 * A 0 j.succ / A 0 0|
            = |A j.succ 0| * |A 0 j.succ| / |A 0 0| := by
                rw [abs_div, abs_mul]
        _ = (|A j.succ 0| / |A 0 0|) * |A 0 j.succ| := by
                field_simp [hden_abs]
        _ = |A j.succ 0 / A 0 0| * |A 0 j.succ| := by
                rw [abs_div]
        _ = rj * a0j := rfl
    have hrev :
        |A j.succ j.succ| - |A j.succ 0 * A 0 j.succ / A 0 0| ≤
          |A j.succ j.succ - A j.succ 0 * A 0 j.succ / A 0 0| := by
      exact abs_sub_abs_le_abs_sub (A j.succ j.succ)
        (A j.succ 0 * A 0 j.succ / A 0 0)
    calc
      |A j.succ j.succ| - rj * a0j
          = |A j.succ j.succ| -
              |A j.succ 0 * A 0 j.succ / A 0 0| := by rw [hb_abs]
      _ ≤ |A j.succ j.succ - A j.succ 0 * A 0 j.succ / A 0 0| := hrev
      _ = |S j j| := by
          simp [S, higham9_1_firstSchurComplement, luFirstSchurComplement]
  calc
    (∑ i : Fin m, (if i = j then 0 else |higham9_1_firstSchurComplement A i j|))
        = ∑ i : Fin m, (if i = j then 0 else |S i j|) := rfl
    _ ≤ aoff + rsum * a0j := hsum_le
    _ ≤ aoff + (1 - rj) * a0j := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hratio_mul aoff
    _ ≤ |A j.succ j.succ| - rj * a0j := hsource_to_diag
    _ ≤ |S j j| := hdiag_lower
    _ = |higham9_1_firstSchurComplement A j j| := rfl

/-- **Theorem 9.9**, first-step max-entry growth for the column-dominant
no-pivot route.  The first Schur complement has every entry bounded by twice
the max-entry norm of the source matrix.  This is a local dependency for the
remaining direct `rho_n <= 2` growth proof; it does not use the row-dominant
equation (9.17) route. -/
theorem higham9_9_colDiagDominant_firstSchurComplement_maxEntryNorm_le_two {m : ℕ}
    (hm : 0 < m)
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0) :
    maxEntryNorm hm (higham9_1_firstSchurComplement A) ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  classical
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  let hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  change Finset.sup' Finset.univ hne
      (fun i => Finset.sup' Finset.univ hne
        (fun j => |higham9_1_firstSchurComplement A i j|)) ≤ 2 * M
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  have hratio : |A i.succ 0 / A 0 0| ≤ 1 :=
    higham9_9_colDiagDominant_entry_ratio_abs_le_one hDD
      (Fin.succ_ne_zero i) hdiag
  have hsource : |A i.succ j.succ| ≤ M := by
    simpa [M] using entry_le_maxEntryNorm (Nat.succ_pos m) A i.succ j.succ
  have hpivotRow : |A 0 j.succ| ≤ M := by
    simpa [M] using entry_le_maxEntryNorm (Nat.succ_pos m) A 0 j.succ
  have hprod :
      |A i.succ 0 / A 0 0| * |A 0 j.succ| ≤ 1 * M :=
    mul_le_mul hratio hpivotRow (abs_nonneg _) (by norm_num)
  have hfactor :
      |A i.succ 0 * A 0 j.succ / A 0 0| =
        |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
    have hden_abs : |A 0 0| ≠ 0 := abs_ne_zero.mpr hdiag
    calc
      |A i.succ 0 * A 0 j.succ / A 0 0|
          = |A i.succ 0| * |A 0 j.succ| / |A 0 0| := by
              rw [abs_div, abs_mul]
      _ = (|A i.succ 0| / |A 0 0|) * |A 0 j.succ| := by
              field_simp [hden_abs]
      _ = |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
              rw [abs_div]
  calc
    |higham9_1_firstSchurComplement A i j|
        = |A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0| := by
            simp [higham9_1_firstSchurComplement, luFirstSchurComplement]
    _ ≤ |A i.succ j.succ| + |A i.succ 0 * A 0 j.succ / A 0 0| := by
            simpa [abs_neg] using
              (abs_sub_le (A i.succ j.succ) 0
                (A i.succ 0 * A 0 j.succ / A 0 0))
    _ = |A i.succ j.succ| +
          |A i.succ 0 / A 0 0| * |A 0 j.succ| := by rw [hfactor]
    _ ≤ M + 1 * M := add_le_add hsource hprod
    _ = 2 * M := by ring

/-- **Theorem 9.9**, max-entry growth-factor endpoint from the remaining
final-upper entry bound.  This adapter isolates the last scalar step in the
diagonal-dominance proof: once the local GE trace supplies
`|U_ij| <= 2 * maxEntryNorm A` for the final upper factor, Higham's
`rho_n <= 2` conclusion follows. -/
theorem higham9_9_growthFactorEntry_le_two_of_upper_entry_bound {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hU : ∀ i j : Fin n, |U i j| ≤ 2 * maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ 2 :=
  growthFactorEntry_le_of_entry_bound_factor hn A U 2 hA hU

/-- **Theorem 9.9**, det-input max-entry growth endpoint from the remaining
final-upper entry bound.

This packages the scalar `rho <= 2` adapter with the positive denominator
derived from nonsingularity of the source matrix.  The algorithmic entry bound
for the final upper factor remains the explicit remaining hypothesis. -/
theorem higham9_9_growthFactorEntry_le_two_of_upper_entry_bound_exists_hAmax
    {n : ℕ} (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU : ∀ i j : Fin n, |U i j| ≤ 2 * maxEntryNorm hn A) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U hAmax ≤ 2 := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdet
  exact
    ⟨hAmax,
      higham9_9_growthFactorEntry_le_two_of_upper_entry_bound
        hn A U hAmax hU⟩

/-- **Theorem 9.9**, first-step lower-factor unit-bound adapter for the
column-dominant no-pivot route.  Column diagonal dominance bounds the new first
column multipliers, while the recursive tail lower factor supplies all trailing
entries. -/
theorem higham9_9_colDiagDominant_luFirstStepL_unit_bound_of_tail_unit_bound {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (L₁ : Fin m → Fin m → ℝ)
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0)
    (hL₁ : ∀ i j : Fin m, |L₁ i j| ≤ 1) :
    ∀ i j : Fin (m + 1), |luFirstStepL A L₁ i j| ≤ 1 := by
  intro i j
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · simp [luFirstStepL, hj]
    · simp [luFirstStepL, hj]
  · by_cases hj : j = 0
    · subst j
      have hratio : |A i 0 / A 0 0| ≤ 1 :=
        higham9_9_colDiagDominant_entry_ratio_abs_le_one hDD hi hdiag
      simpa [luFirstStepL, hi] using hratio
    · simpa [luFirstStepL, hi, hj] using hL₁ (i.pred hi) (j.pred hj)

/-- **Theorem 9.9**, first-step upper-factor entry adapter for the remaining
column-dominant induction route.  If the recursively produced trailing upper
factor is already bounded by `2 * maxEntryNorm A` measured against the original
matrix, then placing the pivot row above it preserves the same bound for
`luFirstStepU A U₁`. -/
theorem higham9_9_luFirstStepU_entry_bound_of_tail_entry_bound {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (U₁ : Fin m → Fin m → ℝ)
    (hU₁ : ∀ i j : Fin m,
      |U₁ i j| ≤ 2 * maxEntryNorm (Nat.succ_pos m) A) :
    ∀ i j : Fin (m + 1),
      |luFirstStepU A U₁ i j| ≤ 2 * maxEntryNorm (Nat.succ_pos m) A := by
  intro i j
  by_cases hi : i = 0
  · subst i
    have hentry : |A 0 j| ≤ maxEntryNorm (Nat.succ_pos m) A :=
      entry_le_maxEntryNorm (Nat.succ_pos m) A 0 j
    have hA_nonneg : 0 ≤ maxEntryNorm (Nat.succ_pos m) A :=
      maxEntryNorm_nonneg (Nat.succ_pos m) A
    have htwo :
        maxEntryNorm (Nat.succ_pos m) A ≤
          2 * maxEntryNorm (Nat.succ_pos m) A := by
      nlinarith
    simpa [luFirstStepU] using le_trans hentry htwo
  · by_cases hj : j = 0
    · subst j
      have hnonneg : 0 ≤ 2 * maxEntryNorm (Nat.succ_pos m) A := by
        have hA_nonneg : 0 ≤ maxEntryNorm (Nat.succ_pos m) A :=
          maxEntryNorm_nonneg (Nat.succ_pos m) A
        nlinarith
      simpa [luFirstStepU, hi] using hnonneg
    · simpa [luFirstStepU, hi, hj] using hU₁ (i.pred hi) (j.pred hj)

/-- **Theorem 9.9**, growth-factor endpoint for one no-pivot construction
step.  Once the recursive tail upper factor has the original-source
`2 * maxEntryNorm A` entry bound, the assembled first-step upper factor has
Higham's `rho <= 2` max-entry growth bound. -/
theorem higham9_9_luFirstStepU_growthFactorEntry_le_two_of_tail_entry_bound_exists_hAmax
    {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (U₁ : Fin m → Fin m → ℝ)
    (hdet :
      Matrix.det
        (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0)
    (hU₁ : ∀ i j : Fin m,
      |U₁ i j| ≤ 2 * maxEntryNorm (Nat.succ_pos m) A) :
    ∃ hAmax : 0 < maxEntryNorm (Nat.succ_pos m) A,
      growthFactorEntry (Nat.succ_pos m) A (luFirstStepU A U₁) hAmax ≤ 2 := by
  exact
    higham9_9_growthFactorEntry_le_two_of_upper_entry_bound_exists_hAmax
      (Nat.succ_pos m) A (luFirstStepU A U₁) hdet
      (higham9_9_luFirstStepU_entry_bound_of_tail_entry_bound A U₁ hU₁)

/-- **Theorem 9.9**, one no-pivot construction step with the induction-facing
factor bounds.  A tail LU factorization of the first Schur complement, a
unit-bound on the tail lower factor, and an original-source `2 * maxEntryNorm A`
bound on the tail upper factor assemble into the full first-step LU package
with the same lower and upper bounds. -/
theorem higham9_9_colDiagDominant_luFirstStep_bounds_of_tail_bounds {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    {L₁ U₁ : Fin m → Fin m → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0)
    (hLU₁ : LUFactSpec m (higham9_1_firstSchurComplement A) L₁ U₁)
    (hL₁ : ∀ i j : Fin m, |L₁ i j| ≤ 1)
    (hU₁ : ∀ i j : Fin m,
      |U₁ i j| ≤ 2 * maxEntryNorm (Nat.succ_pos m) A) :
    LUFactSpec (m + 1) A (luFirstStepL A L₁) (luFirstStepU A U₁) ∧
      (∀ i j : Fin (m + 1), |luFirstStepL A L₁ i j| ≤ 1) ∧
        (∀ i j : Fin (m + 1),
          |luFirstStepU A U₁ i j| ≤ 2 * maxEntryNorm (Nat.succ_pos m) A) := by
  exact
    ⟨LUFactSpec.of_firstSchurComplement_explicit hdiag hLU₁,
      higham9_9_colDiagDominant_luFirstStepL_unit_bound_of_tail_unit_bound
        L₁ hDD hdiag hL₁,
      higham9_9_luFirstStepU_entry_bound_of_tail_entry_bound A U₁ hU₁⟩

/-- **Theorem 9.9**, sharper first-step off-diagonal growth for the
column-dominant no-pivot route.  In the first Schur complement, off-diagonal
trailing entries are bounded by the original max-entry norm; only the diagonal
entries need the coarser `2 * maxEntryNorm A` bound. -/
theorem higham9_9_colDiagDominant_firstSchurComplement_offdiag_le_maxEntryNorm
    {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0)
    {i j : Fin m} (hij : i ≠ j) :
    |higham9_1_firstSchurComplement A i j| ≤
      maxEntryNorm (Nat.succ_pos m) A := by
  classical
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  let off : ℝ := ∑ r : Fin m, if r = j then 0 else |A r.succ j.succ|
  have hcolj : |A 0 j.succ| + off ≤ |A j.succ j.succ| := by
    have h := hDD j.succ
    rw [Fin.sum_univ_succ] at h
    simpa [off, Fin.succ_inj] using h
  have hentry_off_le : |A i.succ j.succ| ≤ off := by
    have hnonneg :
        ∀ r ∈ (Finset.univ : Finset (Fin m)),
          0 ≤ (if r = j then 0 else |A r.succ j.succ|) := by
      intro r _
      by_cases hrj : r = j <;> simp [hrj]
    have hsingle :=
      Finset.single_le_sum hnonneg (Finset.mem_univ i)
    simpa [off, hij] using hsingle
  have hpair_le_diag : |A i.succ j.succ| + |A 0 j.succ| ≤ |A j.succ j.succ| := by
    calc
      |A i.succ j.succ| + |A 0 j.succ|
          = |A 0 j.succ| + |A i.succ j.succ| := by ring
      _ ≤ |A 0 j.succ| + off := by linarith
      _ ≤ |A j.succ j.succ| := hcolj
  have hdiag_le_M : |A j.succ j.succ| ≤ M := by
    simpa [M] using entry_le_maxEntryNorm (Nat.succ_pos m) A j.succ j.succ
  have hpair_le_M : |A i.succ j.succ| + |A 0 j.succ| ≤ M :=
    le_trans hpair_le_diag hdiag_le_M
  have hratio : |A i.succ 0 / A 0 0| ≤ 1 :=
    higham9_9_colDiagDominant_entry_ratio_abs_le_one hDD
      (Fin.succ_ne_zero i) hdiag
  have hprod :
      |A i.succ 0 / A 0 0| * |A 0 j.succ| ≤ |A 0 j.succ| := by
    have hmul :
        |A i.succ 0 / A 0 0| * |A 0 j.succ| ≤
          1 * |A 0 j.succ| :=
      mul_le_mul hratio (le_refl _) (abs_nonneg _) (by norm_num)
    simpa using hmul
  have hfactor :
      |A i.succ 0 * A 0 j.succ / A 0 0| =
        |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
    have hden_abs : |A 0 0| ≠ 0 := abs_ne_zero.mpr hdiag
    calc
      |A i.succ 0 * A 0 j.succ / A 0 0|
          = |A i.succ 0| * |A 0 j.succ| / |A 0 0| := by
              rw [abs_div, abs_mul]
      _ = (|A i.succ 0| / |A 0 0|) * |A 0 j.succ| := by
              field_simp [hden_abs]
      _ = |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
              rw [abs_div]
  calc
    |higham9_1_firstSchurComplement A i j|
        = |A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0| := by
            simp [higham9_1_firstSchurComplement, luFirstSchurComplement]
    _ ≤ |A i.succ j.succ| + |A i.succ 0 * A 0 j.succ / A 0 0| := by
            simpa [abs_neg] using
              (abs_sub_le (A i.succ j.succ) 0
                (A i.succ 0 * A 0 j.succ / A 0 0))
    _ = |A i.succ j.succ| +
          |A i.succ 0 / A 0 0| * |A 0 j.succ| := by rw [hfactor]
    _ ≤ |A i.succ j.succ| + |A 0 j.succ| := by linarith
    _ ≤ M := hpair_le_M

/-- **Theorem 9.9**, real transpose convention: column diagonal dominance of
`Aᵀ` is exactly row diagonal dominance of `A`.  This is the real-matrix analogue
of the source statement that column dominance can be expressed through `A*`. -/
theorem higham9_9_colDiagDominant_transpose_iff_rowDiagDominant {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    IsDiagDominant n (matTranspose A) ↔ IsRowDiagDominant n A := by
  constructor
  · intro h i
    simpa [IsDiagDominant, IsRowDiagDominant, matTranspose, eq_comm] using h i
  · intro h i
    simpa [IsDiagDominant, IsRowDiagDominant, matTranspose, eq_comm] using h i

/-- **Theorem 9.9**, real transpose convention: row diagonal dominance of
`Aᵀ` is exactly column diagonal dominance of `A`. -/
theorem higham9_9_rowDiagDominant_transpose_iff_colDiagDominant {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    IsRowDiagDominant n (matTranspose A) ↔ IsDiagDominant n A := by
  constructor
  · intro h i
    simpa [IsDiagDominant, IsRowDiagDominant, matTranspose, eq_comm] using h i
  · intro h i
    simpa [IsDiagDominant, IsRowDiagDominant, matTranspose, eq_comm] using h i

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, first pivot row.
In the first column of an upper-Hessenberg matrix, any nonzero entry lies in
row `0` or row `1`.  Thus a nonzero partial-pivoting first pivot can only be
the current row or the next row, matching the source's adjacent-swap argument. -/
theorem higham9_10_hessenberg_firstColumn_nonzero_row_le_one {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ} {r : Fin (m + 1)}
    (hH : IsUpperHessenberg (m + 1) A) (hpivot : A r 0 ≠ 0) :
    r.val ≤ 1 := by
  by_contra hle
  have hbelow : (0 : Fin (m + 1)).val + 1 < r.val := by
    simpa using (Nat.lt_of_not_ge hle)
  exact hpivot (hH r 0 hbelow)

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, a nonsingular
active matrix has a nonzero entry in its first active column. -/
theorem higham9_10_exists_first_active_column_nonzero_of_det_ne_zero {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∃ r : Fin (m + 1), A r 0 ≠ 0 := by
  classical
  by_contra hnone
  apply hdet
  apply Matrix.det_eq_zero_of_column_eq_zero
  intro i
  by_contra hne
  exact hnone ⟨i, by simpa [Matrix.of_apply] using hne⟩

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, a nonsingular
active matrix admits a first partial-pivoting choice with nonzero pivot. -/
theorem higham9_10_exists_first_partialPivotChoice_pivot_ne_zero_of_det_ne_zero
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∃ r : Fin (m + 1),
      higham9_1_partialPivotChoice A 0 r ∧ A r 0 ≠ 0 := by
  obtain ⟨r₀, hr₀⟩ :=
    higham9_10_exists_first_active_column_nonzero_of_det_ne_zero
      (A := A) hdet
  exact higham9_1_exists_partialPivotChoice_pivot_ne_zero A 0
    ⟨r₀, Nat.zero_le _, hr₀⟩

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, the first-stage
partial-pivot row swap fixes every active row after the first reduced row. -/
theorem higham9_10_hessenberg_firstPivotRowSwap_tail {m : ℕ}
    {r : Fin (m + 1)} (hr : r.val ≤ 1) {i : Fin m}
    (hi : 1 ≤ i.val) :
    higham9_7_firstPivotRowSwap r i.succ = i.succ := by
  have hne_zero : i.succ ≠ (0 : Fin (m + 1)) := Fin.succ_ne_zero i
  have hne_r : i.succ ≠ r := by
    intro h
    have hval : i.val + 1 = r.val := by
      simpa using congrArg Fin.val h
    omega
  simp [higham9_7_firstPivotRowSwap, hne_zero, hne_r]

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, rows below the
first active row are unchanged by the first Schur-complement update. -/
theorem higham9_10_hessenberg_firstSchurComplement_tail_rows_eq_original {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ} {r : Fin (m + 1)}
    (hH : IsUpperHessenberg (m + 1) A) (hr : r.val ≤ 1)
    {i j : Fin m} (hi : 1 ≤ i.val) :
    luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) i j =
      A i.succ j.succ := by
  let sigma := higham9_7_firstPivotRowSwap r
  have hsigma : sigma i.succ = i.succ :=
    higham9_10_hessenberg_firstPivotRowSwap_tail hr hi
  have hzero : A i.succ 0 = 0 := by
    apply hH
    have hpos : 0 < i.val := by omega
    simpa using Nat.succ_lt_succ hpos
  simp [luFirstSchurComplement, higham9_2_rowPermutedMatrix, sigma, hsigma, hzero]

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, after the first
partial-pivoting adjacent row swap and Schur update, the reduced active matrix
is still upper Hessenberg. -/
theorem higham9_10_hessenberg_firstSchurComplement_isUpperHessenberg {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ} {r : Fin (m + 1)}
    (hH : IsUpperHessenberg (m + 1) A) (hpivot : A r 0 ≠ 0) :
    IsUpperHessenberg m
      (luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) := by
  intro i j hij
  have hr : r.val ≤ 1 :=
    higham9_10_hessenberg_firstColumn_nonzero_row_le_one hH hpivot
  by_cases hi : 1 ≤ i.val
  · rw [higham9_10_hessenberg_firstSchurComplement_tail_rows_eq_original hH hr hi]
    apply hH
    have hlt : j.succ.val + 1 < i.succ.val := by
      have hjs : j.succ.val = j.val + 1 := rfl
      have his : i.succ.val = i.val + 1 := rfl
      omega
    exact hlt
  · omega

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, first reduced-row
bound.  The general partial-pivoting first-step `2M` estimate is normalized
into the row-indexed form needed by the source induction for Hessenberg
matrices: reduced row `i` is bounded by `(i+2) * maxEntryNorm A`. -/
theorem higham9_10_hessenberg_firstSchurComplement_row_bound {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) {r : Fin (m + 1)}
    (hchoice : higham9_1_partialPivotChoice A 0 r) (hpivot : A r 0 ≠ 0)
    (i j : Fin m) :
    |luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) i j| ≤
      (((i.val + 2 : ℕ) : ℝ) * maxEntryNorm (Nat.succ_pos m) A) := by
  have hfirst :=
    higham9_7_partialPivot_firstSchurComplement_entry_abs_le_two A r hchoice hpivot i j
  have hcoef : (2 : ℝ) ≤ ((i.val + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 2 i.val
  exact le_trans hfirst
    (mul_le_mul_of_nonneg_right hcoef (maxEntryNorm_nonneg (Nat.succ_pos m) A))

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, stage invariant.
At a positive active stage, row `0` is the current pivot row and is bounded by
`k * M`; rows below it are unchanged source rows and are bounded by `M`. -/
def higham9_10_HessenbergStageBound {n : ℕ} (M : ℝ) (k : ℕ)
    (A : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i.val = 0 → |A i j| ≤ (k : ℝ) * M) ∧
    (∀ i j : Fin n, 1 ≤ i.val → |A i j| ≤ M)

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, one-stage
Hessenberg invariant transition.  Under a nonzero first partial pivot, the
Schur complement advances the source row bound from `k * M` to `(k+1) * M`
while preserving the unchanged-tail-row bound by `M`. -/
theorem higham9_10_hessenberg_firstSchurComplement_stageBound {m k : ℕ}
    {M : ℝ} (hM : 0 ≤ M)
    {A : Fin (m + 1) → Fin (m + 1) → ℝ} {r : Fin (m + 1)}
    (hH : IsUpperHessenberg (m + 1) A)
    (hstage : higham9_10_HessenbergStageBound M k A)
    (hchoice : higham9_1_partialPivotChoice A 0 r) (hpivot : A r 0 ≠ 0) :
    higham9_10_HessenbergStageBound M (k + 1)
      (luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) := by
  let sigma := higham9_7_firstPivotRowSwap r
  let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowPermutedMatrix A sigma
  let S : Fin m → Fin m → ℝ := luFirstSchurComplement Aperm
  change higham9_10_HessenbergStageBound M (k + 1) S
  have hr : r.val ≤ 1 :=
    higham9_10_hessenberg_firstColumn_nonzero_row_le_one hH hpivot
  constructor
  · intro i j hi0
    have hratio : |Aperm i.succ 0 / Aperm 0 0| ≤ 1 := by
      have hraw :=
        higham9_1_partialPivot_multiplier_abs_le_one A 0 r (sigma i.succ)
          hchoice hpivot (Nat.zero_le _)
      simpa [Aperm, higham9_2_rowPermutedMatrix, sigma, higham9_7_firstPivotRowSwap]
        using hraw
    have hterm_le {B : ℝ} (hB : 0 ≤ B)
        (hpivrow : |Aperm 0 j.succ| ≤ B) :
        |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| ≤ B := by
      have hfactor :
          |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| =
            |Aperm i.succ 0 / Aperm 0 0| * |Aperm 0 j.succ| := by
        rw [abs_div, abs_mul, abs_div]
        ring
      calc
        |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
            = |Aperm i.succ 0 / Aperm 0 0| * |Aperm 0 j.succ| := hfactor
        _ ≤ 1 * B := mul_le_mul hratio hpivrow (abs_nonneg _) zero_le_one
        _ = B := by ring
    have hsplit :
        |S i j| ≤
          |Aperm i.succ j.succ| +
            |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| := by
      change
        |Aperm i.succ j.succ -
            Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| ≤
          |Aperm i.succ j.succ| +
            |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
      simpa [sub_eq_add_neg] using
        abs_add_le (Aperm i.succ j.succ)
          (-(Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0))
    by_cases hr0 : r = 0
    · have hsigma_i : sigma i.succ = i.succ := by
        simp [sigma, higham9_7_firstPivotRowSwap, hr0, Fin.succ_ne_zero]
      have hentry : |Aperm i.succ j.succ| ≤ M := by
        have htail : 1 ≤ i.succ.val := by
          simp
        simpa [Aperm, higham9_2_rowPermutedMatrix, hsigma_i] using
          hstage.2 i.succ j.succ htail
      have hpivrow : |Aperm 0 j.succ| ≤ (k : ℝ) * M := by
        simpa [Aperm, higham9_2_rowPermutedMatrix, sigma,
          higham9_7_firstPivotRowSwap, hr0] using
          hstage.1 (0 : Fin (m + 1)) j.succ rfl
      have hkM_nonneg : 0 ≤ (k : ℝ) * M :=
        mul_nonneg (Nat.cast_nonneg' k) hM
      calc
        |S i j|
            ≤ |Aperm i.succ j.succ| +
                |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| := hsplit
        _ ≤ M + (k : ℝ) * M :=
              add_le_add hentry (hterm_le hkM_nonneg hpivrow)
        _ = ((k + 1 : ℕ) : ℝ) * M := by
              rw [Nat.cast_add, Nat.cast_one]
              ring
    · have hrval : r.val = 1 := by
        have hrne : r.val ≠ 0 := by
          intro hzero
          exact hr0 (Fin.ext hzero)
        omega
      have hir : i.succ = r := by
        apply Fin.ext
        have his : i.succ.val = i.val + 1 := rfl
        omega
      have hsigma_i : sigma i.succ = 0 := by
        simp [sigma, higham9_7_firstPivotRowSwap, hir]
      have hentry : |Aperm i.succ j.succ| ≤ (k : ℝ) * M := by
        simpa [Aperm, higham9_2_rowPermutedMatrix, hsigma_i] using
          hstage.1 (0 : Fin (m + 1)) j.succ rfl
      have hpivrow : |Aperm 0 j.succ| ≤ M := by
        have hr_tail : 1 ≤ r.val := by omega
        simpa [Aperm, higham9_2_rowPermutedMatrix, sigma,
          higham9_7_firstPivotRowSwap] using
          hstage.2 r j.succ hr_tail
      have hkM_nonneg : 0 ≤ (k : ℝ) * M :=
        mul_nonneg (Nat.cast_nonneg' k) hM
      calc
        |S i j|
            ≤ |Aperm i.succ j.succ| +
                |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| := hsplit
        _ ≤ (k : ℝ) * M + M := add_le_add hentry (hterm_le hM hpivrow)
        _ = ((k + 1 : ℕ) : ℝ) * M := by
              rw [Nat.cast_add, Nat.cast_one]
              ring
  · intro i j hi
    have htail :=
      higham9_10_hessenberg_firstSchurComplement_tail_rows_eq_original
        hH hr hi (i := i) (j := j)
    have hS_eq : S i j = A i.succ j.succ := by
      simpa [S, Aperm, sigma] using htail
    rw [hS_eq]
    have hsucc_tail : 1 ≤ i.succ.val := by
      simp
    exact hstage.2 i.succ j.succ hsucc_tail

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, initial stage
bound.  Every entry of the original active matrix is bounded by its max-entry
norm, so it satisfies the source invariant with stage counter `1`. -/
theorem higham9_10_HessenbergStageBound_one_of_maxEntryNorm {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    higham9_10_HessenbergStageBound (maxEntryNorm hn A) 1 A := by
  constructor
  · intro i j _hi
    simpa using entry_le_maxEntryNorm hn A i j
  · intro i j _hi
    exact entry_le_maxEntryNorm hn A i j

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, an explicit
recursive trace interface for partial-pivoting elimination on upper-Hessenberg
active matrices.  The `step` constructor records exactly the adjacent
partial-pivot row swap and first Schur complement used by the source proof; it
does not assert that such a trace has been constructed for every nonsingular
input. -/
inductive higham9_10_HessenbergGEPPTrace (M : ℝ) :
    (k n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | init {n : ℕ} {A : Fin n → Fin n → ℝ}
      (hH : IsUpperHessenberg n A)
      (hstage : higham9_10_HessenbergStageBound M 1 A) :
      higham9_10_HessenbergGEPPTrace M 1 n A
  | step {m k : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r : Fin (m + 1)}
      (hprev : higham9_10_HessenbergGEPPTrace M k (m + 1) A)
      (hchoice : higham9_1_partialPivotChoice A 0 r)
      (hpivot : A r 0 ≠ 0) :
      higham9_10_HessenbergGEPPTrace M (k + 1) m
        (luFirstSchurComplement
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)))

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, recursive trace
induction.  Along any explicit Hessenberg GEPP trace, every active matrix
remains upper Hessenberg and satisfies the source stage invariant. -/
theorem higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound
    {M : ℝ} (hM : 0 ≤ M) {k n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_10_HessenbergGEPPTrace M k n A) :
    IsUpperHessenberg n A ∧ higham9_10_HessenbergStageBound M k A := by
  induction htrace with
  | init hH hstage =>
      exact ⟨hH, hstage⟩
  | step hprev hchoice hpivot ih =>
      rcases ih with ⟨hH, hstage⟩
      exact
        ⟨higham9_10_hessenberg_firstSchurComplement_isUpperHessenberg hH hpivot,
          higham9_10_hessenberg_firstSchurComplement_stageBound hM hH hstage
            hchoice hpivot⟩

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, upper-Hessenberg
projection from the recursive trace invariant. -/
theorem higham9_10_HessenbergGEPPTrace_isUpperHessenberg
    {M : ℝ} (hM : 0 ≤ M) {k n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_10_HessenbergGEPPTrace M k n A) :
    IsUpperHessenberg n A :=
  (higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound hM htrace).1

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, stage-bound
projection from the recursive trace invariant. -/
theorem higham9_10_HessenbergGEPPTrace_stageBound
    {M : ℝ} (hM : 0 ≤ M) {k n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_10_HessenbergGEPPTrace M k n A) :
    higham9_10_HessenbergStageBound M k A :=
  (higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound hM htrace).2

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, every stage
counter occurring in the explicit Hessenberg trace is positive. -/
theorem higham9_10_HessenbergGEPPTrace_stage_pos
    {M : ℝ} {k n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_10_HessenbergGEPPTrace M k n A) :
    0 < k := by
  induction htrace with
  | init _hH _hstage =>
      norm_num
  | step _hprev _hchoice _hpivot ih =>
      omega

/-- **Theorem 9.10 / upper-Hessenberg GEPP `U` trace**, a recursive exact
partial-pivoting trace that exposes the final upper-factor rows.  A step stores
the current Hessenberg trace, the adjacent partial-pivoting row swap, and the
upper factor obtained by placing the permuted pivot row above the recursively
computed upper factor of the Schur complement. -/
inductive higham9_10_HessenbergGEPPUTrace (M : ℝ) :
    (k n : ℕ) → (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {k : ℕ} {A U : Fin 0 → Fin 0 → ℝ} :
      higham9_10_HessenbergGEPPUTrace M k 0 A U
  | step {m k : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r : Fin (m + 1)} {U₁ : Fin m → Fin m → ℝ}
      (htrace : higham9_10_HessenbergGEPPTrace M k (m + 1) A)
      (hchoice : higham9_1_partialPivotChoice A 0 r)
      (hpivot : A r 0 ≠ 0)
      (hnext :
        higham9_10_HessenbergGEPPUTrace M (k + 1) m
          (luFirstSchurComplement
            (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) U₁) :
      higham9_10_HessenbergGEPPUTrace M k (m + 1) A
        (luFirstStepU
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) U₁)

/-- **Theorem 9.10 / upper-Hessenberg GEPP `U` trace**, the exposed `U` rows
are upper triangular along the recursive trace. -/
theorem higham9_10_HessenbergGEPPUTrace_upper_zero {M : ℝ} :
    ∀ {k n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_10_HessenbergGEPPUTrace M k n A U →
      ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  intro k n A U htrace
  induction htrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step hactive _hchoice _hpivot hnext ih =>
      intro i j hij
      by_cases hi : i = 0
      · subst i
        exact (Nat.not_lt_zero _ hij).elim
      · by_cases hj : j = 0
        · subst j
          simp [luFirstStepU, hi]
        · have hpred : (j.pred hj).val < (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hjval := Fin.val_pred j hj
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega
          have hrec := ih (i.pred hi) (j.pred hj) hpred
          simpa [luFirstStepU, hi, hj] using hrec

/-- **Theorem 9.10 / upper-Hessenberg GEPP `U` trace**, row-indexed upper
factor bound.  Along any explicit Hessenberg GEPP `U` trace at source stage
counter `k`, row `i` of the exposed upper factor is bounded by `(k+i)M`. -/
theorem higham9_10_HessenbergGEPPUTrace_row_bound {M : ℝ} (hM : 0 ≤ M) :
    ∀ {k n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_10_HessenbergGEPPUTrace M k n A U →
      ∀ i j : Fin n, |U i j| ≤ ((k + i.val : ℕ) : ℝ) * M := by
  intro k n A U hutrace
  induction hutrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step hactive hchoice hpivot hnext ih =>
      rename_i m k A r U₁
      intro i j
      let sigma := higham9_7_firstPivotRowSwap r
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowPermutedMatrix A sigma
      rcases higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound
          hM hactive with ⟨hH, hstage⟩
      by_cases hi : i = 0
      · subst i
        have hpivrow : |Aperm 0 j| ≤ (k : ℝ) * M := by
          by_cases hr0 : r = 0
          · simpa [Aperm, higham9_2_rowPermutedMatrix, sigma,
              higham9_7_firstPivotRowSwap, hr0] using
              hstage.1 (0 : Fin (m + 1)) j rfl
          · have hrle : r.val ≤ 1 :=
              higham9_10_hessenberg_firstColumn_nonzero_row_le_one hH hpivot
            have hrpos : 1 ≤ r.val := by
              have hrne : r.val ≠ 0 := by
                intro hzero
                exact hr0 (Fin.ext hzero)
              omega
            have htail : |A r j| ≤ M := hstage.2 r j hrpos
            have hkpos : 0 < k :=
              higham9_10_HessenbergGEPPTrace_stage_pos hactive
            have hkcoef : (1 : ℝ) ≤ (k : ℝ) := by
              exact_mod_cast hkpos
            have hM_le : M ≤ (k : ℝ) * M := by
              calc
                M = (1 : ℝ) * M := by ring
                _ ≤ (k : ℝ) * M :=
                    mul_le_mul_of_nonneg_right hkcoef hM
            calc
              |Aperm 0 j| = |A r j| := by
                  simp [Aperm, higham9_2_rowPermutedMatrix, sigma,
                    higham9_7_firstPivotRowSwap]
              _ ≤ M := htail
              _ ≤ (k : ℝ) * M := hM_le
        simpa [Aperm, luFirstStepU] using hpivrow
      · by_cases hj : j = 0
        · subst j
          have hnonneg : 0 ≤ ((k + i.val : ℕ) : ℝ) * M :=
            mul_nonneg (Nat.cast_nonneg' (k + i.val)) hM
          simpa [Aperm, luFirstStepU, hi] using hnonneg
        · have hrec := ih (i.pred hi) (j.pred hj)
          have hidx : k + i.val = k + 1 + (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            omega
          simpa [Aperm, luFirstStepU, hi, hj, hidx] using hrec

/-- **Theorem 9.10**, final scalar step in Wilkinson's upper-Hessenberg growth
argument.  If the source induction for GEPP on an upper-Hessenberg matrix has
shown that final upper-row `i` is bounded by `(i+1) * maxEntryNorm A`, then the
Higham max-entry growth factor satisfies `rho_n^p <= n`.

This is not the full GEPP trace proof; it isolates the arithmetic consequence of
the row-indexed pivot-row bound stated in the source proof. -/
theorem higham9_10_hessenberg_growthFactorEntry_le_card_of_row_bounds {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hRowBound : ∀ i j : Fin n,
      |U i j| ≤ ((i.val + 1 : ℕ) : ℝ) * maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ (n : ℝ) := by
  apply growthFactorEntry_le_of_entry_bound_factor hn A U (n : ℝ) hA
  intro i j
  have hcoef : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt i.isLt
  exact le_trans (hRowBound i j)
    (mul_le_mul_of_nonneg_right hcoef (le_of_lt hA))

/-- **Theorem 9.10**, upper-Hessenberg componentwise stability once the
algorithmic growth bound is supplied. -/
theorem higham9_10_hessenberg_growth_backward_error (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ↑n * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * ↑n * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  hessenberg_growth_backward_error n A L_hat U_hat ε hε hLU hGrowth

/-- **Theorem 9.10**, solve-level componentwise stability for upper-Hessenberg
systems once the source growth inequality is supplied.  The theorem does not
assert the algorithmic Hessenberg growth proof; it packages the available
factorization-and-triangular-solve error theorem with the explicit
`|L_hat||U_hat| <= n |A|` hypothesis. -/
theorem higham9_10_hessenberg_lu_solve_backward_stable_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ (n : ℝ) * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ (n : ℝ) * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_tight fp n A L_hat U_hat b hL_diag hU_diag hLU hn hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hγ3n := gamma_nonneg fp hn3
  calc |ΔA i j|
      ≤ gamma fp (3 * n) * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n) * ((n : ℝ) * |A i j|) :=
        mul_le_mul_of_nonneg_left (hGrowth i j) hγ3n
    _ = (n : ℝ) * gamma fp (3 * n) * |A i j| := by ring

/-- **Theorem 9.11**, Bohte banded-growth scalar bound.

The source formula is `2^(2p-1) - (p-1)2^(p-2)`.  The formal expression uses
natural-number exponents; for the printed `p = 1` case the second coefficient
is zero, so the saturated exponent has no effect on the value.

Higham cites the external proof as Bohte [146, 1975]; Crossref identifies this
as Z. Bohte, "Bounds for Rounding Errors in the Gaussian Elimination for Band
Systems", IMA Journal of Applied Mathematics 16(2):133-142, 1975,
DOI 10.1093/imamat/16.2.133. -/
noncomputable def higham9_11_bohteBound (p : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * p - 1) - ((p : ℝ) - 1) * (2 : ℝ) ^ (p - 2)

/-- **Theorem 9.11**, Bohte formula special case `p = 1`: tridiagonal
matrices give the scalar bound `2`. -/
theorem higham9_11_bohteBound_tridiagonal :
    higham9_11_bohteBound 1 = 2 := by
  norm_num [higham9_11_bohteBound]
  rfl

/-- **Theorem 9.11**, Bohte formula special case `p = 1`, named by common
bandwidth.  This is the same scalar specialization as the tridiagonal
formula. -/
theorem higham9_11_bohteBound_bandwidth_one_formula :
    higham9_11_bohteBound 1 = 2 :=
  higham9_11_bohteBound_tridiagonal

/-- **Theorem 9.11**, arithmetic check for the formal Bohte expression at
`p = 2`: the printed scalar formula evaluates to `7`.  This records only the
formula arithmetic, not a pentadiagonal growth theorem or attainability claim. -/
theorem higham9_11_bohteBound_pentadiagonal_formula :
    higham9_11_bohteBound 2 = 7 := by
  norm_num [higham9_11_bohteBound]
  rfl

/-- **Theorem 9.11**, Bohte formula special case `p = 2`, named by common
bandwidth.  This is the same scalar specialization as the pentadiagonal
formula. -/
theorem higham9_11_bohteBound_bandwidth_two_formula :
    higham9_11_bohteBound 2 = 7 :=
  higham9_11_bohteBound_pentadiagonal_formula

/-- **Theorem 9.11**, arithmetic check for the formal Bohte expression at
`p = 3`: the printed scalar formula evaluates to `28`.  This records only the
formula arithmetic, not a banded-growth theorem or attainability claim. -/
theorem higham9_11_bohteBound_bandwidth_three_formula :
    higham9_11_bohteBound 3 = 28 := by
  norm_num [higham9_11_bohteBound]
  rfl

/-- **Theorem 9.11**, arithmetic check for the source's `n = 9`, `p = 4`
Bohte example: the printed scalar formula evaluates to `116`.  This records
only the scalar formula value, not the example's pivot trace or attainability
claim. -/
theorem higham9_11_bohteBound_bandwidth_four_formula :
    higham9_11_bohteBound 4 = 116 := by
  norm_num [higham9_11_bohteBound]
  rfl

/-- **Theorem 9.11**, arithmetic check for Bohte's formal expression at
`p = 5`: the printed scalar formula evaluates to `480`.  This records only
the scalar formula value, not a banded-growth theorem or attainability claim. -/
theorem higham9_11_bohteBound_bandwidth_five_formula :
    higham9_11_bohteBound 5 = 480 := by
  norm_num [higham9_11_bohteBound]
  rfl

/-- **Theorem 9.11**, arithmetic check for the saturated formal expression at
`p = 0`.  The source theorem is used for positive bandwidths; this endpoint is
recorded for totality of the formal scalar definition. -/
theorem higham9_11_bohteBound_zero :
    higham9_11_bohteBound 0 = 2 := by
  norm_num [higham9_11_bohteBound]
  rfl

/-- **Theorem 9.11**, the printed Bohte scalar expression is nonnegative.
This discharges the nonnegativity side condition needed when using the
expression as a growth constant; it does not prove the banded growth theorem
that supplies the componentwise growth hypothesis. -/
theorem higham9_11_bohteBound_nonneg (p : ℕ) :
    0 ≤ higham9_11_bohteBound p := by
  cases p with
  | zero =>
      have h0 : higham9_11_bohteBound 0 = 2 := by
        norm_num [higham9_11_bohteBound]
        rfl
      rw [h0]
      norm_num
  | succ p =>
      cases p with
      | zero =>
          rw [higham9_11_bohteBound_tridiagonal]
          norm_num
      | succ k =>
          unfold higham9_11_bohteBound
          norm_num
          change ((k : ℝ) + 1) * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 * k + 3)
          rw [show 2 * k + 3 = k + (k + 3) by omega, pow_add]
          rw [mul_comm ((2 : ℝ) ^ k)]
          exact mul_le_mul_of_nonneg_right (by
            have hk1 : k + 1 ≤ 2 ^ (k + 1) := (k + 1).lt_two_pow_self.le
            have hmono : 2 ^ (k + 1) ≤ 2 ^ (k + 3) :=
              pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega)
            exact_mod_cast hk1.trans hmono) (pow_nonneg (by norm_num) k)

/-- **Theorem 9.11**, Bohte's scalar expression dominates the tridiagonal
value.

The formal expression is at least `2` for every natural bandwidth parameter.
This is scalar support only; the banded GEPP growth theorem supplying this
constant remains the external Bohte proof obligation. -/
theorem higham9_11_bohteBound_ge_two (p : ℕ) :
    (2 : ℝ) ≤ higham9_11_bohteBound p := by
  cases p with
  | zero =>
      norm_num [higham9_11_bohteBound]
      exact le_rfl
  | succ p =>
      cases p with
      | zero =>
          rw [higham9_11_bohteBound_tridiagonal]
      | succ k =>
          unfold higham9_11_bohteBound
          have hpow1 : 2 * (k + 1 + 1) - 1 = 2 * k + 3 := by omega
          have hpow2 : k + 1 + 1 - 2 = k := by omega
          rw [hpow1, hpow2]
          norm_num
          have hterm :
              ((k : ℝ) + 1) * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 * k + 2) := by
            rw [show 2 * k + 2 = k + (k + 2) by omega, pow_add]
            rw [mul_comm ((2 : ℝ) ^ k)]
            exact mul_le_mul_of_nonneg_right (by
              have hk1 : k + 1 ≤ 2 ^ (k + 1) := (k + 1).lt_two_pow_self.le
              have hmono : 2 ^ (k + 1) ≤ 2 ^ (k + 2) :=
                pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega)
              exact_mod_cast hk1.trans hmono) (pow_nonneg (by norm_num) k)
          have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * k + 2) := by
            have hpow : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (2 * k + 2) :=
              pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
            simpa using hpow
          have hsum :
              (2 : ℝ) + ((k : ℝ) + 1) * (2 : ℝ) ^ k ≤
                (2 : ℝ) ^ (2 * k + 2) + (2 : ℝ) ^ (2 * k + 2) :=
            add_le_add htwo hterm
          have hdouble :
              (2 : ℝ) ^ (2 * k + 2) + (2 : ℝ) ^ (2 * k + 2) =
                (2 : ℝ) ^ (2 * k + 3) := by
            rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega, pow_add]
            ring
          linarith

/-- **Theorem 9.11**, Bohte's scalar expression is strictly positive for every
formal bandwidth parameter. -/
theorem higham9_11_bohteBound_pos (p : ℕ) :
    0 < higham9_11_bohteBound p := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (higham9_11_bohteBound_ge_two p)

/-- **Theorem 9.11**, Bohte's scalar expression is at least one for every
formal bandwidth parameter. -/
theorem higham9_11_bohteBound_ge_one (p : ℕ) :
    (1 : ℝ) ≤ higham9_11_bohteBound p := by
  exact le_trans (by norm_num : (1 : ℝ) ≤ 2)
    (higham9_11_bohteBound_ge_two p)

/-- **Theorem 9.11**, Bohte scalar recurrence beyond the first two
bandwidths.  This is the closed-form arithmetic recurrence an induction proof
of the banded GEPP growth theorem can use; it does not prove the GEPP growth
bound itself. -/
theorem higham9_11_bohteBound_add_three_eq (k : ℕ) :
    higham9_11_bohteBound (k + 3) =
      4 * higham9_11_bohteBound (k + 2) + (k : ℝ) * (2 : ℝ) ^ (k + 1) := by
  unfold higham9_11_bohteBound
  norm_num
  have h1 : 2 * (k + 3) - 1 = 2 * k + 5 := by omega
  have h2 : k + 3 - 2 = k + 1 := by omega
  have h3 : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
  rw [h1, h2, h3]
  rw [show 2 * k + 5 = (2 * k + 3) + 2 by omega, pow_add]
  rw [show k + 1 = k + 1 by rfl, pow_add]
  norm_num
  ring

/-- **Theorem 9.11**, Bohte scalar recurrence as a lower step:
from bandwidth `k + 2` to `k + 3`, the printed scalar bound is at least four
times the previous scalar bound.  This is scalar support for the future banded
growth induction, not the banded GEPP theorem. -/
theorem higham9_11_bohteBound_quad_le_add_three (k : ℕ) :
    4 * higham9_11_bohteBound (k + 2) ≤ higham9_11_bohteBound (k + 3) := by
  rw [higham9_11_bohteBound_add_three_eq]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (by norm_num) (k + 1)))

/-- **Theorem 9.11**, monotonicity of the Bohte scalar bound from bandwidth
`2` onward.  This is only scalar arithmetic support for the still-open banded
growth proof. -/
theorem higham9_11_bohteBound_le_add_three (k : ℕ) :
    higham9_11_bohteBound (k + 2) ≤ higham9_11_bohteBound (k + 3) := by
  have hnon : 0 ≤ higham9_11_bohteBound (k + 2) :=
    higham9_11_bohteBound_nonneg (k + 2)
  have hle4 : higham9_11_bohteBound (k + 2) ≤
      4 * higham9_11_bohteBound (k + 2) := by
    nlinarith
  exact hle4.trans (higham9_11_bohteBound_quad_le_add_three k)

/-- **Theorem 9.11**, one-step monotonicity of the Bohte scalar bound for all
natural bandwidth parameters.  The first two steps are discharged by direct
formula evaluation; all later steps reuse the closed-form recurrence
`higham9_11_bohteBound_le_add_three`. -/
theorem higham9_11_bohteBound_le_succ (p : ℕ) :
    higham9_11_bohteBound p ≤ higham9_11_bohteBound (p + 1) := by
  cases p with
  | zero =>
      norm_num [higham9_11_bohteBound]
  | succ p =>
      cases p with
      | zero =>
          rw [higham9_11_bohteBound_tridiagonal,
            higham9_11_bohteBound_pentadiagonal_formula]
          norm_num
      | succ k =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            higham9_11_bohteBound_le_add_three k

/-- **Theorem 9.11**, monotonicity of Bohte's scalar banded-growth bound.
This is scalar support for comparing nested bandwidth parameters; the GEPP
banded-growth theorem itself remains the separate Bohte proof obligation. -/
theorem higham9_11_bohteBound_monotone :
    Monotone higham9_11_bohteBound :=
  monotone_nat_of_le_succ higham9_11_bohteBound_le_succ

/-- **Theorem 9.11**, order form of Bohte scalar monotonicity. -/
theorem higham9_11_bohteBound_le_of_le {p q : ℕ} (hpq : p ≤ q) :
    higham9_11_bohteBound p ≤ higham9_11_bohteBound q :=
  higham9_11_bohteBound_monotone hpq

/-- **Theorem 9.11**, banded growth-factor solve bound once the Bohte growth
constant has been supplied. -/
theorem higham9_11_banded_growth_factor_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ) (hρ : 0 ≤ ρ_bound)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ρ_bound * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  banded_growth_factor_solve_tight fp n A L_hat U_hat b ρ_bound hρ
    hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, monotone form of the banded growth-factor solve bound.

If the componentwise growth estimate has been proved with a smaller constant
`rho_bound`, the same solve-level theorem may be consumed at any larger
nonnegative target constant.  This is the generic version of the later
Bohte-specialized widening wrapper. -/
theorem higham9_11_banded_growth_factor_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound ρ_target : ℝ)
    (hρ_target : 0 ≤ ρ_target)
    (hρ_le : ρ_bound ≤ ρ_target)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ρ_target * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_11_banded_growth_factor_solve_tight fp n A L_hat U_hat b
    ρ_target hρ_target hL_diag hU_diag hLU hn hn3
    (fun i j =>
      le_trans (hGrowth i j)
        (mul_le_mul_of_nonneg_right hρ_le (abs_nonneg _)))

/-- **Theorem 9.11**, solve bound specialized to the printed Bohte scalar
expression.  The theorem still requires the source growth hypothesis with this
constant; it only proves the scalar nonnegativity needed by the generic
growth-factor wrapper. -/
theorem higham9_11_bohte_banded_solve_tight (fp : FPModel) (n p : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        higham9_11_bohteBound p * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        higham9_11_bohteBound p * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_11_banded_growth_factor_solve_tight fp n A L_hat U_hat b
    (higham9_11_bohteBound p) (higham9_11_bohteBound_nonneg p)
    hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, Bohte solve bound from any smaller growth constant.

This is the monotone-consumer form for proof routes that establish a sharper
or lower-bandwidth componentwise growth estimate before widening to the
printed Bohte scalar.  It does not prove the missing banded GEPP growth
theorem; it only transports an already supplied growth hypothesis through the
closed scalar comparison. -/
theorem higham9_11_bohte_banded_solve_tight_of_growth_le
    (fp : FPModel) (n p : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ higham9_11_bohteBound p)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        higham9_11_bohteBound p * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_11_bohte_banded_solve_tight fp n p A L_hat U_hat b
    hL_diag hU_diag hLU hn hn3
    (fun i j =>
      le_trans (hGrowth i j)
        (mul_le_mul_of_nonneg_right hρ_le (abs_nonneg _)))

/-- **Theorem 9.11**, solve bound after widening the Bohte bandwidth parameter.

If a caller has established the componentwise growth hypothesis at bandwidth
`q`, then the scalar monotonicity of Bohte's printed expression allows the
same solve-level conclusion at any wider parameter `p`. -/
theorem higham9_11_bohte_banded_solve_tight_of_bandwidth_le
    (fp : FPModel) (n q p : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hqp : q ≤ p)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        higham9_11_bohteBound q * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        higham9_11_bohteBound p * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_11_bohte_banded_solve_tight_of_growth_le fp n p A L_hat U_hat b
    (higham9_11_bohteBound q) (higham9_11_bohteBound_le_of_le hqp)
    hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, source-facing banded solve wrapper with an explicit
`IsBanded` hypothesis.

The structural banded hypothesis records the source side of Bohte's theorem,
while the actual GEPP growth estimate remains an explicit assumption.  This is
therefore an interface theorem, not the missing external Bohte proof. -/
theorem higham9_11_bohte_banded_solve_tight_of_isBanded_common
    (fp : FPModel) (n p q r : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hp : p ≤ r) (hq : q ≤ r)
    (hBanded : IsBanded n p q A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        higham9_11_bohteBound r * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        higham9_11_bohteBound r * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  have _hBanded_common : IsBanded n r r A :=
    isBanded_common_of_le hp hq hBanded
  exact higham9_11_bohte_banded_solve_tight fp n r A L_hat U_hat b
    hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, source-facing banded solve wrapper from any smaller
componentwise growth constant.

The structural banded hypothesis records the source side of Bohte's theorem;
the supplied `hρ_le` and `hGrowth` let callers reuse sharper or narrower
growth estimates before widening to Bohte's printed common-bandwidth constant.
This is an interface theorem, not the missing external Bohte proof. -/
theorem higham9_11_bohte_banded_solve_tight_of_isBanded_common_growth_le
    (fp : FPModel) (n p q r : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hp : p ≤ r) (hq : q ≤ r)
    (hBanded : IsBanded n p q A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ higham9_11_bohteBound r)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        higham9_11_bohteBound r * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  have _hBanded_common : IsBanded n r r A :=
    isBanded_common_of_le hp hq hBanded
  exact
    higham9_11_bohte_banded_solve_tight_of_growth_le fp n r
      A L_hat U_hat b ρ_bound hρ_le hL_diag hU_diag hLU hn hn3
      hGrowth

/-- **Theorem 9.11**, native Matrix form of the supplied-growth banded solve
wrapper.

This exposes the same proved perturbation conclusion as
`higham9_11_banded_growth_factor_solve_tight`, with the solve equation stated
using `Matrix.mulVec` for downstream Matrix users. -/
theorem higham9_11_matrix_banded_growth_factor_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ) (hρ : 0 ≤ ρ_bound)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ ρ_bound * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_11_banded_growth_factor_solve_tight fp n A L_hat U_hat b
      ρ_bound hρ hL_diag hU_diag hLU hn hn3 hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.11**, native Matrix form of the supplied-growth monotone
banded solve wrapper. -/
theorem higham9_11_matrix_banded_growth_factor_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound ρ_target : ℝ)
    (hρ_target : 0 ≤ ρ_target)
    (hρ_le : ρ_bound ≤ ρ_target)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ ρ_target * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_11_banded_growth_factor_solve_tight_of_growth_le fp n
      A L_hat U_hat b ρ_bound ρ_target hρ_target hρ_le
      hL_diag hU_diag hLU hn hn3 hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.11**, native Matrix form of the Bohte banded solve wrapper. -/
theorem higham9_11_matrix_bohte_banded_solve_tight (fp : FPModel) (n p : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        higham9_11_bohteBound p * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_11_bohteBound p * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_11_bohte_banded_solve_tight fp n p A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3 hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.11**, native Matrix form of the Bohte monotone solve wrapper. -/
theorem higham9_11_matrix_bohte_banded_solve_tight_of_growth_le
    (fp : FPModel) (n p : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ higham9_11_bohteBound p)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_11_bohteBound p * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_11_bohte_banded_solve_tight_of_growth_le fp n p
      A L_hat U_hat b ρ_bound hρ_le hL_diag hU_diag hLU hn hn3
      hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.11**, native Matrix form of the Bohte bandwidth-widening solve
wrapper. -/
theorem higham9_11_matrix_bohte_banded_solve_tight_of_bandwidth_le
    (fp : FPModel) (n q p : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hqp : q ≤ p)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        higham9_11_bohteBound q * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_11_bohteBound p * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_11_bohte_banded_solve_tight_of_bandwidth_le fp n q p
      A L_hat U_hat b hqp hL_diag hU_diag hLU hn hn3 hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.11**, native Matrix form of the common-bandwidth Bohte source
wrapper with an explicit structural `IsBanded` hypothesis. -/
theorem higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common
    (fp : FPModel) (n p q r : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hp : p ≤ r) (hq : q ≤ r)
    (hBanded : IsBanded n p q A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        higham9_11_bohteBound r * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_11_bohteBound r * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_11_bohte_banded_solve_tight_of_isBanded_common fp n p q r
      A L_hat U_hat b hp hq hBanded hL_diag hU_diag hLU hn hn3
      hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.11**, native Matrix form of the common-bandwidth Bohte source
wrapper from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common_growth_le
    (fp : FPModel) (n p q r : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hp : p ≤ r) (hq : q ≤ r)
    (hBanded : IsBanded n p q A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ higham9_11_bohteBound r)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_11_bohteBound r * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_11_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n p q r A L_hat U_hat b hp hq hBanded ρ_bound hρ_le
      hL_diag hU_diag hLU hn hn3 hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.11**, bandwidth-one Bohte solve bound.

This is the common-bandwidth alias of the tridiagonal `p = 1` specialization:
the concrete scalar is `2`, and the external banded GEPP growth hypothesis
remains explicit. -/
theorem higham9_11_bandwidth_one_bohte_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_one_formula] using
    higham9_11_bohte_banded_solve_tight fp n 1 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_one_formula] using hGrowth i j)

/-- **Theorem 9.11**, bandwidth-one Bohte solve bound from any smaller
componentwise growth constant.

This is the common-bandwidth `p = 1` specialization of the generic monotone
Bohte consumer: callers may prove a sharper growth estimate and widen it to
the printed tridiagonal constant `2`. -/
theorem higham9_11_bandwidth_one_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 2)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_one_formula] using
    higham9_11_bohte_banded_solve_tight_of_growth_le fp n 1
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_one_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, source-facing bandwidth-one Bohte solve wrapper with
the common-bandwidth structural hypothesis exposed.

This is the `IsBanded n 1 1 A` form of the tridiagonal source case; the GEPP
growth estimate remains the explicit Bohte-side assumption. -/
theorem higham9_11_bandwidth_one_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 1 1 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_tridiagonal] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common fp n 1 1 1
      A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_tridiagonal] using hGrowth i j)

/-- **Theorem 9.11**, source-facing bandwidth-one Bohte solve wrapper from any
smaller componentwise growth constant.

The `IsBanded n 1 1 A` hypothesis records the tridiagonal/bandwidth-one source
shape, while `hρ_le` widens a sharper supplied growth estimate to Bohte's
printed scalar `2`. -/
theorem higham9_11_bandwidth_one_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 1 1 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 2)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_one_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 1 1 1 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_one_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, tridiagonal source-facing Bohte solve wrapper.

For tridiagonal matrices the structural hypothesis is converted to the common
bandwidth-one source condition and the printed Bohte scalar reduces to `2`.
The tridiagonal GEPP growth estimate itself remains explicit. -/
theorem higham9_11_tridiagonal_bohte_solve_tight_of_isTridiagonal
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hA_tridiag : IsTridiagonal n A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  have hBanded : IsBanded n 1 1 A := isBanded_one_one_of_isTridiagonal hA_tridiag
  simpa [higham9_11_bohteBound_tridiagonal] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common fp n 1 1 1
      A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_tridiagonal] using hGrowth i j)

/-- **Theorem 9.11**, tridiagonal source-facing Bohte solve wrapper from any
smaller componentwise growth constant.

This is the `IsTridiagonal` specialization of the bandwidth-one widening
wrapper: the source shape is converted to `IsBanded n 1 1 A`, and a sharper
growth estimate is widened to the printed scalar `2`. -/
theorem higham9_11_tridiagonal_bohte_solve_tight_of_isTridiagonal_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hA_tridiag : IsTridiagonal n A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 2)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  have hBanded : IsBanded n 1 1 A := isBanded_one_one_of_isTridiagonal hA_tridiag
  exact
    higham9_11_bandwidth_one_bohte_solve_tight_of_isBanded_growth_le
      fp n A L_hat U_hat b hBanded ρ_bound hρ_le
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, tridiagonal `p = 1` Bohte solve bound.

This is the printed tridiagonal specialization of
`higham9_11_bohte_banded_solve_tight`: the Bohte scalar expression is reduced
to the concrete constant `2`, while the external GEPP growth hypothesis remains
explicit. -/
theorem higham9_11_tridiagonal_bohte_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_tridiagonal] using
    higham9_11_bohte_banded_solve_tight fp n 1 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_tridiagonal] using hGrowth i j)

/-- **Theorem 9.11**, tridiagonal Bohte solve bound from any smaller
componentwise growth constant.

This source-facing alias exposes the common tridiagonal name while reusing the
bandwidth-one monotone consumer. -/
theorem higham9_11_tridiagonal_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 2)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_11_bandwidth_one_bohte_solve_tight_of_growth_le fp n
    A L_hat U_hat b ρ_bound hρ_le hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-one Bohte solve
bound. -/
theorem higham9_11_matrix_bandwidth_one_bohte_solve_tight
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_one_formula] using
    higham9_11_matrix_bohte_banded_solve_tight fp n 1 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_one_formula] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the bandwidth-one Bohte solve
bound from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_one_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 2)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_one_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_growth_le fp n 1
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_one_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-one Bohte solve
wrapper with the common-bandwidth structural hypothesis exposed. -/
theorem higham9_11_matrix_bandwidth_one_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 1 1 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_tridiagonal] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common
      fp n 1 1 1 A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_tridiagonal] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the bandwidth-one Bohte solve
wrapper from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_one_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 1 1 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 2)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_one_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 1 1 1 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_one_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the tridiagonal Bohte solve
wrapper with an explicit `IsTridiagonal` source hypothesis. -/
theorem higham9_11_matrix_tridiagonal_bohte_solve_tight_of_isTridiagonal
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hA_tridiag : IsTridiagonal n A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have hBanded : IsBanded n 1 1 A := isBanded_one_one_of_isTridiagonal hA_tridiag
  exact
    higham9_11_matrix_bandwidth_one_bohte_solve_tight_of_isBanded
      fp n A L_hat U_hat b hBanded hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the tridiagonal Bohte solve
wrapper from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_tridiagonal_bohte_solve_tight_of_isTridiagonal_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hA_tridiag : IsTridiagonal n A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 2)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have hBanded : IsBanded n 1 1 A := isBanded_one_one_of_isTridiagonal hA_tridiag
  exact
    higham9_11_matrix_bandwidth_one_bohte_solve_tight_of_isBanded_growth_le
      fp n A L_hat U_hat b hBanded ρ_bound hρ_le
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the tridiagonal `p = 1` Bohte
solve bound. -/
theorem higham9_11_matrix_tridiagonal_bohte_solve_tight
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_11_matrix_bandwidth_one_bohte_solve_tight fp n
    A L_hat U_hat b hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the tridiagonal Bohte solve bound
from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_tridiagonal_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 2)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_11_matrix_bandwidth_one_bohte_solve_tight_of_growth_le fp n
    A L_hat U_hat b ρ_bound hρ_le hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, pentadiagonal `p = 2` Bohte solve bound.

This specializes the printed Bohte expression to the concrete scalar `7`.
The external banded GEPP growth hypothesis remains explicit. -/
theorem higham9_11_pentadiagonal_bohte_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        7 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_pentadiagonal_formula] using
    higham9_11_bohte_banded_solve_tight fp n 2 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_pentadiagonal_formula] using hGrowth i j)

/-- **Theorem 9.11**, pentadiagonal Bohte solve bound from any smaller
componentwise growth constant. -/
theorem higham9_11_pentadiagonal_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 7)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_pentadiagonal_formula] using
    higham9_11_bohte_banded_solve_tight_of_growth_le fp n 2
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_pentadiagonal_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, source-facing pentadiagonal Bohte solve wrapper with
the common-bandwidth structural hypothesis exposed.

This is the named pentadiagonal alias of the bandwidth-two structural wrapper;
the GEPP growth estimate remains the explicit Bohte-side assumption. -/
theorem higham9_11_pentadiagonal_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 2 2 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        7 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_pentadiagonal_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common fp n 2 2 2
      A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_pentadiagonal_formula] using hGrowth i j)

/-- **Theorem 9.11**, source-facing pentadiagonal Bohte solve wrapper from
any smaller componentwise growth constant. -/
theorem higham9_11_pentadiagonal_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 2 2 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 7)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_pentadiagonal_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 2 2 2 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_pentadiagonal_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, bandwidth-two Bohte solve bound.

This is the common-bandwidth alias of the pentadiagonal `p = 2` specialization:
the concrete scalar is `7`, and the external banded GEPP growth hypothesis
remains explicit. -/
theorem higham9_11_bandwidth_two_bohte_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        7 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_two_formula] using
    higham9_11_bohte_banded_solve_tight fp n 2 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_two_formula] using hGrowth i j)

/-- **Theorem 9.11**, bandwidth-two Bohte solve bound from any smaller
componentwise growth constant. -/
theorem higham9_11_bandwidth_two_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 7)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_two_formula] using
    higham9_11_bohte_banded_solve_tight_of_growth_le fp n 2
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_two_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, source-facing bandwidth-two Bohte solve wrapper with
the common-bandwidth structural hypothesis exposed.

The structural `IsBanded n 2 2 A` hypothesis records the source band shape;
the GEPP growth estimate remains the explicit Bohte-side assumption. -/
theorem higham9_11_bandwidth_two_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 2 2 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        7 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_two_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common fp n 2 2 2
      A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_two_formula] using hGrowth i j)

/-- **Theorem 9.11**, source-facing bandwidth-two Bohte solve wrapper from
any smaller componentwise growth constant. -/
theorem higham9_11_bandwidth_two_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 2 2 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 7)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_two_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 2 2 2 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_two_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the pentadiagonal Bohte solve
bound. -/
theorem higham9_11_matrix_pentadiagonal_bohte_solve_tight
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        7 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_pentadiagonal_formula] using
    higham9_11_matrix_bohte_banded_solve_tight fp n 2 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_pentadiagonal_formula] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the pentadiagonal Bohte solve
bound from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_pentadiagonal_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 7)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_pentadiagonal_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_growth_le fp n 2
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_pentadiagonal_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the pentadiagonal Bohte solve
wrapper with the common-bandwidth structural hypothesis exposed. -/
theorem higham9_11_matrix_pentadiagonal_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 2 2 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        7 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_pentadiagonal_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common
      fp n 2 2 2 A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_pentadiagonal_formula] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the pentadiagonal Bohte solve
wrapper from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_pentadiagonal_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 2 2 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 7)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_pentadiagonal_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 2 2 2 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_pentadiagonal_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-two Bohte solve
bound. -/
theorem higham9_11_matrix_bandwidth_two_bohte_solve_tight
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        7 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_11_matrix_pentadiagonal_bohte_solve_tight fp n
    A L_hat U_hat b hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-two Bohte solve
bound from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_two_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 7)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_11_matrix_pentadiagonal_bohte_solve_tight_of_growth_le fp n
    A L_hat U_hat b ρ_bound hρ_le hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-two Bohte solve
wrapper with the common-bandwidth structural hypothesis exposed. -/
theorem higham9_11_matrix_bandwidth_two_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 2 2 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        7 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_11_matrix_pentadiagonal_bohte_solve_tight_of_isBanded fp n
    A L_hat U_hat b hBanded hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-two Bohte solve
wrapper from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_two_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 2 2 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 7)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        7 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_11_matrix_pentadiagonal_bohte_solve_tight_of_isBanded_growth_le fp n
    A L_hat U_hat b hBanded ρ_bound hρ_le hL_diag hU_diag hLU hn hn3
    hGrowth

/-- **Theorem 9.11**, bandwidth-three Bohte solve bound.

This specializes the printed Bohte expression to the concrete scalar `28`.
The external banded GEPP growth hypothesis remains explicit. -/
theorem higham9_11_bandwidth_three_bohte_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        28 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        28 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_three_formula] using
    higham9_11_bohte_banded_solve_tight fp n 3 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_three_formula] using hGrowth i j)

/-- **Theorem 9.11**, bandwidth-three Bohte solve bound from any smaller
componentwise growth constant. -/
theorem higham9_11_bandwidth_three_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 28)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        28 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_three_formula] using
    higham9_11_bohte_banded_solve_tight_of_growth_le fp n 3
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_three_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, source-facing bandwidth-three Bohte solve wrapper with
the common-bandwidth structural hypothesis exposed. -/
theorem higham9_11_bandwidth_three_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 3 3 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        28 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        28 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_three_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common fp n 3 3 3
      A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_three_formula] using hGrowth i j)

/-- **Theorem 9.11**, source-facing bandwidth-three Bohte solve wrapper from
any smaller componentwise growth constant. -/
theorem higham9_11_bandwidth_three_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 3 3 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 28)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        28 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_three_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 3 3 3 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_three_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, bandwidth-four Bohte solve bound for the source's
printed `p = 4`, `n = 9` scalar example.

This reduces Bohte's expression to the concrete scalar `116`; the pivot-trace
attainability and the external banded GEPP growth theorem remain separate. -/
theorem higham9_11_bandwidth_four_bohte_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        116 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        116 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_four_formula] using
    higham9_11_bohte_banded_solve_tight fp n 4 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_four_formula] using hGrowth i j)

/-- **Theorem 9.11**, bandwidth-four Bohte solve bound from any smaller
componentwise growth constant. -/
theorem higham9_11_bandwidth_four_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 116)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        116 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_four_formula] using
    higham9_11_bohte_banded_solve_tight_of_growth_le fp n 4
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_four_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, source-facing bandwidth-four Bohte solve wrapper with
the common-bandwidth structural hypothesis exposed. -/
theorem higham9_11_bandwidth_four_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 4 4 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        116 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        116 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_four_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common fp n 4 4 4
      A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_four_formula] using hGrowth i j)

/-- **Theorem 9.11**, source-facing bandwidth-four Bohte solve wrapper from
any smaller componentwise growth constant. -/
theorem higham9_11_bandwidth_four_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 4 4 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 116)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        116 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_four_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 4 4 4 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_four_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, bandwidth-five Bohte solve bound.

This specializes the printed Bohte expression to the concrete scalar `480`.
The external banded GEPP growth hypothesis remains explicit. -/
theorem higham9_11_bandwidth_five_bohte_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        480 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        480 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_five_formula] using
    higham9_11_bohte_banded_solve_tight fp n 5 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_five_formula] using hGrowth i j)

/-- **Theorem 9.11**, bandwidth-five Bohte solve bound from any smaller
componentwise growth constant. -/
theorem higham9_11_bandwidth_five_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 480)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        480 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_five_formula] using
    higham9_11_bohte_banded_solve_tight_of_growth_le fp n 5
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_five_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, source-facing bandwidth-five Bohte solve wrapper with
the common-bandwidth structural hypothesis exposed. -/
theorem higham9_11_bandwidth_five_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 5 5 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        480 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        480 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_five_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common fp n 5 5 5
      A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_five_formula] using hGrowth i j)

/-- **Theorem 9.11**, source-facing bandwidth-five Bohte solve wrapper from
any smaller componentwise growth constant. -/
theorem higham9_11_bandwidth_five_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 5 5 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 480)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        480 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  simpa [higham9_11_bohteBound_bandwidth_five_formula] using
    higham9_11_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 5 5 5 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_five_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-three Bohte solve
bound. -/
theorem higham9_11_matrix_bandwidth_three_bohte_solve_tight
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        28 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        28 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_three_formula] using
    higham9_11_matrix_bohte_banded_solve_tight fp n 3 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_three_formula] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the bandwidth-three Bohte solve
bound from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_three_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 28)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        28 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_three_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_growth_le fp n 3
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_three_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-three Bohte solve
wrapper with the common-bandwidth structural hypothesis exposed. -/
theorem higham9_11_matrix_bandwidth_three_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 3 3 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        28 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        28 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_three_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common
      fp n 3 3 3 A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_three_formula] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the bandwidth-three Bohte solve
wrapper from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_three_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 3 3 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 28)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        28 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_three_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 3 3 3 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_three_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-four Bohte solve
bound. -/
theorem higham9_11_matrix_bandwidth_four_bohte_solve_tight
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        116 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        116 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_four_formula] using
    higham9_11_matrix_bohte_banded_solve_tight fp n 4 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_four_formula] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the bandwidth-four Bohte solve
bound from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_four_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 116)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        116 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_four_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_growth_le fp n 4
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_four_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-four Bohte solve
wrapper with the common-bandwidth structural hypothesis exposed. -/
theorem higham9_11_matrix_bandwidth_four_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 4 4 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        116 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        116 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_four_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common
      fp n 4 4 4 A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_four_formula] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the bandwidth-four Bohte solve
wrapper from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_four_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 4 4 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 116)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        116 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_four_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 4 4 4 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_four_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-five Bohte solve
bound. -/
theorem higham9_11_matrix_bandwidth_five_bohte_solve_tight
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        480 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        480 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_five_formula] using
    higham9_11_matrix_bohte_banded_solve_tight fp n 5 A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_five_formula] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the bandwidth-five Bohte solve
bound from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_five_bohte_solve_tight_of_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 480)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        480 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_five_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_growth_le fp n 5
      A L_hat U_hat b ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_five_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, native Matrix form of the bandwidth-five Bohte solve
wrapper with the common-bandwidth structural hypothesis exposed. -/
theorem higham9_11_matrix_bandwidth_five_bohte_solve_tight_of_isBanded
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 5 5 A)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        480 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        480 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_five_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common
      fp n 5 5 5 A L_hat U_hat b (by omega) (by omega) hBanded
      hL_diag hU_diag hLU hn hn3
      (fun i j => by
        simpa [higham9_11_bohteBound_bandwidth_five_formula] using hGrowth i j)

/-- **Theorem 9.11**, native Matrix form of the bandwidth-five Bohte solve
wrapper from any smaller componentwise growth constant. -/
theorem higham9_11_matrix_bandwidth_five_bohte_solve_tight_of_isBanded_growth_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hBanded : IsBanded n 5 5 A)
    (ρ_bound : ℝ)
    (hρ_le : ρ_bound ≤ 480)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        480 * gamma fp (3 * n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [higham9_11_bohteBound_bandwidth_five_formula] using
    higham9_11_matrix_bohte_banded_solve_tight_of_isBanded_common_growth_le
      fp n 5 5 5 A L_hat U_hat b (by omega) (by omega) hBanded
      ρ_bound
      (by simpa [higham9_11_bohteBound_bandwidth_five_formula] using hρ_le)
      hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.12(a)**, SPD optimal-growth backward-error form once the
SPD growth inequality has been supplied. -/
theorem higham9_12_spd_lu_backward_error (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  spd_lu_backward_error n A L_hat U_hat ε hε hSPD hLU hGrowth

end NumStability
