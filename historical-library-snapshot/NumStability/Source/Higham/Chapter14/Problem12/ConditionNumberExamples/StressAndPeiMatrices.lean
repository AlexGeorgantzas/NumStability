import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter14.Equation34.DeterminantFromLU.MatrixInversion
import NumStability.Source.Higham.Chapter14.Equation35.HymanBlockFactorization.MatrixInversion
import NumStability.Source.Higham.Chapter14.Equation36.HymanDeterminant.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem03.ResidualComparison.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem04.ResidualCounterexample.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem07.OnesVector.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem08.ComplexInverseRealBlock.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem10.EntryPerturbation.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem11.HadamardCondition.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem12.HadamardExamples.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem13.GEJBound.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem14.HymanDeterminant.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem15.DeterminantPerturbation.MatrixInversion
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2B.MatrixInversion
import NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodD.MatrixInversion

/-!
# StressAndPeiMatrices

Canonical destination for the Chapter14.Problem12 declarations relocated from the
historical path `NumStability.Algorithms.MatrixInversion` during wave R08.
Holds 13 declaration(s): 4 public and 9 authored-private.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

private lemma higham14_problem14_12_prod_nat_sub_eq_factorial (n : ℕ) :
    (∏ i ∈ Finset.range n, (n - i)) = Nat.factorial n := by
  calc
    (∏ i ∈ Finset.range n, (n - i))
        = ∏ i ∈ Finset.range n, ((n - 1 - i) + 1) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hi_lt : i < n := Finset.mem_range.mp hi
            omega
    _ = ∏ i ∈ Finset.range n, (i + 1) := by
            rw [Finset.prod_range_reflect (fun i : ℕ => i + 1) n]
    _ = Nat.factorial n := by
            rw [Finset.prod_range_add_one_eq_factorial]

private lemma higham14_problem14_12_prod_fin_nat_sub_eq_factorial (n : ℕ) :
    (∏ i : Fin n, (n - i.val)) = Nat.factorial n := by
  rw [Fin.prod_univ_eq_prod_range]
  exact higham14_problem14_12_prod_nat_sub_eq_factorial n

private lemma higham14_problem14_12_stressUpper_one_upper (n : ℕ) :
    (show Matrix (Fin n) (Fin n) ℝ from higham8_3_stressUpper n 1).BlockTriangular id := by
  intro i j hji
  have hv : j.val < i.val := by simpa using hji
  have hij : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl i.val) hv
  have hnot : ¬ i.val < j.val := by omega
  simp [higham8_3_stressUpper, hij, hnot]

private lemma higham14_problem14_12_det_stressUpper_one (n : ℕ) :
    Matrix.det (higham8_3_stressUpper n 1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  rw [Matrix.det_of_upperTriangular (higham14_problem14_12_stressUpper_one_upper n)]
  simp [higham8_3_stressUpper]

private lemma higham14_problem14_12_sum_tail_one (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, if i.val ≤ j.val then (1 : ℝ) else 0) =
      (n - i.val : ℝ) := by
  have hlt :
      (Finset.univ.filter (fun j : Fin n => j.val < i.val)).card = i.val := by
    simpa [Nat.min_eq_right (Nat.le_of_lt i.isLt)] using
      (Fin.card_filter_val_lt (n := n) (m := i.val))
  have hpart :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun j : Fin n => j.val < i.val)
  have htail :
      (Finset.univ.filter (fun j : Fin n => ¬ j.val < i.val)).card = n - i.val := by
    rw [Finset.card_univ, Fintype.card_fin] at hpart
    omega
  have htail' :
      (Finset.univ.filter (fun j : Fin n => i.val ≤ j.val)).card = n - i.val := by
    simpa only [not_lt] using htail
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [htail']
  exact Nat.cast_sub (Nat.le_of_lt i.isLt)

private lemma higham14_problem14_12_rowNorm2_sq_stressUpper_one
    (n : ℕ) (i : Fin n) :
    higham14_rowNorm2 (higham8_3_stressUpper n 1) i ^ 2 =
      (n - i.val : ℝ) := by
  rw [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
  have hsquare : ∀ j : Fin n,
      higham8_3_stressUpper n 1 i j ^ 2 =
        if i.val ≤ j.val then (1 : ℝ) else 0 := by
    intro j
    by_cases hle : i.val ≤ j.val
    · by_cases hij : i = j
      · subst j
        simp [higham8_3_stressUpper]
      · have hlt : i.val < j.val := by
          exact lt_of_le_of_ne hle (by
            intro hval
            exact hij (Fin.ext hval))
        simp [higham8_3_stressUpper, hij, hlt, hle]
    · have hij : i ≠ j := by
        intro h
        subst j
        exact hle (le_refl i.val)
      have hnotlt : ¬ i.val < j.val := by omega
      simp [higham8_3_stressUpper, hij, hnotlt, hle]
  simp_rw [hsquare]
  rw [higham14_problem14_12_sum_tail_one n i]

private lemma higham14_problem14_12_rowNorm2_stressUpper_one
    (n : ℕ) (i : Fin n) :
    higham14_rowNorm2 (higham8_3_stressUpper n 1) i =
      Real.sqrt ((n - i.val : ℕ) : ℝ) := by
  exact
    (sq_eq_sq₀
      (higham14_rowNorm2_nonneg (higham8_3_stressUpper n 1) i)
      (Real.sqrt_nonneg _)).mp (by
        rw [higham14_problem14_12_rowNorm2_sq_stressUpper_one n i,
          Real.sq_sqrt (Nat.cast_nonneg _)]
        exact (Nat.cast_sub (Nat.le_of_lt i.isLt)).symm)

private lemma higham14_problem14_12_prod_rowNorm2_stressUpper_one (n : ℕ) :
    (∏ i : Fin n, higham14_rowNorm2 (higham8_3_stressUpper n 1) i) =
      Real.sqrt (Nat.factorial n : ℝ) := by
  calc
    (∏ i : Fin n, higham14_rowNorm2 (higham8_3_stressUpper n 1) i)
        = ∏ i : Fin n, Real.sqrt ((n - i.val : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro i _
            exact higham14_problem14_12_rowNorm2_stressUpper_one n i
    _ = Real.sqrt (∏ i : Fin n, ((n - i.val : ℕ) : ℝ)) := by
            exact (Real.sqrt_prod Finset.univ
              (fun i _ => Nat.cast_nonneg (n - i.val))).symm
    _ = Real.sqrt (Nat.factorial n : ℝ) := by
            have hprod :
                (∏ i : Fin n, ((n - i.val : ℕ) : ℝ)) =
                  (Nat.factorial n : ℝ) := by
              exact_mod_cast higham14_problem14_12_prod_fin_nat_sub_eq_factorial n
            rw [hprod]

/-- Higham, 2nd ed., Appendix A, Problem 14.12(b), printed p.560:
    for the Chapter 8 stress matrix `U(1)`, the Hadamard determinant condition
    number is `sqrt(n!)`.  Lean indexes rows as `0, ..., n-1`, so row `i` has
    `n - i` unit entries. -/
theorem higham14_problem14_12_hadamardConditionNumber_stressUpper_one_eq_sqrt_factorial
    (n : ℕ) :
    higham14_hadamardConditionNumber (higham8_3_stressUpper n 1) =
      Real.sqrt (Nat.factorial n : ℝ) := by
  unfold higham14_hadamardConditionNumber
  rw [higham14_problem14_12_prod_rowNorm2_stressUpper_one n,
    higham14_problem14_12_det_stressUpper_one n]
  norm_num

private lemma higham14_problem14_12_peiMatrix_eq_smul_one_add_rankOne
    (n : ℕ) (α : ℝ) (hα : α - 1 ≠ 0) :
    (higham14_peiMatrix n α : Matrix (Fin n) (Fin n) ℝ) =
      (α - 1) •
        (1 + Matrix.replicateCol Unit (fun _ : Fin n => (α - 1)⁻¹) *
          Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ))) := by
  funext i j
  change (if i = j then α else 1) =
    (α - 1) *
      (((1 : Matrix (Fin n) (Fin n) ℝ) +
        Matrix.replicateCol Unit (fun _ : Fin n => (α - 1)⁻¹) *
          Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ))) i j)
  by_cases hij : i = j
  · subst j
    simp [Matrix.add_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    field_simp [hα]
    ring
  · simp [hij, Matrix.add_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    field_simp [hα]

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), dependency:
    determinant of the Pei matrix `(alpha - 1) I + e e^T`. -/
lemma higham14_problem14_12_peiMatrix_det
    (n : ℕ) (α : ℝ) (hn : 0 < n) (hα : α - 1 ≠ 0) :
    Matrix.det (higham14_peiMatrix n α : Matrix (Fin n) (Fin n) ℝ) =
      ((n : ℝ) + α - 1) * (α - 1) ^ (n - 1) := by
  let β : ℝ := α - 1
  have hβ : β ≠ 0 := by simpa [β] using hα
  let M : Matrix (Fin n) (Fin n) ℝ :=
    1 + Matrix.replicateCol Unit (fun _ : Fin n => β⁻¹) *
      Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ))
  have hmatrix :
      (higham14_peiMatrix n α : Matrix (Fin n) (Fin n) ℝ) = β • M := by
    dsimp [M, β]
    exact higham14_problem14_12_peiMatrix_eq_smul_one_add_rankOne n α hα
  rw [hmatrix]
  change Matrix.det (β • M) = ((n : ℝ) + α - 1) * (α - 1) ^ (n - 1)
  rw [Matrix.det_smul]
  rw [Fintype.card_fin]
  have hdetM : Matrix.det M = 1 + (n : ℝ) * β⁻¹ := by
    dsimp [M]
    rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct, Finset.sum_const, Fintype.card_fin]
  rw [hdetM]
  have hn_eq : n = (n - 1) + 1 := by omega
  rw [hn_eq, pow_succ]
  dsimp [β]
  field_simp [hα]
  ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b):
    Pei-matrix Hadamard condition-number formula in the nonnegative
    `|det(A)|` denominator convention used by `higham14_hadamardConditionNumber`. -/
theorem higham14_problem14_12_hadamardConditionNumber_peiMatrix_abs
    (n : ℕ) (α : ℝ) (hn : 0 < n) (hα : α - 1 ≠ 0) :
    higham14_hadamardConditionNumber (higham14_peiMatrix n α) =
      (Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ))) ^ n /
        |((n : ℝ) + α - 1) * (α - 1) ^ (n - 1)| := by
  unfold higham14_hadamardConditionNumber
  rw [higham14_problem14_12_peiMatrix_prod_rowNorm2,
    higham14_problem14_12_peiMatrix_det n α hn hα]

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), Appendix A:
    for the Pei matrix `A = (alpha - 1) I + e e^T` with `alpha > 1`,
    `psi(A) = (sqrt(alpha^2 + n - 1))^n /
      ((n + alpha - 1) * (alpha - 1)^(n - 1))`. -/
theorem higham14_problem14_12_hadamardConditionNumber_peiMatrix
    (n : ℕ) (α : ℝ) (hn : 0 < n) (hα : 1 < α) :
    higham14_hadamardConditionNumber (higham14_peiMatrix n α) =
      (Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ))) ^ n /
        (((n : ℝ) + α - 1) * (α - 1) ^ (n - 1)) := by
  have hαsub_pos : 0 < α - 1 := by linarith
  have hαne : α - 1 ≠ 0 := ne_of_gt hαsub_pos
  have hden_pos : 0 < ((n : ℝ) + α - 1) * (α - 1) ^ (n - 1) := by
    have hfirst : 0 < (n : ℝ) + α - 1 := by
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact mul_pos hfirst (pow_pos hαsub_pos _)
  rw [higham14_problem14_12_hadamardConditionNumber_peiMatrix_abs n α hn hαne,
    abs_of_pos hden_pos]

end NumStability
