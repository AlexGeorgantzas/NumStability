-- NumStability/Source/Higham/Chapter07/Equation17/KahanConditioningExample.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Analysis.HighamChapter7`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import NumStability.Algorithms.CondEstimation
import NumStability.Analysis.Asymptotics.Bounds
import NumStability.Analysis.Conditioning.DistanceToSingularity
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.Conditioning.LinearSystems.SubordinatePerturbation
import NumStability.Analysis.MatrixNorms.SpectralRadius
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Summation.Signs
import NumStability.Source.Higham.Chapter06.Problem05
import NumStability.Source.Higham.Chapter07.Equation26.DistanceToSingularity.Results
import NumStability.Source.Higham.Chapter07.Corollary06.LinearSystemsConditioning.Basic
import NumStability.Source.Higham.Chapter07.Corollary06.LinearSystemsConditioning.Results
import NumStability.Source.Higham.Chapter07.Equation25.InverseConditioning.ExactPerturbation
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ComputedResidual
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Equation05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Equation32
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Equation33
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ForwardErrorKernels
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Lemma09
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem02
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem04
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem06Columnwise
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem06Rowwise
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem07
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem08RectangularBackwardError
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Exact
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Linearized
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part02
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part03
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10OneNorm
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem13SparseResidual
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem15Hadamard
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.RowScaling
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem02
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem04
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part02
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part03
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part04
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part06
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem07FrobeniusScaling
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem08Aliases

/-!
# KahanConditioningExample

Relocated from `NumStability.Analysis.HighamChapter7` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


-- Analysis/HighamChapter7.lean
--
-- Source-facing wrappers for Higham Chapter 7.
--
-- The heavy perturbation arguments live in `PerturbationTheory.lean`; this file
-- records Chapter 7 statements whose exact source shape is a relative
-- infinity-norm or practical-error corollary of those componentwise results.

















namespace NumStability

open scoped BigOperators

private theorem ch7_kahan_solution (ε : ℝ) :
    matMulVec 3 (ch7KahanMatrix ε) (ch7KahanSolution ε) = ch7KahanRhs ε := by
  ext i
  fin_cases i <;>
    simp [matMulVec, ch7KahanMatrix, ch7KahanSolution, ch7KahanRhs,
      Fin.sum_univ_three] <;> ring


private theorem ch7_kahan_inverse (ε : ℝ) (hε : 0 < ε) :
    IsInverse 3 (ch7KahanMatrix ε) (ch7KahanInverse ε) := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [ch7KahanMatrix, ch7KahanInverse, Fin.sum_univ_three] <;>
    field_simp <;> ring


private theorem ch7_kahan_abs_inverse_mul_abs_matrix
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    matMul 3 (absMatrix 3 (ch7KahanInverse ε))
        (absMatrix 3 (ch7KahanMatrix ε)) =
      ch7KahanAbsInverseMulAbsMatrix ε := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  have h1 : 0 ≤ 1 - 2 * ε := by linarith
  have h2 : 0 ≤ 2 * ε + 1 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matMul, absMatrix, ch7KahanMatrix, ch7KahanInverse,
      ch7KahanAbsInverseMulAbsMatrix, Fin.sum_univ_three,
      abs_of_nonneg hε0, abs_of_nonneg h1, abs_of_nonneg h2,
      abs_div, abs_mul] <;>
    field_simp <;> ring


private theorem ch7_kahan_matrix_infNorm
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    infNorm (ch7KahanMatrix ε) = 4 := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;>
        simp [ch7KahanMatrix, Fin.sum_univ_three, abs_of_nonneg hε0] <;>
        linarith
    · norm_num
  · have h := row_sum_le_infNorm (ch7KahanMatrix ε) (0 : Fin 3)
    simp [ch7KahanMatrix, Fin.sum_univ_three,
      show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide] at h
    norm_num at h
    exact h


private theorem ch7_kahan_inverse_infNorm
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    infNorm (ch7KahanInverse ε) = (1 + ε) / (2 * ε) := by
  have h1 : 0 ≤ 1 - 2 * ε := by linarith
  have h2 : 0 ≤ 2 * ε + 1 := by positivity
  have hden : 0 ≤ 4 * ε := by positivity
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;>
        simp [ch7KahanInverse, Fin.sum_univ_three,
          abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg hden,
          abs_div] <;>
        field_simp <;> nlinarith
    · positivity
  · have h := row_sum_le_infNorm (ch7KahanInverse ε) (1 : Fin 3)
    simp [ch7KahanInverse, Fin.sum_univ_three,
      abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg hden,
      abs_div] at h
    field_simp at h ⊢
    nlinarith


private theorem ch7_kahan_kappaInf
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    kappaInf 3 (by norm_num) (ch7KahanMatrix ε) (ch7KahanInverse ε) =
      2 * (1 + ε⁻¹) := by
  rw [kappaInf_eq_infNorm_mul_infNorm,
    ch7_kahan_matrix_infNorm ε hε hεhalf,
    ch7_kahan_inverse_infNorm ε hε hεhalf]
  field_simp
  ring


private theorem ch7_kahan_condSkeel
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    condSkeel 3 (by norm_num) (ch7KahanMatrix ε) (ch7KahanInverse ε) =
      3 + (2 * ε)⁻¹ := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  have h1 : 0 ≤ 1 - 2 * ε := by linarith
  have h2 : 0 ≤ 2 * ε + 1 := by positivity
  have hden : 0 ≤ 4 * ε := by positivity
  unfold condSkeel
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    fin_cases i <;>
      simp [ch7KahanMatrix, ch7KahanInverse, Fin.sum_univ_three,
        abs_of_nonneg hε0, abs_of_nonneg h1, abs_of_nonneg h2,
        abs_of_nonneg hden, abs_div] <;>
      field_simp <;> nlinarith
  · have h := Finset.le_sup'
        (fun i : Fin 3 =>
          ∑ j : Fin 3, |ch7KahanInverse ε i j| *
            ∑ k : Fin 3, |ch7KahanMatrix ε j k|)
        (Finset.mem_univ (1 : Fin 3))
    have hrow :
        (∑ j : Fin 3, |ch7KahanInverse ε (1 : Fin 3) j| *
          ∑ k : Fin 3, |ch7KahanMatrix ε j k|) =
            3 + (2 * ε)⁻¹ := by
      simp [ch7KahanMatrix, ch7KahanInverse, Fin.sum_univ_three,
        abs_of_nonneg hε0, abs_of_nonneg h1, abs_of_nonneg h2,
        abs_of_nonneg hden, abs_div]
      field_simp
      ring
    rw [hrow] at h
    exact h


private theorem ch7_kahan_solution_infNorm
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    infNormVec (ch7KahanSolution ε) = 1 := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;>
        simp [ch7KahanSolution, abs_of_nonneg hε0] <;> linarith
    · norm_num
  · have h := abs_le_infNormVec (ch7KahanSolution ε) (1 : Fin 3)
    simpa [ch7KahanSolution] using h


private theorem ch7_kahan_cond_at_solution
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ch7SkeelCondAtSolutionInf 3 (by norm_num)
      (ch7KahanMatrix ε) (ch7KahanInverse ε) (ch7KahanSolution ε) =
        5 / 2 + ε := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  have h1 : 0 ≤ 1 - 2 * ε := by linarith
  have h2 : 0 ≤ 2 * ε + 1 := by positivity
  have hden : 0 ≤ 4 * ε := by positivity
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
  rw [ch7_kahan_solution_infNorm ε hε hεhalf, div_one]
  unfold ch7ForwardBoundEF
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    fin_cases i <;>
      simp [ch7AmplifiedRhsEF, ch7KahanMatrix, ch7KahanInverse,
        ch7KahanSolution, Fin.sum_univ_three, abs_of_nonneg hε0,
        abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg hden,
        abs_div] <;>
      field_simp <;> nlinarith
  · have h := Finset.le_sup'
        (ch7AmplifiedRhsEF 3 (ch7KahanInverse ε)
          (fun i j => |ch7KahanMatrix ε i j|) (fun _ => 0)
          (ch7KahanSolution ε))
        (Finset.mem_univ (1 : Fin 3))
    have hrow :
        ch7AmplifiedRhsEF 3 (ch7KahanInverse ε)
          (fun i j => |ch7KahanMatrix ε i j|) (fun _ => 0)
          (ch7KahanSolution ε) (1 : Fin 3) = 5 / 2 + ε := by
      simp [ch7AmplifiedRhsEF, ch7KahanMatrix, ch7KahanInverse,
        ch7KahanSolution, Fin.sum_univ_three, abs_of_nonneg hε0,
        abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg hden,
        abs_div]
      field_simp
      ring
    rw [hrow] at h
    exact h


/-- Equation (7.17), Kahan's exact symbolic example.  The source assumption
`0 < ε ≪ 1` is represented by the explicit sufficient range
`0 < ε ≤ 1/2`.  In this range the displayed matrix and right-hand side have
the stated exact solution; the supplied inverse produces the printed
`|A⁻¹||A|`; and the three condition numbers have the source values
`κ∞(A) = 2(1 + ε⁻¹)`, `cond(A) = 3 + (2ε)⁻¹`, and
`cond(A,x) = 5/2 + ε`.  The final strict chain is the precise content behind
the source's qualitative contrast. -/
theorem eq_7_17_kahan_symbolic_example
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    matMulVec 3 (ch7KahanMatrix ε) (ch7KahanSolution ε) = ch7KahanRhs ε ∧
    IsInverse 3 (ch7KahanMatrix ε) (ch7KahanInverse ε) ∧
    kappaInf 3 (by norm_num) (ch7KahanMatrix ε) (ch7KahanInverse ε) =
      2 * (1 + ε⁻¹) ∧
    matMul 3 (absMatrix 3 (ch7KahanInverse ε))
        (absMatrix 3 (ch7KahanMatrix ε)) =
      ch7KahanAbsInverseMulAbsMatrix ε ∧
    condSkeel 3 (by norm_num) (ch7KahanMatrix ε) (ch7KahanInverse ε) =
      3 + (2 * ε)⁻¹ ∧
    ch7SkeelCondAtSolutionInf 3 (by norm_num)
        (ch7KahanMatrix ε) (ch7KahanInverse ε) (ch7KahanSolution ε) =
      5 / 2 + ε ∧
    ch7SkeelCondAtSolutionInf 3 (by norm_num)
        (ch7KahanMatrix ε) (ch7KahanInverse ε) (ch7KahanSolution ε) <
      condSkeel 3 (by norm_num) (ch7KahanMatrix ε) (ch7KahanInverse ε) ∧
    condSkeel 3 (by norm_num) (ch7KahanMatrix ε) (ch7KahanInverse ε) <
      kappaInf 3 (by norm_num) (ch7KahanMatrix ε) (ch7KahanInverse ε) := by
  have hkappa := ch7_kahan_kappaInf ε hε hεhalf
  have hcond := ch7_kahan_condSkeel ε hε hεhalf
  have hcondx := ch7_kahan_cond_at_solution ε hε hεhalf
  refine ⟨ch7_kahan_solution ε, ch7_kahan_inverse ε hε, hkappa,
    ch7_kahan_abs_inverse_mul_abs_matrix ε hε hεhalf, hcond, hcondx, ?_, ?_⟩
  · rw [hcondx, hcond]
    field_simp
    nlinarith
  · rw [hcond, hkappa]
    field_simp
    nlinarith

end NumStability
