import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Pascal.Basic

/-!
# NumStability Analysis TestMatrices Pascal Exact

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Exact` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

/-- The transposed Pascal Cholesky factor acts injectively.  This is derived
from the already proved two-sided inverse of `pascalMatrix`, rather than from
an assumed spectral property. -/
theorem pascalLowerTranspose_mulVec_injective (n : ℕ) :
    Function.Injective ((pascalLower n).transpose).mulVec := by
  intro x y hxy
  have hP : (pascalMatrix n).mulVec x = (pascalMatrix n).mulVec y := by
    rw [pascalMatrix_eq_lower_mul_transpose]
    simpa [Matrix.mulVec_mulVec] using
      congrArg (fun v => (pascalLower n).mulVec v) hxy
  have h := congrArg
    (fun v => ((signedPascal n).transpose * signedPascal n).mulVec v) hP
  simpa [Matrix.mulVec_mulVec, signedGram_mul_pascalMatrix] using h

/-- The Pascal quadratic form is the squared Euclidean norm of the transposed
lower Pascal factor applied to the vector. -/
theorem pascalMatrix_quadratic_eq_sum_sq
    (n : ℕ) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, x i * pascalMatrix n i j * x j) =
      ∑ k : Fin n, (((pascalLower n).transpose).mulVec x k) ^ 2 := by
  rw [pascalMatrix_eq_lower_mul_transpose]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        x i * (pascalLower n i k * pascalLower n j k) * x j) =
      ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
        x i * (pascalLower n i k * pascalLower n j k) * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        x i * (pascalLower n i k * pascalLower n j k) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ((fun j => pascalLower n j k) ⬝ᵥ x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The Pascal quadratic form is strictly positive on every nonzero vector. -/
theorem pascalMatrix_quadratic_pos
    (n : ℕ) (x : Fin n → ℝ) (hx : ∃ i, x i ≠ 0) :
    0 < ∑ i : Fin n, ∑ j : Fin n, x i * pascalMatrix n i j * x j := by
  rw [pascalMatrix_quadratic_eq_sum_sq]
  have hx0 : x ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hx
    exact hi (congrFun h i)
  have hy0 : ((pascalLower n).transpose).mulVec x ≠ 0 := by
    intro h
    exact hx0 ((pascalLowerTranspose_mulVec_injective n)
      (h.trans (Matrix.mulVec_zero _).symm))
  have hy : ∃ i, ((pascalLower n).transpose).mulVec x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy0 (funext h)
  obtain ⟨i, hi⟩ := hy
  refine Finset.sum_pos' (fun k _ => sq_nonneg _) ?_
  exact ⟨i, Finset.mem_univ i,
    (sq_nonneg (((pascalLower n).transpose).mulVec x i)).lt_of_ne
      (Ne.symm (pow_ne_zero 2 hi))⟩

/-- Section 28.4's Pascal SPD claim on the repository's explicit real
quadratic-form surface. -/
theorem pascalMatrix_isSymPosDef_explicit (n : ℕ) :
    (∀ i j : Fin n, pascalMatrix n i j = pascalMatrix n j i) ∧
      ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        0 < ∑ i : Fin n, ∑ j : Fin n,
          x i * pascalMatrix n i j * x j := by
  constructor
  · intro i j
    have h := congrArg (fun M : RSqMat n => M i j) (pascalMatrix_transpose n)
    simpa [Matrix.transpose_apply] using h.symm
  · exact pascalMatrix_quadratic_pos n

end NumStability
