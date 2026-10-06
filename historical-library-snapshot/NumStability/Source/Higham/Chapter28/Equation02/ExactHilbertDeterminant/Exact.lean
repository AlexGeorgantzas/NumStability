import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Analysis.TestMatrices.Hilbert.Exact
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Basic
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Exact

/-!
# Chapter28 Equation02 ExactHilbertDeterminant Exact

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Exact` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

/-- Higham equation (28.2), exact generic determinant formula. -/
theorem hilbert_det_formula (n : ℕ) :
    Matrix.det (hilbertMatrix n) = hilbertDetFormula n := by
  rw [hilbertMatrix_eq_choleskyGram, Matrix.det_mul, Matrix.det_transpose,
    hilbertCholeskyFactor_det]
  rw [← pow_two]
  rw [Fin.prod_univ_eq_prod_range (fun i => hilbertRNat i i) n]
  rw [← Finset.prod_pow]
  exact hilbert_diag_sq_product_nat n

theorem hilbertMatrix_quadratic_eq_sum_sq
    (n : ℕ) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, x i * hilbertMatrix n i j * x j) =
      ∑ k : Fin n, ((hilbertCholeskyFactor n).mulVec x k) ^ 2 := by
  rw [hilbertMatrix_eq_choleskyGram]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        x i * (hilbertCholeskyFactor n k i * hilbertCholeskyFactor n k j) * x j) =
      ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
        x i * (hilbertCholeskyFactor n k i * hilbertCholeskyFactor n k j) * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        x i * (hilbertCholeskyFactor n k i * hilbertCholeskyFactor n k j) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ((fun j => hilbertCholeskyFactor n k j) ⬝ᵥ x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The Hilbert quadratic form is strictly positive on every nonzero vector. -/
theorem hilbertMatrix_quadratic_pos
    (n : ℕ) (x : Fin n → ℝ) (hx : ∃ i, x i ≠ 0) :
    0 < ∑ i : Fin n, ∑ j : Fin n, x i * hilbertMatrix n i j * x j := by
  rw [hilbertMatrix_quadratic_eq_sum_sq]
  have hx0 : x ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hx
    exact hi (congrFun h i)
  have hy0 : (hilbertCholeskyFactor n).mulVec x ≠ 0 := by
    intro h
    exact hx0 ((hilbertCholeskyFactor_mulVec_injective n)
      (h.trans (Matrix.mulVec_zero _).symm))
  have hy : ∃ i, (hilbertCholeskyFactor n).mulVec x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy0 (funext h)
  obtain ⟨i, hi⟩ := hy
  refine Finset.sum_pos' (fun k _ => sq_nonneg _) ?_
  exact ⟨i, Finset.mem_univ i,
    (sq_nonneg ((hilbertCholeskyFactor n).mulVec x i)).lt_of_ne
      (Ne.symm (pow_ne_zero 2 hi))⟩

/-- Section 28.1's SPD claim, in the repository's explicit real quadratic-form
surface. -/
theorem hilbertMatrix_isSymPosDef_explicit (n : ℕ) :
    (∀ i j : Fin n, hilbertMatrix n i j = hilbertMatrix n j i) ∧
      ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        0 < ∑ i : Fin n, ∑ j : Fin n, x i * hilbertMatrix n i j * x j := by
  constructor
  · intro i j
    have h := congrArg (fun M : RSqMat n => M i j) (hilbertMatrix_transpose n)
    simpa [Matrix.transpose_apply] using h.symm
  · exact hilbertMatrix_quadratic_pos n

end NumStability
