import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter14 Problem07 OnesVector MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Problem 14.7:
    if one row of a nonsingular matrix consists entirely of ones, then the
    entries of its inverse sum to one. -/
theorem higham14_problem14_7_inverse_entries_sum_eq_one_of_row_ones (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv)
    (i : Fin n)
    (hrow : ∀ k : Fin n, A i k = 1) :
    (∑ j : Fin n, ∑ k : Fin n, A_inv k j) = 1 := by
  have hColSum : ∀ j : Fin n,
      (∑ k : Fin n, A_inv k j) = if i = j then (1 : ℝ) else 0 := by
    intro j
    have h := hRight i j
    simpa [hrow] using h
  calc
    (∑ j : Fin n, ∑ k : Fin n, A_inv k j)
        = ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hColSum j
    _ = 1 := by
          simp [Finset.mem_univ]

/-- Higham, 2nd ed., Chapter 14, Problem 14.7:
    if one column of a nonsingular matrix consists entirely of ones, then the
    entries of its inverse sum to one. -/
theorem higham14_problem14_7_inverse_entries_sum_eq_one_of_col_ones (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv)
    (j : Fin n)
    (hcol : ∀ k : Fin n, A k j = 1) :
    (∑ i : Fin n, ∑ k : Fin n, A_inv i k) = 1 := by
  have hRowSum : ∀ i : Fin n,
      (∑ k : Fin n, A_inv i k) = if i = j then (1 : ℝ) else 0 := by
    intro i
    have h := hLeft i j
    simpa [hcol] using h
  calc
    (∑ i : Fin n, ∑ k : Fin n, A_inv i k)
        = ∑ i : Fin n, (if i = j then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hRowSum i
    _ = 1 := by
          simp [Finset.mem_univ]

end NumStability
