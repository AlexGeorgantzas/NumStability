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
# Chapter14 Problem10 EntryPerturbation MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Entry perturbation used in Higham Chapter 14, Problem 14.10:
    replace `aᵢⱼ` by `aᵢⱼ + t`, leaving every other entry unchanged. -/
noncomputable def matrixEntryPerturb (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.updateRow (A : Matrix (Fin n) (Fin n) ℝ) i
    ((A : Matrix (Fin n) (Fin n) ℝ) i +
      t • (Pi.single j (1 : ℝ) : Fin n → ℝ))

/-- Higham, 2nd ed., Chapter 14, Problem 14.10, cofactor form:
    changing entry `aᵢⱼ` by `t` changes the determinant by
    `t * adj(A)ⱼᵢ`. -/
theorem higham14_problem14_10_det_entry_perturb_eq
    (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    Matrix.det (matrixEntryPerturb n A i j t) =
      Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) +
        t * Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℝ) j i := by
  unfold matrixEntryPerturb
  rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self, Matrix.adjugate_apply]

/-- Higham, 2nd ed., Chapter 14, Problem 14.10:
    if the `(j,i)` cofactor/adjugate entry vanishes, then `det(A)` is
    independent of the entry `aᵢⱼ`. -/
theorem higham14_problem14_10_det_entry_independent_of_adjugate_eq_zero
    (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n)
    (hAdj : Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℝ) j i = 0) :
    ∀ t : ℝ,
      Matrix.det (matrixEntryPerturb n A i j t) =
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by
  intro t
  rw [higham14_problem14_10_det_entry_perturb_eq n A i j t, hAdj, mul_zero, add_zero]

/-- Higham, 2nd ed., Chapter 14, Problem 14.10:
    the determinant is independent of `aᵢⱼ` for all additive perturbations iff
    the `(j,i)` adjugate entry is zero. -/
theorem higham14_problem14_10_det_entry_independent_iff_adjugate_eq_zero
    (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∀ t : ℝ,
      Matrix.det (matrixEntryPerturb n A i j t) =
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ↔
      Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℝ) j i = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [higham14_problem14_10_det_entry_perturb_eq n A i j 1] at h1
    linarith
  · exact higham14_problem14_10_det_entry_independent_of_adjugate_eq_zero n A i j

end NumStability
