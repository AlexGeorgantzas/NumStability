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
import NumStability.Source.Higham.Chapter14.Equation35.HymanBlockFactorization.MatrixInversion

/-!
# Chapter14 Equation36 HymanDeterminant MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, equation (14.36), printed p.280:
    determinant of the cyclically permuted Hyman block matrix is
    `det(T) * (η - hᵀT⁻¹y)`.  The separate cyclic-permutation sign converts
    this to the determinant of the original Hessenberg matrix. -/
theorem higham14_eq14_36_hyman_det_cyclic_block {n : ℕ}
    (T Tinv : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ)
    (hTinv : IsLeftInverse n T Tinv) :
    Matrix.det (higham14_hymanBlockMatrix T y h η) =
      Matrix.det T * higham14_hymanSchur h y Tinv η := by
  rw [higham14_eq14_35_hyman_block_lu_factorization T Tinv y h η hTinv]
  rw [Matrix.det_mul]
  have hdetL : Matrix.det (higham14_hymanLowerFactor h Tinv) = 1 := by
    rw [higham14_hymanLowerFactor, Matrix.det_fromBlocks_zero₁₂]
    simp
  have hdetU : Matrix.det (higham14_hymanUpperFactor T y h Tinv η) =
      Matrix.det T * higham14_hymanSchur h y Tinv η := by
    rw [higham14_hymanUpperFactor, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [hdetL, hdetU]
  ring

/-- Higham, 2nd ed., Chapter 14, equation (14.36), printed p.280:
    signed determinant formula for an original Hessenberg matrix whose row
    permutation is the cyclic Hyman block matrix.  For the source's cyclic
    permutation, the sign is the printed `(-1)^(n-1)` factor. -/
theorem higham14_eq14_36_hyman_det_original_of_row_permutation {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T Tinv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η : ℝ) (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hH :
      higham14_hymanBlockMatrix T y h η =
        Matrix.submatrix H σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTinv : IsLeftInverse n T Tinv) :
    Matrix.det H =
      (Equiv.Perm.sign σ : ℝ) *
        Matrix.det T * higham14_hymanSchur h y Tinv η := by
  have hperm_det :
      Matrix.det (higham14_hymanBlockMatrix T y h η) =
        (Equiv.Perm.sign σ : ℝ) * Matrix.det H := by
    rw [hH]
    simpa using
      (Matrix.det_permute (R := ℝ) σ H)
  have hcyclic :=
    higham14_eq14_36_hyman_det_cyclic_block
      T Tinv y h η hTinv
  have hdirect :
      (Equiv.Perm.sign σ : ℝ) * Matrix.det H =
        Matrix.det T * higham14_hymanSchur h y Tinv η := by
    rw [← hperm_det, hcyclic]
  have hsq : (Equiv.Perm.sign σ : ℝ) *
      (Equiv.Perm.sign σ : ℝ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
      simp [hsign]
  calc
    Matrix.det H = 1 * Matrix.det H := by ring
    _ = ((Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign σ : ℝ)) *
          Matrix.det H := by
          rw [hsq]
    _ = (Equiv.Perm.sign σ : ℝ) *
          ((Equiv.Perm.sign σ : ℝ) * Matrix.det H) := by
          ring
    _ = (Equiv.Perm.sign σ : ℝ) *
          (Matrix.det T * higham14_hymanSchur h y Tinv η) := by
          rw [hdirect]
    _ = (Equiv.Perm.sign σ : ℝ) *
          Matrix.det T * higham14_hymanSchur h y Tinv η := by
          ring

end NumStability
