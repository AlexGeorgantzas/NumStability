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
# Chapter14 Equation35 HymanBlockFactorization MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Section 14.6.1, printed p.280:
    the row vector `hᵀ T⁻¹` in Hyman's method.  We model the
    source `(n-1)`-by-`(n-1)` block as an arbitrary `Fin n` block. -/
noncomputable def higham14_hymanRowTimesInv {n : ℕ}
    (h : Fin n → ℝ) (Tinv : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun j => ∑ k : Fin n, h k * Tinv k j

/-- Higham, 2nd ed., Chapter 14, Section 14.6.1, printed p.280:
    the Schur scalar `η - hᵀ T⁻¹ y` appearing in (14.35)--(14.36). -/
noncomputable def higham14_hymanSchur {n : ℕ}
    (h y : Fin n → ℝ) (Tinv : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) : ℝ :=
  η - ∑ j : Fin n, higham14_hymanRowTimesInv h Tinv j * y j

/-- Higham, 2nd ed., Chapter 14, Section 14.6.1, printed p.280:
    the cyclically permuted Hessenberg block matrix
    `H₁ = [[T, y], [hᵀ, η]]` used by Hyman's method. -/
noncomputable def higham14_hymanBlockMatrix {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks T (fun i (_ : Unit) => y i) (fun (_ : Unit) j => h j)
    (fun _ _ => η)

/-- Higham, 2nd ed., Chapter 14, equation (14.35), printed p.280:
    the lower block factor `[[I,0],[hᵀT⁻¹,1]]` in Hyman's LU factorization. -/
noncomputable def higham14_hymanLowerFactor {n : ℕ}
    (h : Fin n → ℝ) (Tinv : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks 1 0 (fun (_ : Unit) j => higham14_hymanRowTimesInv h Tinv j)
    (1 : Matrix Unit Unit ℝ)

/-- Higham, 2nd ed., Chapter 14, equation (14.35), printed p.280:
    the upper block factor `[[T,y],[0,η-hᵀT⁻¹y]]` in Hyman's LU factorization. -/
noncomputable def higham14_hymanUpperFactor {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ)
    (Tinv : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks T (fun i (_ : Unit) => y i) 0
    (fun _ _ => higham14_hymanSchur h y Tinv η)

lemma higham14_hymanRowTimesInv_mul_T {n : ℕ}
    (T Tinv : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (hTinv : IsLeftInverse n T Tinv) (j : Fin n) :
    ∑ x : Fin n, higham14_hymanRowTimesInv h Tinv x * T x j = h j := by
  calc
    ∑ x : Fin n, higham14_hymanRowTimesInv h Tinv x * T x j
        = ∑ x : Fin n, (∑ k : Fin n, h k * Tinv k x) * T x j := rfl
    _ = ∑ k : Fin n, h k * (∑ x : Fin n, Tinv k x * T x j) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = ∑ k : Fin n, h k * (if k = j then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hTinv k j]
    _ = h j := by
        simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Higham, 2nd ed., Chapter 14, equation (14.35), printed p.280:
    exact Hyman block LU factorization of the cyclically permuted Hessenberg
    block matrix, assuming the displayed inverse certificate `T⁻¹T = I`. -/
theorem higham14_eq14_35_hyman_block_lu_factorization {n : ℕ}
    (T Tinv : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ)
    (hTinv : IsLeftInverse n T Tinv) :
    higham14_hymanBlockMatrix T y h η =
      higham14_hymanLowerFactor h Tinv *
        higham14_hymanUpperFactor T y h Tinv η := by
  ext a b
  cases a <;> cases b
  · rename_i i j
    simp [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, Matrix.mul_apply, Matrix.one_apply]
  · rename_i i u
    simp [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, Matrix.mul_apply, Matrix.one_apply]
  · rename_i u j
    simpa [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, Matrix.mul_apply]
      using (higham14_hymanRowTimesInv_mul_T T Tinv h hTinv j).symm
  · rename_i u v
    simp [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, higham14_hymanSchur, Matrix.mul_apply]

end NumStability
