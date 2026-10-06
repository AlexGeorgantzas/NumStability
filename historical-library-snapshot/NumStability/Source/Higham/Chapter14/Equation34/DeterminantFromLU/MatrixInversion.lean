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
# Chapter14 Equation34 DeterminantFromLU MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, equation (14.34), exact no-pivot/unit-lower
    LU core: the determinant is the product of the diagonal entries of `U`. -/
theorem higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i := by
  simpa using hLU.det_eq_prod_U_diag

/-- Higham, 2nd ed., Chapter 14, equation (14.34), absolute-value no-pivot
    determinant product form.  The row-interchange parity factor in GEPP is
    absent here because the certificate is an exact `A = L * U` factorization. -/
theorem higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_LUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      |∏ i : Fin n, U i i| := by
  rw [higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec hLU]

/-- Higham, 2nd ed., Chapter 14, equation (14.34), direct signed pivoted
    determinant relation.  If the row permutation `σ` gives `PA = L * U`,
    then `sign(σ) * det(A)` is the product of the computed pivots. -/
theorem higham14_eq14_34_perm_sign_mul_det_eq_prod_U_diag_of_PermutedLUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ} {σ : Fin n → Fin n}
    (hLU : PermutedLUFactSpec n A L U σ) :
    (Equiv.Perm.sign (Equiv.ofBijective σ hLU.perm) : ℝ) *
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i := by
  let Aσ : Fin n → Fin n → ℝ := fun i j => A (σ i) j
  have hLUσ : LUFactSpec n Aσ L U :=
    { L_diag := hLU.L_diag
      L_upper_zero := hLU.L_upper_zero
      U_lower_zero := hLU.U_lower_zero
      product_eq := by
        intro i j
        exact hLU.product_eq i j }
  have hdetσ :
      Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        ∏ i : Fin n, U i i :=
    higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec hLUσ
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective σ hLU.perm
  have hAσ :
      (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.submatrix (A : Matrix (Fin n) (Fin n) ℝ)
          eSigma (Equiv.refl (Fin n)) := by
    ext i j
    change A (σ i) j = A ((Equiv.ofBijective σ hLU.perm) i) j
    rfl
  have hperm :
      Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        (Equiv.Perm.sign eSigma : ℝ) *
          Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hAσ]
    simpa using
      (Matrix.det_permute (R := ℝ) eSigma
        (A : Matrix (Fin n) (Fin n) ℝ))
  change
    (Equiv.Perm.sign eSigma : ℝ) *
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i
  rw [← hdetσ]
  exact hperm.symm

/-- Higham, 2nd ed., Chapter 14, equation (14.34), source-oriented signed
    pivoted determinant product.  Since a permutation sign is its own inverse,
    the direct `sign(σ) * det(A)` relation is equivalent to the displayed
    `det(A) = sign(σ) * ∏ᵢ uᵢᵢ` form. -/
theorem higham14_eq14_34_det_eq_perm_sign_mul_prod_U_diag_of_PermutedLUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ} {σ : Fin n → Fin n}
    (hLU : PermutedLUFactSpec n A L U σ) :
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      (Equiv.Perm.sign (Equiv.ofBijective σ hLU.perm) : ℝ) *
        ∏ i : Fin n, U i i := by
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective σ hLU.perm
  have hdirect :=
    higham14_eq14_34_perm_sign_mul_det_eq_prod_U_diag_of_PermutedLUFactSpec
      (A := A) (L := L) (U := U) (σ := σ) hLU
  change
    (Equiv.Perm.sign eSigma : ℝ) *
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i at hdirect
  have hsq : (Equiv.Perm.sign eSigma : ℝ) *
      (Equiv.Perm.sign eSigma : ℝ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign eSigma) with hsign | hsign <;>
      simp [hsign]
  calc
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)
        = 1 * Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by ring
    _ = ((Equiv.Perm.sign eSigma : ℝ) * (Equiv.Perm.sign eSigma : ℝ)) *
          Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by
          rw [hsq]
    _ = (Equiv.Perm.sign eSigma : ℝ) *
          ((Equiv.Perm.sign eSigma : ℝ) *
            Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) := by
          ring
    _ = (Equiv.Perm.sign eSigma : ℝ) * ∏ i : Fin n, U i i := by
          rw [hdirect]

/-- Higham, 2nd ed., Chapter 14, equation (14.34), pivoted absolute-value
    determinant product form.  A row permutation can change only the sign of
    the determinant, so a `PA = L * U` certificate gives the same absolute
    determinant product as the no-pivot core. -/
theorem higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_PermutedLUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ} {σ : Fin n → Fin n}
    (hLU : PermutedLUFactSpec n A L U σ) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      |∏ i : Fin n, U i i| := by
  let Aσ : Fin n → Fin n → ℝ := fun i j => A (σ i) j
  have hLUσ : LUFactSpec n Aσ L U :=
    { L_diag := hLU.L_diag
      L_upper_zero := hLU.L_upper_zero
      U_lower_zero := hLU.U_lower_zero
      product_eq := by
        intro i j
        exact hLU.product_eq i j }
  have hdetσ :
      Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        ∏ i : Fin n, U i i :=
    higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec hLUσ
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective σ hLU.perm
  have hAσ :
      (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.submatrix (A : Matrix (Fin n) (Fin n) ℝ)
          eSigma (Equiv.refl (Fin n)) := by
    ext i j
    change A (σ i) j = A ((Equiv.ofBijective σ hLU.perm) i) j
    rfl
  have hAbs :
      |Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ)| =
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
    rw [hAσ]
    simpa using
      (Matrix.abs_det_submatrix_equiv_equiv (R := ℝ)
        eSigma (Equiv.refl (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ))
  rw [hdetσ] at hAbs
  exact hAbs.symm

end NumStability
