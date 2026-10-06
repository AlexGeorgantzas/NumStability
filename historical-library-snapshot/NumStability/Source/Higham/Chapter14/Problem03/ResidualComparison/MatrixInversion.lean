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
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter14 Problem03 ResidualComparison MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Problem 14.3 algebraic identity:
    `AX - I = A (XA - I) A⁻¹`. -/
theorem higham14_problem14_3_right_residual_eq_mul_left_residual (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv) :
    inverseRightResidual n A X =
      matMul n (matMul n A (inverseLeftResidual n A X)) A_inv := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := A_inv
  let XM : Matrix (Fin n) (Fin n) ℝ := X
  have hAAinv : AM * AinvM = 1 := by
    ext i j
    simpa [AM, AinvM, Matrix.mul_apply] using hRight i j
  have hmat :
      AM * XM - 1 = AM * (XM * AM - 1) * AinvM := by
    calc
      AM * XM - 1
          = AM * XM * (AM * AinvM) - AM * AinvM := by
              rw [hAAinv]
              simp
      _ = AM * (XM * AM - 1) * AinvM := by
              noncomm_ring
  ext i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmat
  simpa [inverseRightResidual, inverseLeftResidual, matMul, idMatrix,
    AM, AinvM, XM, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] using hentry

/-- Higham, 2nd ed., Chapter 14, Problem 14.3 algebraic identity:
    `XA - I = A⁻¹ (AX - I) A`. -/
theorem higham14_problem14_3_left_residual_eq_mul_right_residual (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv) :
    inverseLeftResidual n A X =
      matMul n (matMul n A_inv (inverseRightResidual n A X)) A := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := A_inv
  let XM : Matrix (Fin n) (Fin n) ℝ := X
  have hAinvA : AinvM * AM = 1 := by
    ext i j
    simpa [AM, AinvM, Matrix.mul_apply] using hLeft i j
  have hmat :
      XM * AM - 1 = AinvM * (AM * XM - 1) * AM := by
    calc
      XM * AM - 1
          = AinvM * AM * XM * AM - AinvM * AM := by
              rw [hAinvA]
              simp
      _ = AinvM * (AM * XM - 1) * AM := by
              noncomm_ring
  ext i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmat
  simpa [inverseRightResidual, inverseLeftResidual, matMul, idMatrix,
    AM, AinvM, XM, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] using hentry

/-- Higham, 2nd ed., Chapter 14, Problem 14.3, infinity-norm half:
    `‖AX - I‖∞ / ‖XA - I‖∞ ≤ κ∞(A)`. -/
theorem higham14_problem14_3_right_over_left_residual_infNorm_le_kappa
    (n : ℕ) (hn : 0 < n)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv)
    (hLeftResPos : 0 < infNorm (inverseLeftResidual n A X)) :
    infNorm (inverseRightResidual n A X) /
        infNorm (inverseLeftResidual n A X) ≤
      kappaInf n hn A A_inv := by
  have hres_eq :=
    higham14_problem14_3_right_residual_eq_mul_left_residual
      n A A_inv X hRight
  have hnorm :
      infNorm (inverseRightResidual n A X) ≤
        (infNorm A * infNorm (inverseLeftResidual n A X)) * infNorm A_inv := by
    calc
      infNorm (inverseRightResidual n A X)
          = infNorm (matMul n (matMul n A (inverseLeftResidual n A X)) A_inv) := by
              rw [hres_eq]
      _ ≤ infNorm (matMul n A (inverseLeftResidual n A X)) * infNorm A_inv :=
              infNorm_matMul_le hn (matMul n A (inverseLeftResidual n A X)) A_inv
      _ ≤ (infNorm A * infNorm (inverseLeftResidual n A X)) * infNorm A_inv := by
              exact mul_le_mul_of_nonneg_right
                (infNorm_matMul_le hn A (inverseLeftResidual n A X))
                (infNorm_nonneg A_inv)
  have hdiv := div_le_div_of_nonneg_right hnorm (le_of_lt hLeftResPos)
  calc
    infNorm (inverseRightResidual n A X) /
        infNorm (inverseLeftResidual n A X)
        ≤ ((infNorm A * infNorm (inverseLeftResidual n A X)) * infNorm A_inv) /
            infNorm (inverseLeftResidual n A X) := hdiv
    _ = infNorm A * infNorm A_inv := by
        field_simp [ne_of_gt hLeftResPos]
    _ = kappaInf n hn A A_inv := by
        rw [kappaInf_eq_infNorm_mul_infNorm n hn A A_inv]

/-- Higham, 2nd ed., Chapter 14, Problem 14.3, infinity-norm half:
    `‖XA - I‖∞ / ‖AX - I‖∞ ≤ κ∞(A)`. -/
theorem higham14_problem14_3_left_over_right_residual_infNorm_le_kappa
    (n : ℕ) (hn : 0 < n)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv)
    (hRightResPos : 0 < infNorm (inverseRightResidual n A X)) :
    infNorm (inverseLeftResidual n A X) /
        infNorm (inverseRightResidual n A X) ≤
      kappaInf n hn A A_inv := by
  have hres_eq :=
    higham14_problem14_3_left_residual_eq_mul_right_residual
      n A A_inv X hLeft
  have hnorm :
      infNorm (inverseLeftResidual n A X) ≤
        (infNorm A_inv * infNorm (inverseRightResidual n A X)) * infNorm A := by
    calc
      infNorm (inverseLeftResidual n A X)
          = infNorm (matMul n (matMul n A_inv (inverseRightResidual n A X)) A) := by
              rw [hres_eq]
      _ ≤ infNorm (matMul n A_inv (inverseRightResidual n A X)) * infNorm A :=
              infNorm_matMul_le hn
                (matMul n A_inv (inverseRightResidual n A X)) A
      _ ≤ (infNorm A_inv * infNorm (inverseRightResidual n A X)) * infNorm A := by
              exact mul_le_mul_of_nonneg_right
                (infNorm_matMul_le hn A_inv (inverseRightResidual n A X))
                (infNorm_nonneg A)
  have hdiv := div_le_div_of_nonneg_right hnorm (le_of_lt hRightResPos)
  calc
    infNorm (inverseLeftResidual n A X) /
        infNorm (inverseRightResidual n A X)
        ≤ ((infNorm A_inv * infNorm (inverseRightResidual n A X)) * infNorm A) /
            infNorm (inverseRightResidual n A X) := hdiv
    _ = infNorm A_inv * infNorm A := by
        field_simp [ne_of_gt hRightResPos]
    _ = kappaInf n hn A A_inv := by
        rw [kappaInf_eq_infNorm_mul_infNorm n hn A A_inv]
        ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.3:
    for nonzero left and right residuals,
    `max (‖AX-I‖∞/‖XA-I‖∞) (‖XA-I‖∞/‖AX-I‖∞) ≤ κ∞(A)`. -/
theorem higham14_problem14_3_max_residual_ratio_infNorm_le_kappa
    (n : ℕ) (hn : 0 < n)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A A_inv)
    (hLeftResPos : 0 < infNorm (inverseLeftResidual n A X))
    (hRightResPos : 0 < infNorm (inverseRightResidual n A X)) :
    max
        (infNorm (inverseRightResidual n A X) /
          infNorm (inverseLeftResidual n A X))
        (infNorm (inverseLeftResidual n A X) /
          infNorm (inverseRightResidual n A X))
      ≤ kappaInf n hn A A_inv := by
  exact max_le
    (higham14_problem14_3_right_over_left_residual_infNorm_le_kappa
      n hn A A_inv X hInv.2 hLeftResPos)
    (higham14_problem14_3_left_over_right_residual_infNorm_le_kappa
      n hn A A_inv X hInv.1 hRightResPos)

end NumStability
