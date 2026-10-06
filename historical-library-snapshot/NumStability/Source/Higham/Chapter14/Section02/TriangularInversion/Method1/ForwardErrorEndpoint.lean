import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
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
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint

/-!
# Chapter14 Section02 TriangularInversion Method1 ForwardErrorEndpoint

Canonical destination for material split out of
`NumStability.Algorithms.Ch14ForwardErrorEndpoint` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- Higham, 2nd ed., Chapter 14, equation (14.6), envelope step.
The Method 1 right-residual theorem itself implies
`|Xhat| ≤ |L⁻¹| + gamma_n |L⁻¹||L||Xhat|`; no componentwise domination of
`Xhat` by the true inverse is assumed. -/
theorem ch14ext_eq14_6_method1_abs_Xhat_envelope (n : ℕ) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hn : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j, |X_hat i j| ≤ |L_inv i j| + gamma fp n *
      ch14ext_rightResidualEnvelopeRemainder n L L_inv X_hat i j := by
  intro X_hat i j
  apply ch14ext_abs_X_le_abs_Ainv_plus_rightResidual_remainder
    n L L_inv X_hat (gamma fp n) hInv
  intro p q
  have hres := triInv_method1_right_residual_matrix n fp L hL_diag hLT hn p q
  simpa [inverseRightResidual, matMul, idMatrix] using hres

/-- The full higher-order term displayed by the equation (14.6) endpoint,
scalarized in u while the computed inverse and all other matrix data stay
fixed. -/
noncomputable def ch14ext_eq14_6_method1_quadraticRemainder (n : ℕ)
    (L L_inv X_hat : Fin n → Fin n → ℝ) (i j : Fin n) (u : ℝ) : ℝ :=
  u ^ 2 *
    (ch14ext_gammaQuadraticCoefficientScalar n u *
        (∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
      (ch14ext_gammaUnitCoefficientScalar n u) ^ 2 *
        (∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| *
            ch14ext_rightResidualEnvelopeRemainder n L L_inv X_hat k₂ j)))

/-- At the model unit roundoff, the scalarized equation (14.6) remainder is
definitionally the higher-order term in the endpoint theorem. -/
theorem ch14ext_eq14_6_method1_quadraticRemainder_at_fp (n : ℕ)
    (fp : FPModel) (L L_inv X_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    ch14ext_eq14_6_method1_quadraticRemainder
        n L L_inv X_hat i j fp.u =
      fp.u ^ 2 *
        (ch14ext_gammaQuadraticCoefficient fp n *
            (∑ k₁ : Fin n, |L_inv i k₁| *
              (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
          (ch14ext_gammaUnitCoefficient fp n) ^ 2 *
            (∑ k₁ : Fin n, |L_inv i k₁| *
              (∑ k₂ : Fin n, |L k₁ k₂| *
                ch14ext_rightResidualEnvelopeRemainder
                  n L L_inv X_hat k₂ j))) := by
  rfl

end Ch14Ext
end NumStability
