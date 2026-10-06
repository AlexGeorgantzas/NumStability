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
import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion
import NumStability.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter14 Section01 ProductErrorNotation ProductErrorNotation

Canonical destination for material split out of
`NumStability.Algorithms.Ch14ProductErrorNotation` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

namespace Ch14RectProductTree

/-- Higham's `p`-budget form:

`|Delta(A1, ..., Ak)| <= gamma_p |A1| ... |Ak|`,

where `p` is the sum of the inner dimensions at the internal nodes of the
chosen binary evaluation tree. -/
theorem productDelta_abs_le_gamma_operationBudget {m n : Nat} (fp : FPModel)
    (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    forall i j,
      |productDelta fp tree i j| <=
        gamma fp (operationBudget tree) * exactAbsProduct tree i j := by
  intro i j
  calc
    |productDelta fp tree i j|
        <= orderCoefficient fp tree * exactAbsProduct tree i j :=
      productDelta_abs_le_orderCoefficient fp tree hvalid i j
    _ <= gamma fp (operationBudget tree) * exactAbsProduct tree i j :=
      mul_le_mul_of_nonneg_right
        (orderCoefficient_le_gamma_operationBudget fp tree hvalid)
        (exactAbsProduct_nonneg tree i j)

/-- Rectangular contract at the collapsed `gamma_p` coefficient. -/
theorem roundedEval_RectMatProdError_gamma_operationBudget {m n : Nat}
    (fp : FPModel) (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    RectMatProdError (roundedEval fp tree) (exactEval tree)
      (gamma fp (operationBudget tree)) (exactAbsProduct tree) := by
  intro i j
  simpa [productDelta] using
    productDelta_abs_le_gamma_operationBudget fp tree hvalid i j

/-- Literal `c_p u` form with the explicit choice `c_p = 2p`.  The displayed
smallness guard is the standard condition under which `gamma_p <= 2p*u`.
It also discharges `gammaValid fp p`. -/
theorem productDelta_abs_le_two_mul_operationBudget_mul_u {m n : Nat}
    (fp : FPModel) (tree : Ch14RectProductTree m n)
    (hhalf : (operationBudget tree : Real) * fp.u <= 1 / 2) :
    forall i j,
      |productDelta fp tree i j| <=
        (2 * (operationBudget tree : Real)) * fp.u *
          exactAbsProduct tree i j := by
  have hvalid : gammaValid fp (operationBudget tree) := by
    unfold gammaValid
    linarith
  have hgamma :
      gamma fp (operationBudget tree) <=
        2 * ((operationBudget tree : Real) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp (operationBudget tree) hhalf
  intro i j
  calc
    |productDelta fp tree i j|
        <= gamma fp (operationBudget tree) * exactAbsProduct tree i j :=
      productDelta_abs_le_gamma_operationBudget fp tree hvalid i j
    _ <= (2 * ((operationBudget tree : Real) * fp.u)) *
          exactAbsProduct tree i j :=
      mul_le_mul_of_nonneg_right hgamma (exactAbsProduct_nonneg tree i j)
    _ = (2 * (operationBudget tree : Real)) * fp.u *
          exactAbsProduct tree i j := by ring

/-- Rectangular contract in the literal source shape `c_p*u`, with
`c_p = 2p`. -/
theorem roundedEval_RectMatProdError_two_mul_operationBudget_mul_u
    {m n : Nat} (fp : FPModel) (tree : Ch14RectProductTree m n)
    (hhalf : (operationBudget tree : Real) * fp.u <= 1 / 2) :
    RectMatProdError (roundedEval fp tree) (exactEval tree)
      ((2 * (operationBudget tree : Real)) * fp.u) (exactAbsProduct tree) := by
  intro i j
  simpa [productDelta] using
    productDelta_abs_le_two_mul_operationBudget_mul_u fp tree hhalf i j

/-- Adapter back to the chapter's legacy square `MatProdError` interface for
square endpoints of the heterogeneous tree. -/
theorem roundedEval_MatProdError_gamma_operationBudget {n : Nat}
    (fp : FPModel) (tree : Ch14RectProductTree n n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    MatProdError n (roundedEval fp tree) (exactEval tree)
      (gamma fp (operationBudget tree)) (exactAbsProduct tree) := by
  intro i j
  simpa [productDelta] using
    productDelta_abs_le_gamma_operationBudget fp tree hvalid i j

/-- Literal Chapter 14 package at the exact `gamma_p` budget: the concrete
computed product equals the exact compatible product plus a perturbation that
obeys the printed componentwise absolute-product shape. -/
theorem exists_productDelta_gamma_operationBudget {m n : Nat} (fp : FPModel)
    (tree : Ch14RectProductTree m n)
    (hvalid : gammaValid fp (operationBudget tree)) :
    exists Delta : Fin m -> Fin n -> Real,
      roundedEval fp tree = (fun i j => exactEval tree i j + Delta i j) /\
      forall i j,
        |Delta i j| <=
          gamma fp (operationBudget tree) * exactAbsProduct tree i j := by
  refine ⟨productDelta fp tree,
    roundedEval_eq_exactEval_add_productDelta fp tree, ?_⟩
  exact productDelta_abs_le_gamma_operationBudget fp tree hvalid

/-- Literal Chapter 14 `c_p*u` package with the explicit model-derived choice
`c_p = 2p` under `p*u <= 1/2`. -/
theorem exists_productDelta_two_mul_operationBudget_mul_u {m n : Nat}
    (fp : FPModel) (tree : Ch14RectProductTree m n)
    (hhalf : (operationBudget tree : Real) * fp.u <= 1 / 2) :
    exists Delta : Fin m -> Fin n -> Real,
      roundedEval fp tree = (fun i j => exactEval tree i j + Delta i j) /\
      forall i j,
        |Delta i j| <=
          (2 * (operationBudget tree : Real)) * fp.u *
            exactAbsProduct tree i j := by
  refine ⟨productDelta fp tree,
    roundedEval_eq_exactEval_add_productDelta fp tree, ?_⟩
  exact productDelta_abs_le_two_mul_operationBudget_mul_u fp tree hhalf

end Ch14RectProductTree
end NumStability
