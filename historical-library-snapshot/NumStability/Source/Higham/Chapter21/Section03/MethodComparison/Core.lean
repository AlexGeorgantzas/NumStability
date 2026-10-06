import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.CorrectedRecurrence.Core
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation04.UnderdeterminedSpec

/-!
# Source.Higham.Chapter21.Section03.MethodComparison.Core

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 21, unnumbered MGS discussion in Section 21.3 (printed pp. 412-413).



namespace NumStability

open scoped BigOperators

noncomputable section

/-! ## The displayed comparison bound -/









theorem higham21MGSRectKappa2With_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real) :
    0 <= higham21MGSRectKappa2With A Aplus := by
  exact mul_nonneg (complexMatrixOp2_nonneg _) (complexMatrixOp2_nonneg _)

/-- A literal proposition-level reading of
    `relativeError <= c_mn * u * kappa_2(A) + O(u^2)`.

    The remainder is a parameter so the structure has proof fields only. -/
structure Higham21MGSComparisonBound
    (relativeError remainder : Real -> Real)
    (c_mn kappaA : Real) : Prop where
  remainder_isBigO :
    remainder =O[nhds 0] (fun u : Real => u ^ 2)
  bound : forall u, 0 <= u ->
    relativeError u <= c_mn * u * kappaA + remainder u

/-- A finite quadratic remainder used to instantiate the printed Landau term. -/
def higham21MGSQuadraticRemainder (C u : Real) : Real :=
  C * u ^ 2

theorem higham21MGSQuadraticRemainder_isBigO (C : Real) :
    (fun u : Real => higham21MGSQuadraticRemainder C u)
      =O[nhds 0] (fun u : Real => u ^ 2) := by
  simpa [higham21MGSQuadraticRemainder] using
    (Asymptotics.isBigO_const_mul_self
      C (fun u : Real => u ^ 2) (nhds 0))

/-- An explicit `C*u^2` estimate closes the exact Landau interface used by the
    historical comparison on printed page 412. -/
theorem higham21_mgs_comparison_bound_of_quadratic
    (relativeError : Real -> Real) (c_mn kappaA C : Real)
    (hbound : forall u, 0 <= u ->
      relativeError u <= c_mn * u * kappaA + C * u ^ 2) :
    Exists fun remainder : Real -> Real =>
      Higham21MGSComparisonBound relativeError remainder c_mn kappaA := by
  refine ⟨higham21MGSQuadraticRemainder C, ?_⟩
  constructor
  · exact higham21MGSQuadraticRemainder_isBigO C
  · intro u hu
    simpa [higham21MGSQuadraticRemainder] using hbound u hu

/-- The same comparison specialized to the source `kappa_2(A)` product.
    The pseudoinverse hypothesis licenses that interpretation; the historical
    algorithm analyses supplying `hbound` are not reconstructed here. -/
theorem higham21_mgs_comparison_bound_with_rect_kappa2_of_quadratic
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (_hAplus : RectMoorePenrosePseudoinverse m n A Aplus)
    (relativeError : Real -> Real) (c_mn C : Real)
    (hbound : forall u, 0 <= u ->
      relativeError u <=
        c_mn * u * higham21MGSRectKappa2With A Aplus + C * u ^ 2) :
    Exists fun remainder : Real -> Real =>
      Higham21MGSComparisonBound relativeError remainder c_mn
        (higham21MGSRectKappa2With A Aplus) :=
  higham21_mgs_comparison_bound_of_quadratic
    relativeError c_mn (higham21MGSRectKappa2With A Aplus) C hbound

/-! ## Naive forward formation and its two exact error channels -/








































































































































































































































/-- An exact economy QR factorization with orthonormal columns and nonsingular
    `R` produces the minimum-norm solution through `Q*y`. -/
theorem higham21_mgs_economy_qr_min_norm {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Q : Fin n -> Fin m -> Real) (R Rinv : Fin m -> Fin m -> Real)
    (y : Fin m -> Real)
    (hfactor : finiteTranspose A = matMulRect n m m Q R)
    (hsolve : rectMatMulVec (finiteTranspose R) y = b)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hRight : IsRightInverse m R Rinv) :
    RectMinNormSolution m n A b (higham21MGSNaiveFormation Q y) := by
  have hsystem :
      rectMatMulVec A (higham21MGSNaiveFormation Q y) = b :=
    higham21_mgs_naive_formation_solves_of_orthonormal
      A Q R b y hfactor hsolve hQ
  let z : Fin m -> Real := rectMatMulVec Rinv y
  have hz : rectMatMulVec R z = y := by
    change matMulVec m R (matMulVec m Rinv y) = y
    exact matMulVec_of_isRightInverse R Rinv hRight y
  have htranspose :
      rectTransposeMulVec A z = higham21MGSNaiveFormation Q y := by
    change rectMatMulVec (finiteTranspose A) z = rectMatMulVec Q y
    rw [hfactor]
    change rectMatMulVec (rectMatMul Q R) z = rectMatMulVec Q y
    rw [rectMatMulVec_rectMatMul, hz]
  have htransposeSolve :
      rectMatMulVec A (rectTransposeMulVec A z) = b := by
    rw [htranspose]
    exact hsystem
  have hmin :=
    higham21_eq21_4_rect_transpose_min_norm_of_solves
      A b z htransposeSolve
  rw [htranspose] at hmin
  exact hmin

/-! ## The corrected backward recurrence -/


































































/-! ## Rowwise stability handoff -/




















































































































































end

end NumStability
