import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Logic.Equiv.Basic
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
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsPrelude
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.WeakFamily
import NumStability.Source.Higham.Chapter14.Problem15

/-!
# Chapter14 Corollary07 DiagonalDominance FinalDivisionFamilyClosure

Canonical destination for material split out of
`NumStability.Algorithms.Ch14Cor147FinalDivisionFamilyClosure` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- Successful weakly row-diagonally-dominant runs of the literal final-
division executor along a vanishing-roundoff family.

The extra fields are source structure: a fixed exact no-pivot factorization
`A = L*U`, its fixed exact upper inverse, a fixed source inverse, and a fixed
exact solution.  The computed factors are related to `A` only by the
operation-derived `LUBackwardError` in `gje`; in particular, this contract
does not force the first-stage factorization error to vanish.  No residual,
forward-error, proximity, or remainder conclusion is stored in the contract. -/
structure Ch14Cor147FinalizedRunFamily
    (I : Type*) (l : Filter I) (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) where
  gje : Ch14GJEFinalizedFamily I l n A b
  row_diag_dominant : IsRowDiagDominant n A
  determinant_ne_zero :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0
  L : Fin n -> Fin n -> Real
  U : Fin n -> Fin n -> Real
  U_inv : Fin n -> Fin n -> Real
  exact_lu : LUFactSpec n A L U
  exact_upper_inverse : IsInverse n U U_inv
  source_inverse : IsInverse n A A_inv
  exact_solution : forall i, matMulVec n A x i = b i
  exact_solution_nonzero : 0 < infNormVec x

/-- The computed inverse product printed in (14.31). -/
noncomputable def ch14ext_cor147FinalizedPrintedX
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) (t : I) :
    Fin n -> Fin n -> Real :=
  matMul n (absMatrix n (F.gje.initial t).matrix)
    (absMatrix n (F.gje.U_inv t))

/-- The absolute computed-versus-exact leading-object correction. -/
noncomputable def ch14ext_cor147FinalizedResidualLeadingCorrection
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) (i : Fin n) : Real :=
  |ch14ext_gjeResidualS2 n (F.gje.L_hat t)
      (ch14ext_cor147FinalizedPrintedX F t) (F.gje.initial t).matrix
      (ch14ext_gjeFinalizedFamilyOutput F.gje t) i -
    ch14ext_gjeResidualS2 n F.L
      (ch14ext_cor147WeakExactX n F.U F.U_inv) F.U
      (ch14ext_gjeFinalizedFamilyOutput F.gje t) i|

/-- The actual named terminal term from (14.31), evaluated at the literal
`fl_div` output. -/
noncomputable def ch14ext_cor147FinalizedResidualTerminal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) (i : Fin n) : Real :=
  ch14ext_gjeResidualFinalizedPrintedHigherOrder (F.gje.model t)
    (F.gje.L_hat t) (F.gje.initial t).matrix (F.gje.U_inv t)
    (ch14ext_gjeFinalizedFamilyXabs F.gje t)
    (ch14ext_gjeFinalizedFamilyNormalizedPabs F.gje t)
    (F.gje.initial t).rhs (ch14ext_gjeFinalizedFamilyOutput F.gje t) i

/-- Full Corollary 14.7 residual remainder.  It contains the actual (14.31)
terminal plus the explicit `u * O(u)` transfer from computed factors to the
fixed exact row-dominant factors. -/
noncomputable def ch14ext_cor147FinalizedResidualRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) (i : Fin n) : Real :=
  8 * (n : Real) * (F.gje.model t).u *
      ch14ext_cor147FinalizedResidualLeadingCorrection F t i +
    ch14ext_cor147FinalizedResidualTerminal F t i

/-- The actual terminal vector from (14.32), evaluated at the literal
`fl_div` output. -/
noncomputable def ch14ext_cor147FinalizedForwardTerminalVector
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) (i : Fin n) : Real :=
  ch14ext_gjeForwardFinalDivisionHigherOrder n (F.gje.model t) A_inv
    (F.gje.L_hat t) (F.gje.initial t).matrix
    (ch14ext_gjeFinalizedFamilyNormalizedPabs F.gje t)
    (F.gje.U_inv t) (F.gje.z t) (F.gje.initial t).rhs
    (ch14ext_gjeFinalizedFamilyOutput F.gje t) i

/-- Relative infinity norm of the actual (14.32) terminal vector. -/
noncomputable def ch14ext_cor147FinalizedForwardRelativeTerminal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  infNormVec (ch14ext_cor147FinalizedForwardTerminalVector F t) /
    infNormVec x

/-- Full vector remainder after replacing the computed first-order (14.32)
objects by the fixed exact LU objects.  The first summand is `u * O(u)` and
the second is the actual final-division terminal. -/
noncomputable def ch14ext_cor147FinalizedForwardVectorRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) (i : Fin n) : Real :=
  2 * (n : Real) * (F.gje.model t).u *
      ((ch14ext_gjeForwardT1 n A_inv (F.gje.L_hat t)
          (F.gje.initial t).matrix
          (ch14ext_gjeFinalizedFamilyOutput F.gje t) i +
        3 * ch14ext_gjeForwardT2 n (absMatrix n (F.gje.U_inv t))
          (F.gje.initial t).matrix
          (ch14ext_gjeFinalizedFamilyOutput F.gje t) i) -
       (ch14ext_gjeForwardT1 n A_inv F.L F.U
          (ch14ext_gjeFinalizedFamilyOutput F.gje t) i +
        3 * ch14ext_gjeForwardT2 n (absMatrix n F.U_inv) F.U
          (ch14ext_gjeFinalizedFamilyOutput F.gje t) i)) +
    ch14ext_cor147FinalizedForwardTerminalVector F t i

/-- Relative infinity norm of the full computed-to-exact forward remainder. -/
noncomputable def ch14ext_cor147FinalizedForwardRelativeRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  infNormVec (ch14ext_cor147FinalizedForwardVectorRemainder F t) /
    infNormVec x

/-- Printed first-order relative forward coefficient in Corollary 14.7. -/
noncomputable def ch14ext_cor147FinalizedForwardLeadingCoefficient
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  4 * (n : Real) ^ 3 * (F.gje.model t).u *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos)
      A A_inv + 3)

theorem ch14ext_cor147FinalizedForwardLeadingCoefficient_tendsto_zero
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    Tendsto (ch14ext_cor147FinalizedForwardLeadingCoefficient F) l
      (nhds 0) := by
  let K : Real := 4 * (n : Real) ^ 3 *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos)
      A A_inv + 3)
  have h := F.gje.unit_tendsto_zero.const_mul K
  convert h using 1
  · funext t
    dsimp [ch14ext_cor147FinalizedForwardLeadingCoefficient, K]
    ring
  · simp

theorem ch14ext_cor147FinalizedForwardLeadingCoefficient_nonneg
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) (t : I) :
    0 <= ch14ext_cor147FinalizedForwardLeadingCoefficient F t := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos
  have hk := kappaInf_nonneg n hn A A_inv
  have hu := (F.gje.model t).u_nonneg
  unfold ch14ext_cor147FinalizedForwardLeadingCoefficient
  positivity

/-- Exact correction after eliminating the computed/exact norm ratio from
the actual-output forward bound.  If `C` is the printed coefficient and `rho`
the full relative computed-to-exact remainder, this is
`C^2/(1-C)+rho/(1-C)`. -/
noncomputable def ch14ext_cor147FinalizedForwardPrintedRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  let C := ch14ext_cor147FinalizedForwardLeadingCoefficient F t
  C ^ 2 / (1 - C) +
    ch14ext_cor147FinalizedForwardRelativeRemainder F t / (1 - C)

end Ch14Ext
end NumStability
