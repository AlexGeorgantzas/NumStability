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
import NumStability.Source.Higham.Chapter09.DoolittleClosure
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
import NumStability.Source.Higham.Chapter14.Problem15

/-!
# Chapter14 Algorithm04 Execution GJEActualDoolittleAdapter

Canonical destination for material split out of
`NumStability.Algorithms.Ch14GJEActualDoolittleAdapter` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- The computed lower factor produced by the literal square Algorithm 9.2
loop used as phase one of Algorithm 14.4. -/
noncomputable def ch14ext_gjeActualDoolittleL {n : Nat}
    (fp : FPModel) (A : Fin n -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A

/-- The computed upper factor produced by the literal square Algorithm 9.2
loop used as phase one of Algorithm 14.4. -/
noncomputable def ch14ext_gjeActualDoolittleU {n : Nat}
    (fp : FPModel) (A : Fin n -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A

/-- The actual state handed from rounded Doolittle elimination and rounded
forward substitution to Algorithm 14.4's second phase. -/
noncomputable def ch14ext_gjeActualDoolittleInitial {n : Nat}
    (fp : FPModel) (A : Fin n -> Fin n -> Real) (b : Fin n -> Real) :
    Ch14GJEState n where
  matrix := ch14ext_gjeActualDoolittleU fp A
  rhs := fl_forwardSub fp n (ch14ext_gjeActualDoolittleL fp A) b

@[simp] theorem ch14ext_gjeActualDoolittleInitial_matrix {n : Nat}
    (fp : FPModel) (A : Fin n -> Fin n -> Real) (b : Fin n -> Real) :
    (ch14ext_gjeActualDoolittleInitial fp A b).matrix =
      ch14ext_gjeActualDoolittleU fp A := by
  rfl

@[simp] theorem ch14ext_gjeActualDoolittleInitial_rhs {n : Nat}
    (fp : FPModel) (A : Fin n -> Fin n -> Real) (b : Fin n -> Real) :
    (ch14ext_gjeActualDoolittleInitial fp A b).rhs =
      fl_forwardSub fp n (ch14ext_gjeActualDoolittleL fp A) b := by
  rfl

/-- Constructor for an operational Algorithm 14.4 family whose first stage
is not an abstract LU certificate: `L_hat`, `U_hat`, and the forward RHS are
definitionally the literal rounded Doolittle/forward-substitution executors,
and `lu_certificate` is proved by the executable Theorem 9.3 endpoint.

The remaining hypotheses are successful-run conditions (nonzero pivots and
inverse/solve witnesses) plus local boundedness used by the family-level
Landau statements.  None is a residual or forward-error conclusion. -/
noncomputable def ch14ext_gjeFinalizedFamily_of_actualDoolittle
    {I : Type*} {l : Filter I} {n : Nat}
    (model : I -> FPModel) (A : Fin n -> Fin n -> Real)
    (b : Fin n -> Real)
    (U_inv : I -> Fin n -> Fin n -> Real)
    (z : I -> Fin n -> Real)
    (hunit : Tendsto (fun t => (model t).u) l (nhds 0))
    (hvalid_n : forall t, gammaValid (model t) n)
    (hvalid_one : forall t, gammaValid (model t) 1)
    (hvalid_three : forall t, gammaValid (model t) 3)
    (hn : 1 <= n)
    (hUdiag : forall t k, ch14ext_gjeActualDoolittleU (model t) A k k ≠ 0)
    (hpivots : forall t q, (hq : q < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix (model t) 1
        (ch14ext_gjeActualDoolittleInitial (model t) A b) (1 + q)
        ⟨1 + q, by omega⟩ ⟨1 + q, by omega⟩ ≠ 0)
    (hinverse : forall t, IsInverse n
      (ch14ext_gjeActualDoolittleU (model t) A) (U_inv t))
    (hsolve : forall t i,
      matMulVec n (ch14ext_gjeActualDoolittleU (model t) A) (z t) i =
        fl_forwardSub (model t) n
          (ch14ext_gjeActualDoolittleL (model t) A) b i)
    (hLone : MatrixFamilyIsBigOOne l
      (fun t => ch14ext_gjeActualDoolittleL (model t) A))
    (hUone : MatrixFamilyIsBigOOne l
      (fun t => ch14ext_gjeActualDoolittleU (model t) A))
    (hXone : MatrixFamilyIsBigOOne l (fun t =>
      ch14ext_gjeFinalizedSourceXabs (model t)
        (ch14ext_gjeActualDoolittleInitial (model t) A b)))
    (hPone : MatrixFamilyIsBigOOne l (fun t =>
      ch14ext_gjeNormalizedPabs n
        (ch14ext_gjeBeforeFinalDivision (model t)
          (ch14ext_gjeActualDoolittleInitial (model t) A b)).matrix
        (ch14ext_gjeFinalizedSourcePabs (model t)
          (ch14ext_gjeActualDoolittleInitial (model t) A b))))
    (hyone : VectorFamilyIsBigOOne l (fun t =>
      fl_forwardSub (model t) n
        (ch14ext_gjeActualDoolittleL (model t) A) b))
    (houtone : VectorFamilyIsBigOOne l (fun t =>
      ch14ext_gjeFinalizedDivOutput (model t)
        (ch14ext_gjeActualDoolittleInitial (model t) A b)))
    (hUinvone : MatrixFamilyIsBigOOne l U_inv)
    (hzone : VectorFamilyIsBigOOne l z) :
    Ch14GJEFinalizedFamily I l n A b where
  model := model
  L_hat := fun t => ch14ext_gjeActualDoolittleL (model t) A
  initial := fun t => ch14ext_gjeActualDoolittleInitial (model t) A b
  U_inv := U_inv
  z := z
  unit_tendsto_zero := hunit
  lu_certificate := fun t => by
    simpa [ch14ext_gjeActualDoolittleL, ch14ext_gjeActualDoolittleU,
      ch14ext_gjeActualDoolittleInitial] using
      higham9_3_rectRoundedLoop_square_to_LUBackwardError_source
        (model t) A (by
          simpa [ch14ext_gjeActualDoolittleU] using hUdiag t) (hvalid_n t)
  valid_n := hvalid_n
  valid_one := hvalid_one
  valid_three := hvalid_three
  dimension_pos := hn
  diagonal_nonzero := hUdiag
  forward_start := fun _ => rfl
  pivots_nonzero := hpivots
  computed_upper_inverse := hinverse
  upper_solve := hsolve
  L_hat_isBigO_one := hLone
  U_hat_isBigO_one := hUone
  source_Xabs_isBigO_one := hXone
  normalized_Pabs_isBigO_one := hPone
  y_isBigO_one := hyone
  output_isBigO_one := houtone
  U_inv_isBigO_one := hUinvone
  z_isBigO_one := hzone

end Ch14Ext
end NumStability
