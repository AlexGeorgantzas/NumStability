-- Algorithms/Ch14GJEActualDoolittleAdapter.lean
--
-- End-to-end phase-one adapter for Algorithm 14.4.  The first Gaussian-
-- elimination phase is the literal rounded Algorithm 9.2 Doolittle loop;
-- its LU backward-error certificate is derived by Theorem 9.3 and then fed
-- to the literal second-stage/final-division family.

import NumStability.Algorithms.Ch14GJEFinalDivisionClosure
import NumStability.Algorithms.HighamChapter9DoolittleClosure

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

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

end NumStability.Ch14Ext
