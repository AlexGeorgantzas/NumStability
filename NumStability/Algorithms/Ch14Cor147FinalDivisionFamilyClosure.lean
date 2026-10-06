-- Algorithms/Ch14Cor147FinalDivisionFamilyClosure.lean
--
-- Literal family closure of Higham Corollary 14.7.  Every computed vector in
-- this file is the componentwise `fl_div` result returned by Algorithm 14.4.

import NumStability.Algorithms.Ch14GJEFinalDivisionClosure
import NumStability.Algorithms.Ch14Corollary147SourceClosure

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

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

/-- The operational LU backward certificate implies `O(u)` proximity to the
fixed exact no-pivot factors.  This is the perturbative bridge that prevents
the literal final-division endpoint from silently restricting to zero
first-stage factorization error. -/
theorem ch14ext_cor147Finalized_factorProximity_isBigO
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    Ch14MatrixFamilyIsBigO l
        (fun t i j => F.gje.L_hat t i j - F.L i j)
        (fun t => (F.gje.model t).u) /\
      Ch14MatrixFamilyIsBigO l
        (fun t i j => (F.gje.initial t).matrix i j - F.U i j)
        (fun t => (F.gje.model t).u) := by
  apply ch14ext_luBackward_factorProximity_isBigO F.gje.model A F.L F.U
    F.gje.L_hat (fun t => (F.gje.initial t).matrix)
    F.gje.unit_tendsto_zero F.gje.lu_certificate F.gje.valid_n
    F.gje.L_hat_isBigO_one F.gje.U_hat_isBigO_one F.exact_lu
  exact F.exact_lu.det_ne_zero_iff_U_diag_ne_zero.mp F.determinant_ne_zero

/-- The computed upper inverse is also `O(u)` close to the fixed exact upper
inverse, by the exact inverse-difference identity. -/
theorem ch14ext_cor147Finalized_inverseProximity_isBigO
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => F.gje.U_inv t i j - F.U_inv i j)
      (fun t => (F.gje.model t).u) := by
  let unit : I -> Real := fun t => (F.gje.model t).u
  have hUprox := (ch14ext_cor147Finalized_factorProximity_isBigO F).2
  have hfirst : Ch14MatrixFamilyIsBigO l
      (fun t => matMul n (F.gje.U_inv t)
        (fun i j => (F.gje.initial t).matrix i j - F.U i j)) unit := by
    have h := ch14ext_matrixFamily_mul_isBigO
      (M := F.gje.U_inv)
      (N := fun t i j => (F.gje.initial t).matrix i j - F.U i j)
      (f := fun _ : I => (1 : Real)) (g := unit)
      F.gje.U_inv_isBigO_one hUprox
    simpa only [one_mul] using h
  have htriple : Ch14MatrixFamilyIsBigO l
      (fun t => matMul n
        (matMul n (F.gje.U_inv t)
          (fun i j => (F.gje.initial t).matrix i j - F.U i j)) F.U_inv)
      unit := by
    have hfixed : Ch14MatrixFamilyIsBigO l
        (fun _ : I => F.U_inv) (fun _ : I => (1 : Real)) :=
      ch14ext_fixedMatrix_isBigOOne F.U_inv
    have h := ch14ext_matrixFamily_mul_isBigO
      (M := fun t => matMul n (F.gje.U_inv t)
        (fun i j => (F.gje.initial t).matrix i j - F.U i j))
      (N := fun _ : I => F.U_inv) (f := unit)
      (g := fun _ : I => (1 : Real)) hfirst hfixed
    simpa only [mul_one] using h
  intro i j
  have hneg := (htriple i j).neg_left
  convert hneg using 1
  funext t
  exact congrFun (congrFun
    (ch14ext_inverseDifference_identity n (F.gje.initial t).matrix F.U
      (F.gje.U_inv t) F.U_inv (F.gje.computed_upper_inverse t).1
      F.exact_upper_inverse.2) i) j

/-- The computed inverse product printed in (14.31). -/
noncomputable def ch14ext_cor147FinalizedPrintedX
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) (t : I) :
    Fin n -> Fin n -> Real :=
  matMul n (absMatrix n (F.gje.initial t).matrix)
    (absMatrix n (F.gje.U_inv t))

/-- The computed printed inverse product is `O(u)` close to the exact one. -/
theorem ch14ext_cor147Finalized_printedX_difference_isBigO
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => ch14ext_cor147FinalizedPrintedX F t i j -
        ch14ext_cor147WeakExactX n F.U F.U_inv i j)
      (fun t => (F.gje.model t).u) := by
  have hprox := ch14ext_cor147Finalized_factorProximity_isBigO F
  have hInv := ch14ext_cor147Finalized_inverseProximity_isBigO F
  have hUabs := ch14ext_matrixFamily_absDifference_isBigO F.U hprox.2
  have hInvabs := ch14ext_matrixFamily_absDifference_isBigO F.U_inv hInv
  have h := ch14ext_matrixFamily_productDifference_isBigO
    (M := fun t i j => |(F.gje.initial t).matrix i j|)
    (N := fun t i j => |F.gje.U_inv t i j|)
    (absMatrix n F.U) (absMatrix n F.U_inv)
    (by simpa only [absMatrix] using hUabs)
    (by simpa only [absMatrix] using hInvabs)
    (matrixFamily_abs_isBigOOne F.gje.U_inv_isBigO_one)
  simpa only [ch14ext_cor147FinalizedPrintedX,
    ch14ext_cor147WeakExactX, absMatrix] using h

/-- The residual leading object formed with the computed factors and inverse
is `O(u)` close to the exact row-dominant leading object. -/
theorem ch14ext_cor147Finalized_printedResidualLeading_difference_isBigO
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeResidualS2 n (F.gje.L_hat t)
            (ch14ext_cor147FinalizedPrintedX F t)
            (F.gje.initial t).matrix
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i -
          ch14ext_gjeResidualS2 n F.L
            (ch14ext_cor147WeakExactX n F.U F.U_inv) F.U
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i)
      (fun t => (F.gje.model t).u) := by
  let unit : I -> Real := fun t => (F.gje.model t).u
  have hprox := ch14ext_cor147Finalized_factorProximity_isBigO F
  have hPXdiff := ch14ext_cor147Finalized_printedX_difference_isBigO F
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne F.gje.output_isBigO_one
  have hUabsOne := matrixFamily_abs_isBigOOne F.gje.U_hat_isBigO_one
  have hUabsDiff := ch14ext_matrixFamily_absDifference_isBigO F.U hprox.2
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |(F.gje.initial t).matrix i j|)
        (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |(F.gje.initial t).matrix a j|)
            (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|) i -
          matMulVec n (absMatrix n F.U)
            (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |(F.gje.initial t).matrix i j|) (absMatrix n F.U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hPXOne : MatrixFamilyIsBigOOne l
      (ch14ext_cor147FinalizedPrintedX F) :=
    ch14ext_matrixFamily_mul_family_isBigOOne
      (matrixFamily_abs_isBigOOne F.gje.U_hat_isBigO_one)
      (matrixFamily_abs_isBigOOne F.gje.U_inv_isBigO_one)
  have hPXabsDiff := ch14ext_matrixFamily_absDifference_isBigO
    (ch14ext_cor147WeakExactX n F.U F.U_inv) hPXdiff
  have hPXactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n
        (fun i j => |ch14ext_cor147FinalizedPrintedX F t i j|)
        (matMulVec n (fun i j => |(F.gje.initial t).matrix i j|)
          (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|))) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne
      (matrixFamily_abs_isBigOOne hPXOne) hUactionOne
  have hPXactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |ch14ext_cor147FinalizedPrintedX F t a j|)
            (matMulVec n (fun a j => |(F.gje.initial t).matrix a j|)
              (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|)) i -
          matMulVec n
            (absMatrix n (ch14ext_cor147WeakExactX n F.U F.U_inv))
            (matMulVec n (absMatrix n F.U)
              (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|)) i) unit :=
    ch14ext_matrixVectorFamily_productDifference_isBigO
      (M := fun t i j => |ch14ext_cor147FinalizedPrintedX F t i j|)
      (A := absMatrix n (ch14ext_cor147WeakExactX n F.U F.U_inv))
      (x := fun t => matMulVec n (fun i j => |(F.gje.initial t).matrix i j|)
        (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|))
      (y := fun t => matMulVec n (absMatrix n F.U)
        (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|))
      (by simpa only [absMatrix] using hPXabsDiff) hUactionDiff hUactionOne
  have hLabsDiff := ch14ext_matrixFamily_absDifference_isBigO F.L hprox.1
  have hfinal := ch14ext_matrixVectorFamily_productDifference_isBigO
    (M := fun t i j => |F.gje.L_hat t i j|) (A := absMatrix n F.L)
    (x := fun t => matMulVec n
      (fun i j => |ch14ext_cor147FinalizedPrintedX F t i j|)
      (matMulVec n (fun i j => |(F.gje.initial t).matrix i j|)
        (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|)))
    (y := fun t => matMulVec n
      (absMatrix n (ch14ext_cor147WeakExactX n F.U F.U_inv))
      (matMulVec n (absMatrix n F.U)
        (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|)))
    (by simpa only [absMatrix] using hLabsDiff) hPXactionDiff hPXactionOne
  simpa only [ch14ext_gjeResidualS2, absMatrix, absVec] using hfinal

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

theorem ch14ext_cor147FinalizedResidualLeadingCorrection_family_isBigO_u
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) (i : Fin n) :
    (fun t => ch14ext_cor147FinalizedResidualLeadingCorrection F t i)
      =O[l] (fun t => (F.gje.model t).u) := by
  simpa only [ch14ext_cor147FinalizedResidualLeadingCorrection,
    Real.norm_eq_abs] using
    (ch14ext_cor147Finalized_printedResidualLeading_difference_isBigO F i).norm_left

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

/-- The literal (14.31) terminal remainder is componentwise `O(u^2)`. -/
theorem ch14ext_cor147FinalizedResidualRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) (i : Fin n) :
    (fun t => ch14ext_cor147FinalizedResidualRemainder F t i)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  let unit : I -> Real := fun t => (F.gje.model t).u
  have hu : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hlead :=
    ch14ext_cor147FinalizedResidualLeadingCorrection_family_isBigO_u F i
  have hscaled : (fun t => 8 * (n : Real) * unit t *
      ch14ext_cor147FinalizedResidualLeadingCorrection F t i)
      =O[l] (fun t => unit t ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (hu.mul hlead).const_mul_left (8 * (n : Real))
  have hterminal : (fun t => ch14ext_cor147FinalizedResidualTerminal F t i)
      =O[l] (fun t => unit t ^ 2) := by
    simpa only [ch14ext_cor147FinalizedResidualTerminal, unit] using
      (ch14ext_gjeFinalizedFamily_theorem14_5_endpoint F.gje A_inv x
        F.source_inverse.1 F.exact_solution).2.1 i
  simpa only [ch14ext_cor147FinalizedResidualRemainder, unit] using
    hscaled.add hterminal

/-- Printed rowwise Corollary 14.7 residual bound for the actual returned
vector.  The named remainder includes both the actual (14.31) terminal and
the computed-to-exact factor transfer. -/
theorem ch14ext_cor147Finalized_residual_bound
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    forall t i,
      |b i - matMulVec n A (ch14ext_gjeFinalizedFamilyOutput F.gje t) i| <=
        32 * (n : Real) ^ 2 * (F.gje.model t).u *
            (Finset.univ.sum (fun j : Fin n => |A i j|)) *
            (Finset.univ.sum (fun j : Fin n =>
              |ch14ext_gjeFinalizedFamilyOutput F.gje t j|)) +
          ch14ext_cor147FinalizedResidualRemainder F t i := by
  intro t i
  let xhat := ch14ext_gjeFinalizedFamilyOutput F.gje t
  let computed := ch14ext_gjeResidualS2 n (F.gje.L_hat t)
    (ch14ext_cor147FinalizedPrintedX F t) (F.gje.initial t).matrix xhat i
  let exact := ch14ext_gjeResidualS2 n F.L
    (ch14ext_cor147WeakExactX n F.U F.U_inv) F.U xhat i
  have hraw :=
    (ch14ext_gjeFinalizedFamily_theorem14_5_endpoint F.gje A_inv x
      F.source_inverse.1 F.exact_solution).1 t i
  have hreplace : computed <= exact + |computed - exact| := by
    linarith [le_abs_self (computed - exact)]
  have hcoef : 0 <= 8 * (n : Real) * (F.gje.model t).u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (F.gje.model t).u_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hreplace hcoef
  have hURow := ch14ext_exactNoPivotLU_upper_higham8_8 A F.L F.U
    F.row_diag_dominant F.determinant_ne_zero F.exact_lu
  have hlead := ch14ext_cor147_residual_leading_object_le
    n (F.gje.model t) A F.L F.U F.U_inv xhat F.exact_lu hURow
      F.exact_upper_inverse i
  calc
    |b i - matMulVec n A (ch14ext_gjeFinalizedFamilyOutput F.gje t) i| <=
        8 * (n : Real) * (F.gje.model t).u * computed +
          ch14ext_cor147FinalizedResidualTerminal F t i := by
      simpa only [computed, xhat, ch14ext_cor147FinalizedPrintedX,
        ch14ext_cor147FinalizedResidualTerminal] using hraw
    _ <= 8 * (n : Real) * (F.gje.model t).u *
          (exact + |computed - exact|) +
          ch14ext_cor147FinalizedResidualTerminal F t i :=
      add_le_add hscaled (le_refl _)
    _ = 8 * (n : Real) * (F.gje.model t).u * exact +
          ch14ext_cor147FinalizedResidualRemainder F t i := by
      simp only [ch14ext_cor147FinalizedResidualRemainder,
        ch14ext_cor147FinalizedResidualLeadingCorrection, computed, exact,
        xhat]
      ring
    _ <= 32 * (n : Real) ^ 2 * (F.gje.model t).u *
            (Finset.univ.sum (fun j : Fin n => |A i j|)) *
            (Finset.univ.sum (fun j : Fin n =>
              |ch14ext_gjeFinalizedFamilyOutput F.gje t j|)) +
          ch14ext_cor147FinalizedResidualRemainder F t i := by
      simpa only [exact, xhat, ch14ext_cor147WeakExactX, add_comm] using
        add_le_add_right hlead
          (ch14ext_cor147FinalizedResidualRemainder F t i)

/-- Family-level literal residual closure of Corollary 14.7. -/
theorem ch14ext_cor147Finalized_residual_vanishing_family_endpoint
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    (forall t i,
      |b i - matMulVec n A (ch14ext_gjeFinalizedFamilyOutput F.gje t) i| <=
        32 * (n : Real) ^ 2 * (F.gje.model t).u *
            (Finset.univ.sum (fun j : Fin n => |A i j|)) *
            (Finset.univ.sum (fun j : Fin n =>
              |ch14ext_gjeFinalizedFamilyOutput F.gje t j|)) +
          ch14ext_cor147FinalizedResidualRemainder F t i) /\
      forall i, (fun t => ch14ext_cor147FinalizedResidualRemainder F t i)
        =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  exact ⟨ch14ext_cor147Finalized_residual_bound F,
    ch14ext_cor147FinalizedResidualRemainder_family_isBigO_u_sq F⟩

/-! ## Computed-to-exact transfer for the (14.32) leading objects -/

theorem ch14ext_cor147Finalized_forwardT1_difference_isBigO
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeForwardT1 n A_inv (F.gje.L_hat t)
            (F.gje.initial t).matrix
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i -
          ch14ext_gjeForwardT1 n A_inv F.L F.U
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i)
      (fun t => (F.gje.model t).u) := by
  let unit : I -> Real := fun t => (F.gje.model t).u
  have hprox := ch14ext_cor147Finalized_factorProximity_isBigO F
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne F.gje.output_isBigO_one
  have hUabsOne := matrixFamily_abs_isBigOOne F.gje.U_hat_isBigO_one
  have hUabsDiff := ch14ext_matrixFamily_absDifference_isBigO F.U hprox.2
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |(F.gje.initial t).matrix i j|)
        (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |(F.gje.initial t).matrix a j|)
            (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|) i -
          matMulVec n (absMatrix n F.U)
            (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |(F.gje.initial t).matrix i j|) (absMatrix n F.U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hLabsOne := matrixFamily_abs_isBigOOne F.gje.L_hat_isBigO_one
  have hLabsDiff := ch14ext_matrixFamily_absDifference_isBigO F.L hprox.1
  have hLactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |F.gje.L_hat t i j|)
        (matMulVec n (fun i j => |(F.gje.initial t).matrix i j|)
          (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|))) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hLabsOne hUactionOne
  have hLactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |F.gje.L_hat t a j|)
            (matMulVec n (fun a j => |(F.gje.initial t).matrix a j|)
              (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|)) i -
          matMulVec n (absMatrix n F.L)
            (matMulVec n (absMatrix n F.U)
              (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|)) i) unit :=
    ch14ext_matrixVectorFamily_productDifference_isBigO
      (M := fun t i j => |F.gje.L_hat t i j|) (A := absMatrix n F.L)
      (x := fun t => matMulVec n (fun i j => |(F.gje.initial t).matrix i j|)
        (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|))
      (y := fun t => matMulVec n (absMatrix n F.U)
        (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|))
      (by simpa only [absMatrix] using hLabsDiff) hUactionDiff hUactionOne
  have hfinal := ch14ext_fixedMatrix_vectorDifference_isBigO
    (absMatrix n A_inv) hLactionDiff
  simpa only [ch14ext_gjeForwardT1, absMatrix, absVec] using hfinal

theorem ch14ext_cor147Finalized_forwardT2_difference_isBigO
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeForwardT2 n (absMatrix n (F.gje.U_inv t))
            (F.gje.initial t).matrix
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i -
          ch14ext_gjeForwardT2 n (absMatrix n F.U_inv) F.U
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i)
      (fun t => (F.gje.model t).u) := by
  let unit : I -> Real := fun t => (F.gje.model t).u
  have hprox := ch14ext_cor147Finalized_factorProximity_isBigO F
  have hInv := ch14ext_cor147Finalized_inverseProximity_isBigO F
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne F.gje.output_isBigO_one
  have hUabsOne := matrixFamily_abs_isBigOOne F.gje.U_hat_isBigO_one
  have hUabsDiff := ch14ext_matrixFamily_absDifference_isBigO F.U hprox.2
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |(F.gje.initial t).matrix i j|)
        (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |(F.gje.initial t).matrix a j|)
            (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|) i -
          matMulVec n (absMatrix n F.U)
            (fun j => |ch14ext_gjeFinalizedFamilyOutput F.gje t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |(F.gje.initial t).matrix i j|) (absMatrix n F.U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hInvAbsDiff := ch14ext_matrixFamily_absDifference_isBigO F.U_inv hInv
  have hfinal := ch14ext_matrixVectorFamily_productDifference_isBigO
    (M := fun t i j => |F.gje.U_inv t i j|) (A := absMatrix n F.U_inv)
    (x := fun t => matMulVec n (fun i j => |(F.gje.initial t).matrix i j|)
      (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|))
    (y := fun t => matMulVec n (absMatrix n F.U)
      (fun i => |ch14ext_gjeFinalizedFamilyOutput F.gje t i|))
    (by simpa only [absMatrix] using hInvAbsDiff) hUactionDiff hUactionOne
  simpa only [ch14ext_gjeForwardT2, absMatrix, absVec] using hfinal

theorem ch14ext_cor147Finalized_forwardCore_difference_isBigO
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        (ch14ext_gjeForwardT1 n A_inv (F.gje.L_hat t)
            (F.gje.initial t).matrix
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n (F.gje.U_inv t))
            (F.gje.initial t).matrix
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i) -
        (ch14ext_gjeForwardT1 n A_inv F.L F.U
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n F.U_inv) F.U
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i))
      (fun t => (F.gje.model t).u) := by
  intro i
  have h1 := ch14ext_cor147Finalized_forwardT1_difference_isBigO F i
  have h2 := ch14ext_cor147Finalized_forwardT2_difference_isBigO F i
  have h := h1.add (h2.const_mul_left (3 : Real))
  convert h using 1
  funext t
  ring

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

/-- The relative infinity norm of the literal (14.32) terminal vector is
`O(u^2)`. -/
theorem ch14ext_cor147FinalizedForwardRelativeTerminal_family_isBigO_u_sq
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor147FinalizedForwardRelativeTerminal F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  have hvec : Ch14VectorFamilyIsBigO l
      (fun t i => ch14ext_cor147FinalizedForwardTerminalVector F t i)
      (fun t => (F.gje.model t).u ^ 2) := by
    intro i
    simpa only [ch14ext_cor147FinalizedForwardTerminalVector] using
      (ch14ext_gjeFinalizedFamily_theorem14_5_endpoint F.gje A_inv x
        F.source_inverse.1 F.exact_solution).2.2.2 i
  have hnorm := ch14ext_vectorFamily_infNorm_isBigO hvec
  have hscaled := hnorm.const_mul_left (infNormVec x)⁻¹
  simpa only [ch14ext_cor147FinalizedForwardRelativeTerminal,
    div_eq_mul_inv, mul_comm] using hscaled

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

theorem ch14ext_cor147FinalizedForwardVectorRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    Ch14VectorFamilyIsBigO l
      (ch14ext_cor147FinalizedForwardVectorRemainder F)
      (fun t => (F.gje.model t).u ^ 2) := by
  let unit : I -> Real := fun t => (F.gje.model t).u
  have hu : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hcore := ch14ext_cor147Finalized_forwardCore_difference_isBigO F
  intro i
  have hscaled := (hu.mul (hcore i)).const_mul_left (2 * (n : Real))
  have hlead : (fun t => 2 * (n : Real) * unit t *
      ((ch14ext_gjeForwardT1 n A_inv (F.gje.L_hat t)
          (F.gje.initial t).matrix
          (ch14ext_gjeFinalizedFamilyOutput F.gje t) i +
        3 * ch14ext_gjeForwardT2 n (absMatrix n (F.gje.U_inv t))
          (F.gje.initial t).matrix
          (ch14ext_gjeFinalizedFamilyOutput F.gje t) i) -
       (ch14ext_gjeForwardT1 n A_inv F.L F.U
          (ch14ext_gjeFinalizedFamilyOutput F.gje t) i +
        3 * ch14ext_gjeForwardT2 n (absMatrix n F.U_inv) F.U
          (ch14ext_gjeFinalizedFamilyOutput F.gje t) i)))
      =O[l] (fun t => unit t ^ 2) := by
    simpa only [pow_two, mul_assoc] using hscaled
  have hterminal : (fun t =>
      ch14ext_cor147FinalizedForwardTerminalVector F t i)
      =O[l] (fun t => unit t ^ 2) := by
    simpa only [ch14ext_cor147FinalizedForwardTerminalVector, unit] using
      (ch14ext_gjeFinalizedFamily_theorem14_5_endpoint F.gje A_inv x
        F.source_inverse.1 F.exact_solution).2.2.2 i
  simpa only [ch14ext_cor147FinalizedForwardVectorRemainder, unit] using
    hlead.add hterminal

/-- Relative infinity norm of the full computed-to-exact forward remainder. -/
noncomputable def ch14ext_cor147FinalizedForwardRelativeRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  infNormVec (ch14ext_cor147FinalizedForwardVectorRemainder F t) /
    infNormVec x

theorem ch14ext_cor147FinalizedForwardRelativeRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor147FinalizedForwardRelativeRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  have hnorm := ch14ext_vectorFamily_infNorm_isBigO
    (ch14ext_cor147FinalizedForwardVectorRemainder_family_isBigO_u_sq F)
  have hscaled := hnorm.const_mul_left (infNormVec x)⁻¹
  simpa only [ch14ext_cor147FinalizedForwardRelativeRemainder,
    div_eq_mul_inv, mul_comm] using hscaled

/-- Intermediate forward bound with the actual-output norm ratio.  Its
leading coefficient is obtained from the fixed exact row-dominant factors;
all computed-factor effects are in the explicit quadratic remainder. -/
theorem ch14ext_cor147Finalized_forward_bound
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    forall t,
      infNormVec (fun i =>
          x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.gje.model t).u *
            (kappaInf n
              (lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos)
              A A_inv + 3) *
            (infNormVec (ch14ext_gjeFinalizedFamilyOutput F.gje t) /
              infNormVec x) +
          ch14ext_cor147FinalizedForwardRelativeRemainder F t := by
  intro t
  let xhat := ch14ext_gjeFinalizedFamilyOutput F.gje t
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos
  have hraw :=
    (ch14ext_gjeFinalizedFamily_theorem14_5_endpoint F.gje A_inv x
      F.source_inverse.1 F.exact_solution).2.2.1 t
  have hURow := ch14ext_exactNoPivotLU_upper_higham8_8 A F.L F.U
    F.row_diag_dominant F.determinant_ne_zero F.exact_lu
  have hFactProduct : LUFactSpec n
      (ch14ext_cor147ComputedProduct n F.L F.U) F.L F.U := {
    L_diag := F.exact_lu.L_diag
    L_upper_zero := F.exact_lu.L_upper_zero
    U_lower_zero := F.exact_lu.U_lower_zero
    product_eq := by intro i j; rfl
  }
  have hProductEq : ch14ext_cor147ComputedProduct n F.L F.U = A := by
    funext i j
    simpa only [ch14ext_cor147ComputedProduct, matMul] using
      F.exact_lu.product_eq i j
  have hProductNorm :
      infNorm (ch14ext_cor147ComputedProduct n F.L F.U) <=
        infNorm A / (1 : Real) := by
    rw [hProductEq, div_one]
  have hExactLead := ch14ext_cor147_forward_leading_infNorm_le
    n (F.gje.model t) hn A A_inv F.L F.U F.U_inv xhat hFactProduct
      hURow F.exact_upper_inverse (1 : Real) zero_lt_one hProductNorm
  let exactLead : Fin n -> Real := fun i =>
    2 * (n : Real) * (F.gje.model t).u *
        ch14ext_gjeForwardT1 n A_inv F.L F.U xhat i +
      6 * (n : Real) * (F.gje.model t).u *
        ch14ext_gjeForwardT2 n (absMatrix n F.U_inv) F.U xhat i
  let rem : Fin n -> Real := fun i =>
    ch14ext_cor147FinalizedForwardVectorRemainder F t i
  have hpoint : forall i, |x i - xhat i| <= exactLead i + rem i := by
    intro i
    calc
      |x i - xhat i| <=
          2 * (n : Real) * (F.gje.model t).u *
              (ch14ext_gjeForwardT1 n A_inv (F.gje.L_hat t)
                  (F.gje.initial t).matrix xhat i +
                3 * ch14ext_gjeForwardT2 n
                  (absMatrix n (F.gje.U_inv t))
                  (F.gje.initial t).matrix xhat i) +
            ch14ext_cor147FinalizedForwardTerminalVector F t i := by
        simpa only [xhat, ch14ext_cor147FinalizedForwardTerminalVector,
          mul_add, mul_assoc] using hraw i
      _ = exactLead i + rem i := by
        dsimp [exactLead, rem]
        unfold ch14ext_cor147FinalizedForwardVectorRemainder
        ring
  have hnormSplit : infNormVec (fun i => x i - xhat i) <=
      infNormVec exactLead + infNormVec rem := by
    apply infNormVec_le_of_abs_le
    · intro i
      calc
        |x i - xhat i| <= exactLead i + rem i := hpoint i
        _ <= |exactLead i| + |rem i| :=
          add_le_add (le_abs_self _) (le_abs_self _)
        _ <= infNormVec exactLead + infNormVec rem :=
          add_le_add (abs_le_infNormVec exactLead i) (abs_le_infNormVec rem i)
    · exact add_nonneg (infNormVec_nonneg exactLead) (infNormVec_nonneg rem)
  have hlead : infNormVec exactLead <=
      4 * (n : Real) ^ 3 * (F.gje.model t).u *
        (kappaInf n hn A A_inv + 3) * infNormVec xhat := by
    simpa only [exactLead, div_one] using hExactLead
  have hnorm : infNormVec (fun i => x i - xhat i) <=
      4 * (n : Real) ^ 3 * (F.gje.model t).u *
          (kappaInf n hn A A_inv + 3) * infNormVec xhat +
        infNormVec rem :=
    le_trans hnormSplit (add_le_add hlead (le_refl _))
  calc
    infNormVec (fun i =>
        x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) / infNormVec x <=
        (4 * (n : Real) ^ 3 * (F.gje.model t).u *
            (kappaInf n hn A A_inv + 3) * infNormVec xhat +
          infNormVec rem) / infNormVec x := by
      simpa only [xhat] using
        div_le_div_of_nonneg_right hnorm F.exact_solution_nonzero.le
    _ = 4 * (n : Real) ^ 3 * (F.gje.model t).u *
            (kappaInf n hn A A_inv + 3) *
            (infNormVec (ch14ext_gjeFinalizedFamilyOutput F.gje t) /
              infNormVec x) +
          ch14ext_cor147FinalizedForwardRelativeRemainder F t := by
      rw [add_div]
      unfold ch14ext_cor147FinalizedForwardRelativeRemainder
      dsimp [rem, xhat]
      ring

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

/-- The denominator correction and the rescaled full forward remainder are
together `O(u^2)`. -/
theorem ch14ext_cor147FinalizedForwardPrintedRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor147FinalizedForwardPrintedRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  let unit : I -> Real := fun t => (F.gje.model t).u
  let C : I -> Real := ch14ext_cor147FinalizedForwardLeadingCoefficient F
  let rho : I -> Real := fun t =>
    ch14ext_cor147FinalizedForwardRelativeRemainder F t
  let K : Real := 4 * (n : Real) ^ 3 *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos)
      A A_inv + 3)
  have hCeq : C = fun t => K * unit t := by
    funext t
    dsimp [C, K, unit, ch14ext_cor147FinalizedForwardLeadingCoefficient]
    ring
  have hunit : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hC : C =O[l] unit := by
    rw [hCeq]
    exact hunit.const_mul_left K
  have hCsq : (fun t => C t ^ 2) =O[l] (fun t => unit t ^ 2) := by
    simpa only [pow_two] using hC.mul hC
  have hCzero : Tendsto C l (nhds 0) := by
    simpa only [C] using
      ch14ext_cor147FinalizedForwardLeadingCoefficient_tendsto_zero F
  have hden : Tendsto (fun t => 1 - C t) l (nhds 1) := by
    simpa using hCzero.const_sub 1
  have hinvOne : (fun t => (1 - C t)⁻¹) =O[l]
      (fun _ : I => (1 : Real)) := by
    have hinv : Tendsto (fun t => (1 - C t)⁻¹) l (nhds (1 : Real)) := by
      simpa using hden.inv₀ one_ne_zero
    exact hinv.isBigO_one Real
  have hterm1 : (fun t => C t ^ 2 / (1 - C t)) =O[l]
      (fun t => unit t ^ 2) := by
    simpa only [div_eq_mul_inv, mul_one] using hCsq.mul hinvOne
  have hrho : rho =O[l] (fun t => unit t ^ 2) := by
    simpa only [rho, unit] using
      ch14ext_cor147FinalizedForwardRelativeRemainder_family_isBigO_u_sq F
  have hterm2 : (fun t => rho t / (1 - C t)) =O[l]
      (fun t => unit t ^ 2) := by
    simpa only [div_eq_mul_inv, mul_one] using hrho.mul hinvOne
  simpa only [ch14ext_cor147FinalizedForwardPrintedRemainder,
    C, rho, unit] using hterm1.add hterm2

/-- Ratio-free printed forward bound whenever the leading coefficient is
below one. -/
theorem ch14ext_cor147Finalized_forward_printed_bound_of_coefficient_lt_one
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x)
    (t : I)
    (hsmall : ch14ext_cor147FinalizedForwardLeadingCoefficient F t < 1) :
    infNormVec (fun i =>
        x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) / infNormVec x <=
      4 * (n : Real) ^ 3 * (F.gje.model t).u *
          (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos)
            A A_inv + 3) +
        ch14ext_cor147FinalizedForwardPrintedRemainder F t := by
  let xhat := ch14ext_gjeFinalizedFamilyOutput F.gje t
  let e : Real := infNormVec (fun i => x i - xhat i) / infNormVec x
  let ratio : Real := infNormVec xhat / infNormVec x
  let rho : Real := ch14ext_cor147FinalizedForwardRelativeRemainder F t
  let C : Real := ch14ext_cor147FinalizedForwardLeadingCoefficient F t
  have hbase : e <= C * ratio + rho := by
    simpa only [e, ratio, rho, C, xhat,
      ch14ext_cor147FinalizedForwardLeadingCoefficient] using
      ch14ext_cor147Finalized_forward_bound F t
  have hratio : ratio <= 1 + e := by
    dsimp only [ratio, e]
    apply (div_le_iff₀ F.exact_solution_nonzero).2
    calc
      infNormVec xhat <=
          infNormVec x + infNormVec (fun i => x i - xhat i) :=
        ch14ext_infNormVec_approx_le_exact_add_error x xhat
      _ = (1 + infNormVec (fun i => x i - xhat i) / infNormVec x) *
          infNormVec x := by
        field_simp [F.exact_solution_nonzero.ne']
  have hCnonneg : 0 <= C := by
    exact ch14ext_cor147FinalizedForwardLeadingCoefficient_nonneg F t
  have hraw : e <= C * (1 + e) + rho := by
    exact le_trans hbase
      (add_le_add (mul_le_mul_of_nonneg_left hratio hCnonneg) (le_refl rho))
  have hdenpos : 0 < 1 - C := sub_pos.mpr hsmall
  have hmult : e * (1 - C) <= C + rho := by
    nlinarith [hraw]
  have hdiv : e <= (C + rho) / (1 - C) :=
    (le_div_iff₀ hdenpos).2 hmult
  have hdecomp : (C + rho) / (1 - C) =
      C + (C ^ 2 / (1 - C) + rho / (1 - C)) := by
    field_simp [ne_of_gt hdenpos]
    ring
  calc
    infNormVec (fun i =>
        x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) /
        infNormVec x = e := rfl
    _ <= (C + rho) / (1 - C) := hdiv
    _ = C + (C ^ 2 / (1 - C) + rho / (1 - C)) := hdecomp
    _ = 4 * (n : Real) ^ 3 * (F.gje.model t).u *
          (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos)
            A A_inv + 3) +
        ch14ext_cor147FinalizedForwardPrintedRemainder F t := by
      rfl

/-- Along a vanishing-roundoff family the bootstrap condition `C(u)<1`
holds eventually, so the printed coefficient contains no computed/exact norm
ratio. -/
theorem ch14ext_cor147Finalized_forward_printed_eventually
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    ∀ᶠ t in l,
      infNormVec (fun i =>
          x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.gje.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147FinalizedForwardPrintedRemainder F t := by
  have hzero :=
    ch14ext_cor147FinalizedForwardLeadingCoefficient_tendsto_zero F
  have hsmall : ∀ᶠ t in l,
      ch14ext_cor147FinalizedForwardLeadingCoefficient F t < 1 :=
    (tendsto_order.1 hzero).2 1 zero_lt_one
  filter_upwards [hsmall] with t ht
  exact
    ch14ext_cor147Finalized_forward_printed_bound_of_coefficient_lt_one F t ht

/-- Family-level ratio-free forward closure of Corollary 14.7. -/
theorem ch14ext_cor147Finalized_forward_vanishing_family_endpoint
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    (∀ᶠ t in l,
      infNormVec (fun i =>
          x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.gje.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147FinalizedForwardPrintedRemainder F t) /\
      (fun t => ch14ext_cor147FinalizedForwardPrintedRemainder F t)
        =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  exact ⟨ch14ext_cor147Finalized_forward_printed_eventually F,
    ch14ext_cor147FinalizedForwardPrintedRemainder_family_isBigO_u_sq F⟩

/-- **Higham Corollary 14.7, literal actual-output family endpoint.**
Both printed estimates use the componentwise `fl_div` result.  Their named
remainders contain the actual (14.31)/(14.32) terminals and the derived
`u * O(u)` transfer from computed factors to fixed exact row-dominant factors;
the forward remainder also contains the exact bootstrap correction.  Both
remainders are proved `O(u^2)`. -/
theorem ch14ext_cor147Finalized_vanishing_family_endpoint
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x) :
    ((forall t i,
      |b i - matMulVec n A (ch14ext_gjeFinalizedFamilyOutput F.gje t) i| <=
        32 * (n : Real) ^ 2 * (F.gje.model t).u *
            (Finset.univ.sum (fun j : Fin n => |A i j|)) *
            (Finset.univ.sum (fun j : Fin n =>
              |ch14ext_gjeFinalizedFamilyOutput F.gje t j|)) +
          ch14ext_cor147FinalizedResidualRemainder F t i) /\
      forall i, (fun t => ch14ext_cor147FinalizedResidualRemainder F t i)
        =O[l] (fun t => (F.gje.model t).u ^ 2)) /\
    ((∀ᶠ t in l,
      infNormVec (fun i =>
          x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.gje.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.gje.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147FinalizedForwardPrintedRemainder F t) /\
      (fun t => ch14ext_cor147FinalizedForwardPrintedRemainder F t)
        =O[l] (fun t => (F.gje.model t).u ^ 2)) := by
  exact ⟨ch14ext_cor147Finalized_residual_vanishing_family_endpoint F,
    ch14ext_cor147Finalized_forward_vanishing_family_endpoint F⟩

end NumStability.Ch14Ext
