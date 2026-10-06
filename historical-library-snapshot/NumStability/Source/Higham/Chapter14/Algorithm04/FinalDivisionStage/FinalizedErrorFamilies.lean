import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.Closure
import NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEAsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEFinalDivisionClosure

/-!
# FinalizedErrorFamilies

Canonical destination for the Chapter14.Algorithm04 declarations relocated from the
historical path `NumStability.Algorithms.Ch14GJEFinalDivisionClosure` during wave R08.
Holds 14 declaration(s): 14 public.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open Filter Asymptotics
open Finset BigOperators
open scoped Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- The additional final-division residual remainder is genuinely `O(u²)`.
This is the analytic bridge needed before specializing (14.31) to Corollaries
14.6 and 14.7. -/
theorem ch14ext_gjeResidualFinalDivisionHigherOrder_family_isBigO
    {ι : Type*} {l : Filter ι} (n : Nat) (fp : ι -> FPModel)
    (L X U : ι -> Fin n -> Fin n -> Real)
    (y xhat : ι -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (nhds 0))
    (hL : MatrixFamilyIsBigOOne l L) (hX : MatrixFamilyIsBigOOne l X)
    (hU : MatrixFamilyIsBigOOne l U)
    (hy : VectorFamilyIsBigOOne l y)
    (hx : VectorFamilyIsBigOOne l xhat) (i : Fin n) :
    (fun t => ch14ext_gjeResidualFinalDivisionHigherOrder n (fp t)
      (L t) (X t) (U t) (y t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hbase := ch14ext_gjeResidualHigherOrder_family_isBigO
    n fp L X U y xhat hu hL hX hU hy hx i
  have hgn := ch14ext_gamma_family_isBigO_unit n fp hu
  have hg1 := ch14ext_gamma_family_isBigO_unit 1 fp hu
  have hgr1 := ch14ext_gammaRem_family_isBigO_unit_sq 1 fp hu
  have hc := ch14ext_gje_c3_family_isBigO_unit n fp hu
  have huOne : (fun t => (fp t).u) =O[l] (fun _ : ι => (1 : Real)) :=
    hu.isBigO_one Real
  have hgnOne := hgn.trans huOne
  have hg1One := hg1.trans huOne
  have hone : (fun _ : ι => (1 : Real)) =O[l] (fun _ : ι => (1 : Real)) :=
    Asymptotics.isBigO_refl _ l
  have hOneG : (fun t => 1 + gamma (fp t) n)
      =O[l] (fun _ : ι => (1 : Real)) := by
    exact hone.add hgnOne
  have hs2 : VectorFamilyIsBigOOne l (fun t i =>
      ch14ext_gjeResidualS2 n (L t) (X t) (U t) (xhat t) i) := by
    have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
      (matrixFamily_abs_isBigOOne hU)
      (ch14ext_vectorFamily_abs_isBigOOne hx)
    have hXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
      (matrixFamily_abs_isBigOOne hX) hUx
    have hLXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
      (matrixFamily_abs_isBigOOne hL) hXUx
    simpa only [ch14ext_gjeResidualS2, absMatrix, absVec] using hLXUx
  have hs22 : VectorFamilyIsBigOOne l (fun t i =>
      ch14ext_gjeResidualS22 n (L t) (X t) (U t) (xhat t) i) := by
    have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
      (matrixFamily_abs_isBigOOne hU)
      (ch14ext_vectorFamily_abs_isBigOOne hx)
    have hXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
      (matrixFamily_abs_isBigOOne hX) hUx
    have hXXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
      (matrixFamily_abs_isBigOOne hX) hXUx
    have hLXXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
      (matrixFamily_abs_isBigOOne hL) hXXUx
    simpa only [ch14ext_gjeResidualS22, absMatrix, absVec] using hLXXUx
  have hg1gn : (fun t => gamma (fp t) 1 * gamma (fp t) n)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hg1.mul hgn
  have hcg1 : (fun t => gje_c₃ (fp t) n * gamma (fp t) 1)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hc.mul hg1
  have hcg1One : (fun t =>
      gje_c₃ (fp t) n * gamma (fp t) 1 * (1 + gamma (fp t) n))
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hcg1.mul hOneG
  have hcoef1 : (fun t =>
      ch14ext_gammaRem (fp t) 1 + gamma (fp t) 1 * gamma (fp t) n +
        2 * gje_c₃ (fp t) n * gamma (fp t) 1 * (1 + gamma (fp t) n))
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_assoc] using
      (hgr1.add hg1gn).add (hcg1One.const_mul_left 2)
  have hterm1 : (fun t =>
      (ch14ext_gammaRem (fp t) 1 + gamma (fp t) 1 * gamma (fp t) n +
        2 * gje_c₃ (fp t) n * gamma (fp t) 1 * (1 + gamma (fp t) n)) *
        ch14ext_gjeResidualS2 n (L t) (X t) (U t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hcoef1.mul (hs2 i)
  have hcSq : (fun t => gje_c₃ (fp t) n * gje_c₃ (fp t) n)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hc.mul hc
  have hcoef2 : (fun t =>
      gje_c₃ (fp t) n * gje_c₃ (fp t) n * gamma (fp t) 1 *
        (1 + gamma (fp t) n))
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using (hcSq.mul hg1One).mul hOneG
  have hterm2 : (fun t =>
      gje_c₃ (fp t) n * gje_c₃ (fp t) n * gamma (fp t) 1 *
        (1 + gamma (fp t) n) *
        ch14ext_gjeResidualS22 n (L t) (X t) (U t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hcoef2.mul (hs22 i)
  simpa only [ch14ext_gjeResidualFinalDivisionHigherOrder] using
    (hbase.add hterm1).add hterm2

/-- The full printed (14.31) remainder, including the general-diagonal
inverse-envelope correction, is `O(u²)` under the standard local boundedness
hypotheses. -/
theorem ch14ext_gjeResidualFinalizedPrintedHigherOrder_family_isBigO
    {ι : Type*} {l : Filter ι} (n : Nat) (fp : ι -> FPModel)
    (L U U_inv X Z : ι -> Fin n -> Fin n -> Real)
    (y xhat : ι -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (nhds 0))
    (hL : MatrixFamilyIsBigOOne l L) (hU : MatrixFamilyIsBigOOne l U)
    (hUinv : MatrixFamilyIsBigOOne l U_inv)
    (hX : MatrixFamilyIsBigOOne l X) (hZ : MatrixFamilyIsBigOOne l Z)
    (hy : VectorFamilyIsBigOOne l y)
    (hx : VectorFamilyIsBigOOne l xhat) (i : Fin n) :
    (fun t => ch14ext_gjeResidualFinalizedPrintedHigherOrder (fp t)
      (L t) (U t) (U_inv t) (X t) (Z t) (y t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hbase := ch14ext_gjeResidualFinalDivisionHigherOrder_family_isBigO
    n fp L X U y xhat hu hL hX hU hy hx i
  have hc := ch14ext_gje_c3_family_isBigO_unit n fp hu
  have huRefl : (fun t => (fp t).u) =O[l] (fun t => (fp t).u) :=
    Asymptotics.isBigO_refl _ l
  have huOne : (fun t => (fp t).u) =O[l] (fun _ : ι => (1 : Real)) :=
    hu.isBigO_one Real
  have hcOne := hc.trans huOne
  have hAU := matrixFamily_abs_isBigOOne hU
  have hAUi := matrixFamily_abs_isBigOOne hUinv
  have hUZ := ch14ext_matrixFamily_mul_family_isBigOOne hAU hZ
  have hUZU := ch14ext_matrixFamily_mul_family_isBigOOne hUZ hAU
  have hUZUUi := ch14ext_matrixFamily_mul_family_isBigOOne hUZU hAUi
  have hXU := ch14ext_matrixFamily_mul_family_isBigOOne hX hAU
  have hXUUi := ch14ext_matrixFamily_mul_family_isBigOOne hXU hAUi
  have hXUZ := ch14ext_matrixFamily_mul_family_isBigOOne hXU hZ
  have hXUZU := ch14ext_matrixFamily_mul_family_isBigOOne hXUZ hAU
  have hXUZUUi := ch14ext_matrixFamily_mul_family_isBigOOne hXUZU hAUi
  have hC : MatrixFamilyIsBigOOne l (fun t =>
      ch14ext_gjeFinalizedResidualEnvelopeCorrection n
        (U t) (X t) (Z t) (U_inv t) (gje_c₃ (fp t) n)) := by
    intro a b
    have hfirst : (fun t =>
        matMul n (matMul n (matMul n (absMatrix n (U t)) (Z t))
          (absMatrix n (U t))) (absMatrix n (U_inv t)) a b)
        =O[l] (fun _ : ι => (1 : Real)) := by
      simpa only [absMatrix] using hUZUUi a b
    have hsecond : (fun t =>
        matMul n (matMul n (X t) (absMatrix n (U t)))
          (absMatrix n (U_inv t)) a b)
        =O[l] (fun _ : ι => (1 : Real)) := by
      simpa only [absMatrix] using hXUUi a b
    have hthird : (fun t => gje_c₃ (fp t) n *
        matMul n (matMul n (matMul n (matMul n (X t)
          (absMatrix n (U t))) (Z t)) (absMatrix n (U t)))
          (absMatrix n (U_inv t)) a b)
        =O[l] (fun _ : ι => (1 : Real)) := by
      simpa only [absMatrix, one_mul] using hcOne.mul (hXUZUUi a b)
    simpa only [ch14ext_gjeFinalizedResidualEnvelopeCorrection] using
      (hfirst.add hsecond).add hthird
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAU
    (ch14ext_vectorFamily_abs_isBigOOne hx)
  have hCUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hC hUx
  have hCorr := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hL) hCUx
  have huc : (fun t => (fp t).u * gje_c₃ (fp t) n)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using huRefl.mul hc
  have hterm : (fun t =>
      8 * (n : Real) * (fp t).u * gje_c₃ (fp t) n *
        ch14ext_gjeFinalizedResidualPrintedCorrection (fp t)
          (L t) (U t) (U_inv t) (X t) (Z t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one, mul_assoc,
      ch14ext_gjeFinalizedResidualPrintedCorrection] using
      (huc.const_mul_left (8 * (n : Real))).mul (hCorr i)
  simpa only [ch14ext_gjeResidualFinalizedPrintedHigherOrder] using
    hbase.add hterm

/-- The literal final-division forward remainder in (14.32) is `O(u²)`.
The only extra rate input is the already-proved first-order stage-two error;
the operational family adapter below supplies it from (14.29). -/
theorem ch14ext_gjeForwardFinalDivisionHigherOrder_family_isBigO
    {ι : Type*} {l : Filter ι} (n : Nat) (fp : ι -> FPModel)
    (A_inv L U X U_inv : ι -> Fin n -> Fin n -> Real)
    (z y xhat : ι -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (nhds 0))
    (hA : MatrixFamilyIsBigOOne l A_inv)
    (hL : MatrixFamilyIsBigOOne l L) (hU : MatrixFamilyIsBigOOne l U)
    (hX : MatrixFamilyIsBigOOne l X)
    (hUinv : MatrixFamilyIsBigOOne l U_inv)
    (hz : VectorFamilyIsBigOOne l z) (hy : VectorFamilyIsBigOOne l y)
    (hx : VectorFamilyIsBigOOne l xhat)
    (he : forall j : Fin n,
      (fun t => |z t j - xhat t j|) =O[l] (fun t => (fp t).u))
    (i : Fin n) :
    (fun t => ch14ext_gjeForwardFinalDivisionHigherOrder n (fp t)
      (A_inv t) (L t) (U t) (X t) (U_inv t)
      (z t) (y t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hgn := ch14ext_gamma_family_isBigO_unit n fp hu
  have hg1 := ch14ext_gamma_family_isBigO_unit 1 fp hu
  have hgrn := ch14ext_gammaRem_family_isBigO_unit_sq n fp hu
  have hgr1 := ch14ext_gammaRem_family_isBigO_unit_sq 1 fp hu
  have hc := ch14ext_gje_c3_family_isBigO_unit n fp hu
  have hcr := ch14ext_gje_c3_quadratic_remainder_family_isBigO_unit_sq n fp hu
  have hAU := matrixFamily_abs_isBigOOne hU
  have hAA := matrixFamily_abs_isBigOOne hA
  have hAL := matrixFamily_abs_isBigOOne hL
  have hAUi := matrixFamily_abs_isBigOOne hUinv
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne hx
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAU hxabs
  have hLUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAL hUx
  have hT1 := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAA hLUx
  have hT2X := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX hUx
  have hT2Ui := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAUi hUx
  have hzabs := ch14ext_vectorFamily_abs_isBigOOne hz
  have hyabs := ch14ext_vectorFamily_abs_isBigOOne hy
  have hUz := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAU hzabs
  have hXUz := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX hUz
  have hXy := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX hyabs
  have hRaw : VectorFamilyIsBigOOne l (fun t a =>
      ch14ext_gjeForwardRaw n (X t) (U t) (z t) (y t) a) := by
    intro a
    simpa only [ch14ext_gjeForwardRaw] using (hXUz a).add (hXy a)
  have hUraw := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAU hRaw
  have hQ2 := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX hUraw
  have hUix := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAUi hUx
  have hUUix := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAU hUix
  have hCorr := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX hUUix
  have hErrAction :=
    ch14ext_gjeForwardFirstStageErrorAction_family_isBigO_unit
      n fp A_inv L U z xhat hA hL hU he i
  have hcSq : (fun t => gje_c₃ (fp t) n * gje_c₃ (fp t) n)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hc.mul hc
  have hcg1 : (fun t => gje_c₃ (fp t) n * gamma (fp t) 1)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hc.mul hg1
  have hcoef2 : (fun t =>
      2 * gje_c3_quadratic_remainder (fp t) n +
        ch14ext_gammaRem (fp t) 1)
      =O[l] (fun t => (fp t).u ^ 2) := by
    exact (hcr.const_mul_left 2).add hgr1
  have hterm1 : (fun t => 2 * ch14ext_gammaRem (fp t) n *
      ch14ext_gjeForwardT1 n (A_inv t) (L t) (U t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [ch14ext_gjeForwardT1, absMatrix, absVec, mul_one,
      mul_assoc] using (hgrn.const_mul_left 2).mul (hT1 i)
  have hterm2 : (fun t =>
      (2 * gje_c3_quadratic_remainder (fp t) n +
        ch14ext_gammaRem (fp t) 1) *
        ch14ext_gjeForwardT2 n (absMatrix n (U_inv t))
          (U t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [ch14ext_gjeForwardT2, absMatrix, absVec, mul_one] using
      hcoef2.mul (hT2Ui i)
  have hterm3 : (fun t => 2 * gamma (fp t) n *
      ch14ext_gjeForwardFirstStageErrorAction n
        (A_inv t) (L t) (U t) (z t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (hgn.const_mul_left 2).mul hErrAction
  have hterm4 : (fun t =>
      2 * gje_c₃ (fp t) n * gje_c₃ (fp t) n *
        ch14ext_gjeForwardQ2 n (X t) (U t) (z t) (y t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [ch14ext_gjeForwardQ2, absMatrix, mul_one, mul_assoc] using
      (hcSq.const_mul_left 2).mul (hQ2 i)
  have hterm5 : (fun t =>
      2 * gje_c₃ (fp t) n * gamma (fp t) 1 *
        ch14ext_gjeForwardT2 n (X t) (U t) (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [ch14ext_gjeForwardT2, absMatrix, absVec, mul_one,
      mul_assoc] using (hcg1.const_mul_left 2).mul (hT2X i)
  have hterm6 : (fun t =>
      2 * gje_c₃ (fp t) n * gje_c₃ (fp t) n *
        ch14ext_gjeForwardUinvCorrection n (X t) (U t) (U_inv t)
          (xhat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [ch14ext_gjeForwardUinvCorrection, absMatrix, absVec,
      mul_one, mul_assoc] using (hcSq.const_mul_left 2).mul (hCorr i)
  simpa only [ch14ext_gjeForwardFinalDivisionHigherOrder] using
    ((((hterm1.add hterm2).add hterm3).add hterm4).add hterm5).add hterm6

/-- The actual second-stage error of an operational family is componentwise
`O(u)`, derived from the literal (14.29) endpoint rather than assumed. -/
theorem ch14ext_gjeFinalizedFamily_stage2_error_isBigO_unit
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14GJEFinalizedFamily ι l n A b) (i : Fin n) :
    (fun t => |F.z t i - ch14ext_gjeFinalizedFamilyOutput F t i|)
      =O[l] (fun t => (F.model t).u) := by
  let X := ch14ext_gjeFinalizedFamilyNormalizedPabs F
  let U : ι -> Fin n -> Fin n -> Real := fun t => (F.initial t).matrix
  let y : ι -> Fin n -> Real := fun t => (F.initial t).rhs
  let xhat := ch14ext_gjeFinalizedFamilyOutput F
  have hXone : MatrixFamilyIsBigOOne l X := by
    simpa only [X, ch14ext_gjeFinalizedFamilyNormalizedPabs] using
      F.normalized_Pabs_isBigO_one
  have hUone : MatrixFamilyIsBigOOne l U := F.U_hat_isBigO_one
  have hyone : VectorFamilyIsBigOOne l y := F.y_isBigO_one
  have hxone : VectorFamilyIsBigOOne l xhat := by
    simpa only [xhat, ch14ext_gjeFinalizedFamilyOutput] using
      F.output_isBigO_one
  have hAU := matrixFamily_abs_isBigOOne hUone
  have hzabs := ch14ext_vectorFamily_abs_isBigOOne F.z_isBigO_one
  have hyabs := ch14ext_vectorFamily_abs_isBigOOne hyone
  have hUz := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hAU hzabs
  have hXUz := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hXone hUz
  have hXy := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hXone hyabs
  have hRaw : VectorFamilyIsBigOOne l (fun t a =>
      ch14ext_gjeForwardRaw n (X t) (U t) (F.z t) (y t) a) := by
    intro a
    simpa only [ch14ext_gjeForwardRaw] using (hXUz a).add (hXy a)
  have hc := ch14ext_gje_c3_family_isBigO_unit n F.model
    F.unit_tendsto_zero
  have hg1 := ch14ext_gamma_family_isBigO_unit 1 F.model
    F.unit_tendsto_zero
  have hterm1 : (fun t => gje_c₃ (F.model t) n *
      ch14ext_gjeForwardRaw n (X t) (U t) (F.z t) (y t) i)
      =O[l] (fun t => (F.model t).u) := by
    simpa only [mul_one] using hc.mul (hRaw i)
  have hterm2 : (fun t => gamma (F.model t) 1 * |xhat t i|)
      =O[l] (fun t => (F.model t).u) := by
    simpa only [mul_one] using hg1.mul
      ((ch14ext_vectorFamily_abs_isBigOOne hxone) i)
  have hrhs : (fun t =>
      gje_c₃ (F.model t) n *
          ch14ext_gjeForwardRaw n (X t) (U t) (F.z t) (y t) i +
        gamma (F.model t) 1 * |xhat t i|)
      =O[l] (fun t => (F.model t).u) := hterm1.add hterm2
  have hdom : (fun t => |F.z t i - xhat t i|) =O[l] (fun t =>
      gje_c₃ (F.model t) n *
          ch14ext_gjeForwardRaw n (X t) (U t) (F.z t) (y t) i +
        gamma (F.model t) 1 * |xhat t i|) := by
    have hrhsNonneg : forall t, 0 <=
        gje_c₃ (F.model t) n *
            ch14ext_gjeForwardRaw n (X t) (U t) (F.z t) (y t) i +
          gamma (F.model t) 1 * |xhat t i| := by
      intro t
      have hP : forall a j : Fin n,
          0 <= ch14ext_gjeFinalizedSourcePabs (F.model t) (F.initial t) a j := by
        intro a j
        exact gje_cumulative_product_abs_nonneg n
          (ch14ext_gjeFinalizedSourceStages (F.model t) (F.initial t))
          1 (1 + (n - 1)) a j
      have hXnonneg : forall a j : Fin n, 0 <= X t a j := by
        simpa only [X, ch14ext_gjeFinalizedFamilyNormalizedPabs] using
          (ch14ext_gjeNormalizedPabs_nonneg n
            (ch14ext_gjeBeforeFinalDivision (F.model t) (F.initial t)).matrix
            (ch14ext_gjeFinalizedSourcePabs (F.model t) (F.initial t)) hP)
      exact add_nonneg
        (mul_nonneg (gje_c3_nonneg (F.model t) n F.dimension_pos
          (F.valid_three t))
          (ch14ext_gjeForwardRaw_nonneg n (X t) (U t) (F.z t) (y t) i
            hXnonneg))
        (mul_nonneg (gamma_nonneg (F.model t) (F.valid_one t)) (abs_nonneg _))
    have hle : forall t, |F.z t i - xhat t i| <=
        gje_c₃ (F.model t) n *
            ch14ext_gjeForwardRaw n (X t) (U t) (F.z t) (y t) i +
          gamma (F.model t) 1 * |xhat t i| := by
      intro t
      simpa only [X, U, y, xhat, ch14ext_gjeFinalizedFamilyOutput,
        ch14ext_gjeFinalizedFamilyNormalizedPabs] using
        ch14ext_gjeFinalizedSourceTrace_stage2_forward_error_14_29_with_final_division
          (F.model t) (F.initial t) (F.z t) F.dimension_pos
          (F.valid_three t) (F.valid_one t)
          (F.lu_certificate t).U_lower_zero (F.diagonal_nonzero t)
          (F.upper_solve t) (F.pivots_nonzero t) i
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with t
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
      abs_of_nonneg (hrhsNonneg t)] using hle t
  exact hdom.trans hrhs

/-- Family-level literal Theorem 14.5 endpoint.  It supplies the pointwise
printed inequalities and proves both named remainders are `O(u²)`.  This is
the common operational adapter consumed by Corollaries 14.6 and 14.7. -/
theorem ch14ext_gjeFinalizedFamily_theorem14_5_endpoint
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14GJEFinalizedFamily ι l n A b)
    (A_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hAinv : IsLeftInverse n A A_inv)
    (hExact : forall i : Fin n, matMulVec n A x i = b i) :
    (forall (t : ι) (i : Fin n),
      |b i - matMulVec n A (ch14ext_gjeFinalizedFamilyOutput F t) i| <=
        8 * (n : Real) * (F.model t).u *
          ch14ext_gjeResidualS2 n (F.L_hat t)
            (matMul n (absMatrix n (F.initial t).matrix)
              (absMatrix n (F.U_inv t)))
            (F.initial t).matrix (ch14ext_gjeFinalizedFamilyOutput F t) i +
        ch14ext_gjeResidualFinalizedPrintedHigherOrder (F.model t)
          (F.L_hat t) (F.initial t).matrix (F.U_inv t)
          (ch14ext_gjeFinalizedFamilyXabs F t)
          (ch14ext_gjeFinalizedFamilyNormalizedPabs F t)
          (F.initial t).rhs (ch14ext_gjeFinalizedFamilyOutput F t) i) /\
    (forall i : Fin n, (fun t =>
      ch14ext_gjeResidualFinalizedPrintedHigherOrder (F.model t)
        (F.L_hat t) (F.initial t).matrix (F.U_inv t)
        (ch14ext_gjeFinalizedFamilyXabs F t)
        (ch14ext_gjeFinalizedFamilyNormalizedPabs F t)
        (F.initial t).rhs (ch14ext_gjeFinalizedFamilyOutput F t) i)
      =O[l] (fun t => (F.model t).u ^ 2)) /\
    (forall (t : ι) (i : Fin n),
      |x i - ch14ext_gjeFinalizedFamilyOutput F t i| <=
        2 * (n : Real) * (F.model t).u *
          (ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
              (ch14ext_gjeFinalizedFamilyOutput F t) i +
            3 * ch14ext_gjeForwardT2 n (absMatrix n (F.U_inv t))
              (F.initial t).matrix (ch14ext_gjeFinalizedFamilyOutput F t) i) +
        ch14ext_gjeForwardFinalDivisionHigherOrder n (F.model t)
          A_inv (F.L_hat t) (F.initial t).matrix
          (ch14ext_gjeFinalizedFamilyNormalizedPabs F t) (F.U_inv t)
          (F.z t) (F.initial t).rhs
          (ch14ext_gjeFinalizedFamilyOutput F t) i) /\
    (forall i : Fin n, (fun t =>
      ch14ext_gjeForwardFinalDivisionHigherOrder n (F.model t)
        A_inv (F.L_hat t) (F.initial t).matrix
        (ch14ext_gjeFinalizedFamilyNormalizedPabs F t) (F.U_inv t)
        (F.z t) (F.initial t).rhs
        (ch14ext_gjeFinalizedFamilyOutput F t) i)
      =O[l] (fun t => (F.model t).u ^ 2)) := by
  constructor
  . intro t
    simpa only [ch14ext_gjeFinalizedFamilyOutput,
      ch14ext_gjeFinalizedFamilyXabs,
      ch14ext_gjeFinalizedFamilyNormalizedPabs] using
      ch14ext_gjeFinalizedSourceTrace_overall_residual_14_31_printed
        (F.model t) A (F.L_hat t) (F.U_inv t) b (F.initial t)
        (F.lu_certificate t) (F.computed_upper_inverse t).2
        (F.valid_n t) F.dimension_pos (F.valid_one t) (F.valid_three t)
        (F.diagonal_nonzero t) (F.forward_start t) (F.pivots_nonzero t)
  constructor
  . intro i
    exact ch14ext_gjeResidualFinalizedPrintedHigherOrder_family_isBigO
      n F.model F.L_hat (fun t => (F.initial t).matrix) F.U_inv
      (ch14ext_gjeFinalizedFamilyXabs F)
      (ch14ext_gjeFinalizedFamilyNormalizedPabs F)
      (fun t => (F.initial t).rhs) (ch14ext_gjeFinalizedFamilyOutput F)
      F.unit_tendsto_zero F.L_hat_isBigO_one F.U_hat_isBigO_one
      F.U_inv_isBigO_one
      (by simpa only [ch14ext_gjeFinalizedFamilyXabs] using
        F.source_Xabs_isBigO_one)
      (by simpa only [ch14ext_gjeFinalizedFamilyNormalizedPabs] using
        F.normalized_Pabs_isBigO_one)
      F.y_isBigO_one
      (by simpa only [ch14ext_gjeFinalizedFamilyOutput] using
        F.output_isBigO_one) i
  constructor
  . intro t
    simpa only [ch14ext_gjeFinalizedFamilyOutput,
      ch14ext_gjeFinalizedFamilyNormalizedPabs] using
      ch14ext_gjeFinalizedSourceTrace_overall_forward_14_32
        (F.model t) A A_inv (F.L_hat t) (F.U_inv t) b x (F.z t)
        (F.initial t) (F.lu_certificate t) hAinv
        (F.computed_upper_inverse t).2 (F.valid_n t) F.dimension_pos
        (F.valid_one t) (F.valid_three t) (F.diagonal_nonzero t)
        (F.forward_start t) hExact (F.upper_solve t) (F.pivots_nonzero t)
  . intro i
    exact ch14ext_gjeForwardFinalDivisionHigherOrder_family_isBigO
      n F.model (fun _ => A_inv) F.L_hat (fun t => (F.initial t).matrix)
      (ch14ext_gjeFinalizedFamilyNormalizedPabs F) F.U_inv F.z
      (fun t => (F.initial t).rhs) (ch14ext_gjeFinalizedFamilyOutput F)
      F.unit_tendsto_zero (ch14ext_fixedMatrix_family_isBigOOne l A_inv)
      F.L_hat_isBigO_one F.U_hat_isBigO_one
      (by simpa only [ch14ext_gjeFinalizedFamilyNormalizedPabs] using
        F.normalized_Pabs_isBigO_one)
      F.U_inv_isBigO_one F.z_isBigO_one F.y_isBigO_one
      (by simpa only [ch14ext_gjeFinalizedFamilyOutput] using
        F.output_isBigO_one)
      (ch14ext_gjeFinalizedFamily_stage2_error_isBigO_unit F) i

/-- The actual (14.31) terminal vector has Euclidean norm `O(u^2)`. -/
theorem ch14ext_cor146FinalizedResidualTerminal_family_isBigO_u_sq
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor146FinalizedResidualTerminal F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  apply ch14ext_cor146Closure_vecNorm2_family_isBigO
  exact (ch14ext_gjeFinalizedFamily_theorem14_5_endpoint F.gje A_inv x
    F.uniform_inverse.source_inverse.1 F.exact_solution).2.1

/-- The actual (14.32) terminal vector has Euclidean norm `O(u^2)`. -/
theorem ch14ext_cor146FinalizedForwardTerminal_family_isBigO_u_sq
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor146FinalizedForwardTerminal F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  apply ch14ext_cor146Closure_vecNorm2_family_isBigO
  exact (ch14ext_gjeFinalizedFamily_theorem14_5_endpoint F.gje A_inv x
    F.uniform_inverse.source_inverse.1 F.exact_solution).2.2.2

/-- The complete actual-output residual remainder is genuinely `O(u^2)`. -/
theorem ch14ext_cor146FinalizedResidualRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor146FinalizedResidualRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  have hn : Filter.Eventually (fun t => gammaValid (F.gje.model t) n) l :=
    Filter.Eventually.of_forall F.gje.valid_n
  have hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (F.gje.model t) n < 1) l :=
    Filter.Eventually.of_forall F.gamma_small
  have hcorr := ch14ext_cor146ResidualSpectralCorrection_family_isBigO_u
    n F.gje.model A A_inv F.gje.L_hat
      (fun t => (F.gje.initial t).matrix) F.gje.unit_tendsto_zero
      F.gje.dimension_pos hn hsmall F.uniform_inverse
  have hxnorm : (fun t =>
      vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t))
      =O[l] (fun _ : I => (1 : Real)) :=
    ch14ext_cor146Closure_vecNorm2_family_isBigO F.gje.output_isBigO_one
  have huO := Asymptotics.isBigO_refl (fun t => (F.gje.model t).u) l
  have hraw := (huO.mul hcorr).mul hxnorm
  have hlead : (fun t =>
      8 * (n : Real) ^ 3 * (F.gje.model t).u *
        ch14ext_cor146ResidualSpectralCorrection n F.gje.model A A_inv
          F.gje.L_hat (fun s => (F.gje.initial s).matrix) t *
        opNorm2 A * vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t))
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
    have h := hraw.const_mul_left (8 * (n : Real) ^ 3 * opNorm2 A)
    simpa only [pow_two, one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm]
      using h
  simpa only [ch14ext_cor146FinalizedResidualRemainder] using
    (ch14ext_cor146FinalizedResidualTerminal_family_isBigO_u_sq F).add hlead

/-- The complete actual-output absolute forward remainder is `O(u^2)`. -/
theorem ch14ext_cor146FinalizedForwardAbsoluteRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor146FinalizedForwardAbsoluteRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  have hn : Filter.Eventually (fun t => gammaValid (F.gje.model t) n) l :=
    Filter.Eventually.of_forall F.gje.valid_n
  have hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (F.gje.model t) n < 1) l :=
    Filter.Eventually.of_forall F.gamma_small
  have hcorr := ch14ext_cor146ForwardCoefficientCorrection_family_isBigO_u
    n F.gje.model A A_inv F.gje.L_hat
      (fun t => (F.gje.initial t).matrix) F.gje.unit_tendsto_zero
      F.gje.dimension_pos hn hsmall F.uniform_inverse
  have hxnorm : (fun t =>
      vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t))
      =O[l] (fun _ : I => (1 : Real)) :=
    ch14ext_cor146Closure_vecNorm2_family_isBigO F.gje.output_isBigO_one
  have huO := Asymptotics.isBigO_refl (fun t => (F.gje.model t).u) l
  have hraw := (huO.mul hcorr).mul hxnorm
  have hextra : (fun t => (F.gje.model t).u *
      ch14ext_cor146ForwardCoefficientCorrection n F.gje.model A A_inv
        F.gje.L_hat (fun s => (F.gje.initial s).matrix) t *
      vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t))
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
    simpa only [pow_two, mul_one, mul_assoc] using hraw
  simpa only [ch14ext_cor146FinalizedForwardAbsoluteRemainder] using
    (ch14ext_cor146FinalizedForwardTerminal_family_isBigO_u_sq F).add hextra

/-- The ratio-removal correction preserves the `O(u^2)` order. -/
theorem ch14ext_cor146FinalizedForwardRelativeRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor146FinalizedForwardRelativeRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  let q : I -> Real := fun t => c * (F.gje.model t).u
  have huO := Asymptotics.isBigO_refl (fun t => (F.gje.model t).u) l
  have hq : q =O[l] (fun t => (F.gje.model t).u) := by
    simpa only [q] using huO.const_mul_left c
  have hqSq : (fun t => q t ^ 2) =O[l]
      (fun t => (F.gje.model t).u ^ 2) := by
    simpa only [pow_two] using hq.mul hq
  have hqZero : Tendsto q l (nhds 0) := by
    simpa only [q, mul_zero] using F.gje.unit_tendsto_zero.const_mul c
  have hden : Tendsto (fun t => 1 - q t) l (nhds 1) := by
    simpa using hqZero.const_sub 1
  have hinvOne : (fun t => (1 - q t)⁻¹)
      =O[l] (fun _ : I => (1 : Real)) := by
    have hinv : Tendsto (fun t => (1 - q t)⁻¹) l (nhds (1 : Real)) := by
      simpa using hden.inv₀ one_ne_zero
    exact hinv.isBigO_one Real
  have hterm1 : (fun t => q t ^ 2 * (1 - q t)⁻¹)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
    simpa only [mul_one] using hqSq.mul hinvOne
  have habs :=
    ch14ext_cor146FinalizedForwardAbsoluteRemainder_family_isBigO_u_sq F
  have hxconst : (fun _ : I => (vecNorm2 x)⁻¹)
      =O[l] (fun _ : I => (1 : Real)) := by
    simpa using
      (Asymptotics.isBigO_refl (fun _ : I => (1 : Real)) l).const_mul_left
        (vecNorm2 x)⁻¹
  have hterm2 : (fun t =>
      ch14ext_cor146FinalizedForwardAbsoluteRemainder F t *
        (1 - q t)⁻¹ * (vecNorm2 x)⁻¹)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
    simpa only [mul_one] using (habs.mul hinvOne).mul hxconst
  simpa only [ch14ext_cor146FinalizedForwardRelativeRemainder, c, q] using
    hterm1.add hterm2

/-- The actual final-division output converges to the exact solution with
normwise error `O(u)`.  This is derived from the absolute forward endpoint,
the bounded actual output family, and its explicit `O(u^2)` remainder. -/
theorem ch14ext_cor146Finalized_output_error_family_isBigO_u
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) :
    (fun t => vecNorm2 (fun i : Fin n =>
      x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i))
      =O[l] (fun t => (F.gje.model t).u) := by
  let err : I -> Real := fun t => vecNorm2 (fun i : Fin n =>
    x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i)
  let lead : I -> Real := fun t =>
    8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
      kappa2 A A_inv *
      vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t)
  let rem : I -> Real := fun t =>
    ch14ext_cor146FinalizedForwardAbsoluteRemainder F t
  have hpoint : forall t, err t <= lead t + rem t := by
    intro t
    simpa only [err, lead, rem] using
      ch14ext_cor146Finalized_forward_absolute_source_literal F t
  have hxnorm : (fun t =>
      vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t))
      =O[l] (fun _ : I => (1 : Real)) :=
    ch14ext_cor146Closure_vecNorm2_family_isBigO F.gje.output_isBigO_one
  have huO := Asymptotics.isBigO_refl (fun t => (F.gje.model t).u) l
  have hleadRaw :=
    (huO.const_mul_left
      (8 * (n : Real) ^ 2 * Real.sqrt n * kappa2 A A_inv)).mul hxnorm
  have hlead : lead =O[l] (fun t => (F.gje.model t).u) := by
    simpa only [lead, one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm]
      using hleadRaw
  have huOne : (fun t => (F.gje.model t).u)
      =O[l] (fun _ : I => (1 : Real)) :=
    F.gje.unit_tendsto_zero.isBigO_one Real
  have huSq : (fun t => (F.gje.model t).u ^ 2)
      =O[l] (fun t => (F.gje.model t).u) := by
    simpa only [pow_two, mul_one] using huO.mul huOne
  have hrem : rem =O[l] (fun t => (F.gje.model t).u) := by
    exact (ch14ext_cor146FinalizedForwardAbsoluteRemainder_family_isBigO_u_sq
      F).trans huSq
  have hrhs : (fun t => lead t + rem t)
      =O[l] (fun t => (F.gje.model t).u) := hlead.add hrem
  have hdom : err =O[l] (fun t => lead t + rem t) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with t
    have herr0 : 0 <= err t := by
      exact vecNorm2_nonneg _
    have hrhs0 : 0 <= lead t + rem t := le_trans herr0 (hpoint t)
    simpa only [Real.norm_eq_abs, abs_of_nonneg herr0,
      abs_of_nonneg hrhs0, one_mul] using hpoint t
  simpa only [err] using hdom.trans hrhs

/-- The exact-solution-norm replacement term in the printed residual is
`O(u^2)`: its explicit leading `u` multiplies the derived `O(u)` output
error. -/
theorem ch14ext_cor146FinalizedResidualExactNormCorrection_family_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) :
    (fun t =>
      8 * (n : Real) ^ 3 * (F.gje.model t).u *
        Real.sqrt (kappa2 A A_inv) * opNorm2 A *
        vecNorm2 (fun i =>
          ch14ext_gjeFinalizedFamilyOutput F.gje t i - x i))
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  have herr := ch14ext_cor146Finalized_output_error_family_isBigO_u F
  have herr' : (fun t => vecNorm2 (fun i =>
      ch14ext_gjeFinalizedFamilyOutput F.gje t i - x i))
      =O[l] (fun t => (F.gje.model t).u) := by
    simpa only [vecNorm2_sub_comm] using herr
  have huO := Asymptotics.isBigO_refl (fun t => (F.gje.model t).u) l
  have hraw := (huO.mul herr').const_mul_left
    (8 * (n : Real) ^ 3 * Real.sqrt (kappa2 A A_inv) * opNorm2 A)
  simpa only [pow_two, one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm]
    using hraw

/-- The full exact-PDF residual remainder, including the replacement of
`||xhat||_2` by `||x||_2`, is genuinely `O(u^2)`. -/
theorem ch14ext_cor146FinalizedResidualPrintedRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor146FinalizedResidualPrintedRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  simpa only [ch14ext_cor146FinalizedResidualPrintedRemainder] using
    (ch14ext_cor146FinalizedResidualRemainder_family_isBigO_u_sq F).add
      (ch14ext_cor146FinalizedResidualExactNormCorrection_family_isBigO_u_sq F)

/-- Complete literal Corollary 14.6 endpoint for operational Algorithm 14.4
families.  The residual leading coefficient multiplies the exact PDF quantity
`||x||_2`, the relative forward coefficient contains no computed/exact norm
ratio, and both named remainders are genuine `O(u^2)` terms. -/
theorem ch14ext_cor146Finalized_vanishing_family_endpoint
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) :
    (forall t,
      vecNorm2 (fun i : Fin n =>
          b i - matMulVec n A
            (ch14ext_gjeFinalizedFamilyOutput F.gje t) i) <=
        8 * (n : Real) ^ 3 * (F.gje.model t).u *
            Real.sqrt (kappa2 A A_inv) * opNorm2 A *
            vecNorm2 x +
          ch14ext_cor146FinalizedResidualPrintedRemainder F t) /\
    ((fun t => ch14ext_cor146FinalizedResidualPrintedRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2)) /\
    (Filter.Eventually (fun t =>
      vecNorm2 (fun i : Fin n =>
          x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) / vecNorm2 x <=
        8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
            kappa2 A A_inv +
          ch14ext_cor146FinalizedForwardRelativeRemainder F t) l) /\
    ((fun t => ch14ext_cor146FinalizedForwardRelativeRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2)) := by
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  have hqZero : Tendsto (fun t => c * (F.gje.model t).u) l (nhds 0) := by
    simpa only [mul_zero] using F.gje.unit_tendsto_zero.const_mul c
  have hqSmall : Filter.Eventually
      (fun t => c * (F.gje.model t).u < 1) l :=
    (tendsto_order.1 hqZero).2 1 zero_lt_one
  have hbootstrap : Filter.Eventually (fun t =>
      8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
        kappa2 A A_inv < 1) l := by
    filter_upwards [hqSmall] with t ht
    dsimp [c, ch14ext_cor146ForwardPrintedCoefficient] at ht
    convert ht using 1 <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ch14ext_cor146Finalized_residual_exact_solution_literal F
  · exact
      ch14ext_cor146FinalizedResidualPrintedRemainder_family_isBigO_u_sq F
  · filter_upwards [hbootstrap] with t ht
    exact ch14ext_cor146Finalized_forward_relative_source_literal F t ht
  · exact
      ch14ext_cor146FinalizedForwardRelativeRemainder_family_isBigO_u_sq F

end Ch14Ext
end NumStability
