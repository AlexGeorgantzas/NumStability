import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEAsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEPrintedEnvelopeClosure
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJETheorem145SourceClosure
import NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds

/-!
# VanishingEndpoints

Canonical destination for the Chapter14.Theorem05 declarations relocated from the
historical path `NumStability.Algorithms.Ch14GJETheorem145SourceClosure` during wave R08.
Holds 7 declaration(s): 7 public.

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

/-- Higham (14.30a-c), source-active trace with the printed
`|Uhat||Uhat^-1|` envelope and explicit `O(u^2)` corrections. -/
theorem ch14ext_gjeSourceTrace_14_30abc_printed_vanishing_family_endpoint
    {iota : Type*} {l : Filter iota} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (U_inv : iota -> Fin n -> Fin n -> Real)
    (hUinv : forall t, IsRightInverse n (R.state t).matrix (U_inv t))
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv) :
    exists DeltaU : iota -> Fin n -> Fin n -> Real,
      exists Deltay : iota -> Fin n -> Real,
      (forall t i,
        ∑ j : Fin n,
          ((R.state t).matrix i j + DeltaU t i j) * R.x_hat t j =
            (R.state t).rhs i + Deltay t i) /\
      (forall t i j, |DeltaU t i j| <=
        gje_c₃ (R.model t) n *
          matMul n
            (ch14ext_gjePrintedUinvEnvelope
              (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv
                hUinv_one) t)
            (absMatrix n (R.state t).matrix) i j +
          ch14ext_gje1430bPrintedRemainder
            (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv
              hUinv_one) t i j) /\
      (forall t i, |Deltay t i| <=
        gje_c₃ (R.model t) n *
          matMulVec n
            (ch14ext_gjePrintedUinvEnvelope
              (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv
                hUinv_one) t)
            (absVec n (R.state t).rhs) i +
          ch14ext_gje1430cPrintedRemainder
            (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv
              hUinv_one) (fun q => (R.state q).rhs) t i) /\
      (forall i j,
        (fun t => ch14ext_gje1430bPrintedRemainder
          (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv
            hUinv_one) t i j)
          =O[l] (fun t => (R.model t).u ^ 2)) /\
      (forall i,
        (fun t => ch14ext_gje1430cPrintedRemainder
          (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv
            hUinv_one) (fun q => (R.state q).rhs) t i)
          =O[l] (fun t => (R.model t).u ^ 2)) := by
  let F := ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv hUinv_one
  have hwitness : forall t,
      exists DeltaU : Fin n -> Fin n -> Real,
        exists Deltay : Fin n -> Real,
        (forall i : Fin n,
          ∑ j : Fin n,
            ((R.state t).matrix i j + DeltaU i j) * R.x_hat t j =
              (R.state t).rhs i + Deltay i) /\
        (forall i j : Fin n, |DeltaU i j| <= gje_c₃ (R.model t) n *
          ∑ k : Fin n,
            |ch14ext_gjeSourceFamilyXabs R t i k| *
              |(R.state t).matrix k j|) /\
        (forall i : Fin n, |Deltay i| <= gje_c₃ (R.model t) n *
          ∑ j : Fin n,
            |ch14ext_gjeSourceFamilyXabs R t i j| *
              |(R.state t).rhs j|) := by
    intro t
    simpa [ch14ext_gjeSourceFamilyXabs] using
      ch14ext_gjeSourceTrace_stage2_backward_error_14_30abc
        (R.model t) (R.state t) (R.x_hat t) R.dimension_pos
        (R.valid_three t) (R.lu_certificate t).U_lower_zero
        (R.final_matrix t) (R.final_vector t) (R.pivots_nonzero t)
  choose DeltaU Deltay hEq hDeltaU hDeltay using hwitness
  refine ⟨DeltaU, Deltay, hEq, ?_, ?_, ?_, ?_⟩
  . intro t i j
    have hraw : |DeltaU t i j| <= gje_c₃ (R.model t) n *
        matMul n (ch14ext_gjeExactQPEnvelope F t)
          (absMatrix n (R.state t).matrix) i j := by
      have hEnvelope : ch14ext_gjeExactQPEnvelope F t =
          ch14ext_gjeSourceFamilyXabs R t := by rfl
      calc
        |DeltaU t i j| <= gje_c₃ (R.model t) n *
            ∑ k : Fin n,
              |ch14ext_gjeSourceFamilyXabs R t i k| *
                |(R.state t).matrix k j| := hDeltaU t i j
        _ = gje_c₃ (R.model t) n *
            matMul n (ch14ext_gjeExactQPEnvelope F t)
              (absMatrix n (R.state t).matrix) i j := by
          rw [hEnvelope]
          unfold matMul absMatrix
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_of_nonneg]
          exact ch14ext_gjeXabs_nonneg n
            (ch14ext_gjeSourceStages (R.model t) (R.state t))
            (ch14ext_gjeSourceQ (R.model t) (R.state t)) 1 (n - 1) i k
    have hreplace :=
      ch14ext_gjeExactQPEnvelope_matMul_le_printed_add_correction F t
        (absMatrix n (R.state t).matrix) (fun _ _ => abs_nonneg _) i j
    have hc := gje_c3_nonneg (R.model t) n R.dimension_pos (R.valid_three t)
    calc
      |DeltaU t i j| <= gje_c₃ (R.model t) n *
          matMul n (ch14ext_gjeExactQPEnvelope F t)
            (absMatrix n (R.state t).matrix) i j := hraw
      _ <= gje_c₃ (R.model t) n *
          (matMul n (ch14ext_gjePrintedUinvEnvelope F t)
              (absMatrix n (R.state t).matrix) i j +
            gje_c₃ (R.model t) n *
              matMul n (ch14ext_gjePrintedEnvelopeCorrection F t)
                (absMatrix n (R.state t).matrix) i j) :=
        mul_le_mul_of_nonneg_left hreplace hc
      _ = gje_c₃ (R.model t) n *
          matMul n (ch14ext_gjePrintedUinvEnvelope F t)
            (absMatrix n (R.state t).matrix) i j +
          ch14ext_gje1430bPrintedRemainder F t i j := by
        unfold ch14ext_gje1430bPrintedRemainder
        dsimp only [F, ch14ext_gjeSourcePrintedEnvelopeFamily]
        ring
  . intro t i
    have hraw : |Deltay t i| <= gje_c₃ (R.model t) n *
        matMulVec n (ch14ext_gjeExactQPEnvelope F t)
          (absVec n (R.state t).rhs) i := by
      have hEnvelope : ch14ext_gjeExactQPEnvelope F t =
          ch14ext_gjeSourceFamilyXabs R t := by rfl
      calc
        |Deltay t i| <= gje_c₃ (R.model t) n *
            ∑ j : Fin n,
              |ch14ext_gjeSourceFamilyXabs R t i j| *
                |(R.state t).rhs j| := hDeltay t i
        _ = gje_c₃ (R.model t) n *
            matMulVec n (ch14ext_gjeExactQPEnvelope F t)
              (absVec n (R.state t).rhs) i := by
          rw [hEnvelope]
          unfold matMulVec absVec
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_of_nonneg]
          exact ch14ext_gjeXabs_nonneg n
            (ch14ext_gjeSourceStages (R.model t) (R.state t))
            (ch14ext_gjeSourceQ (R.model t) (R.state t)) 1 (n - 1) i j
    have hreplace :=
      ch14ext_gjeExactQPEnvelope_matMulVec_le_printed_add_correction F t
        (absVec n (R.state t).rhs) (fun _ => abs_nonneg _) i
    have hc := gje_c3_nonneg (R.model t) n R.dimension_pos (R.valid_three t)
    calc
      |Deltay t i| <= gje_c₃ (R.model t) n *
          matMulVec n (ch14ext_gjeExactQPEnvelope F t)
            (absVec n (R.state t).rhs) i := hraw
      _ <= gje_c₃ (R.model t) n *
          (matMulVec n (ch14ext_gjePrintedUinvEnvelope F t)
              (absVec n (R.state t).rhs) i +
            gje_c₃ (R.model t) n *
              matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t)
                (absVec n (R.state t).rhs) i) :=
        mul_le_mul_of_nonneg_left hreplace hc
      _ = gje_c₃ (R.model t) n *
          matMulVec n (ch14ext_gjePrintedUinvEnvelope F t)
            (absVec n (R.state t).rhs) i +
          ch14ext_gje1430cPrintedRemainder F
            (fun q => (R.state q).rhs) t i := by
        unfold ch14ext_gje1430cPrintedRemainder
        dsimp only [F, ch14ext_gjeSourcePrintedEnvelopeFamily]
        ring
  . intro i j
    exact ch14ext_gje1430bPrintedRemainder_isBigO_unit_sq F i j
  . intro i
    exact ch14ext_gje1430cPrintedRemainder_isBigO_unit_sq F
      (fun q => (R.state q).rhs) R.y_isBigO_one i

/-- Replacing the exact `|Q|Pabs` middle factor in the residual action by
`|Uhat||Uhat^-1|` leaves one explicit factor of `c3`. -/
theorem ch14ext_gjeResidualS2_exact_le_printed_add_correction
    {iota : Type*} {l : Filter iota} {n : Nat}
    (F : Ch14GJEPrintedEnvelopeFamily iota l n)
    (L : iota -> Fin n -> Fin n -> Real)
    (x_hat : iota -> Fin n -> Real)
    (t : iota) (i : Fin n) :
    ch14ext_gjeResidualS2 n (L t) (ch14ext_gjeExactQPEnvelope F t)
        (F.U_hat t) (x_hat t) i <=
      ch14ext_gjeResidualS2 n (L t) (ch14ext_gjePrintedUinvEnvelope F t)
          (F.U_hat t) (x_hat t) i +
        gje_c₃ (F.model t) n *
          ch14ext_gjeResidualPrintedEnvelopeCorrection F L x_hat t i := by
  let w := matMulVec n (absMatrix n (F.U_hat t)) (absVec n (x_hat t))
  have hw : forall j : Fin n, 0 <= w j := by
    intro j
    unfold w matMulVec absMatrix absVec
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hinner : forall a : Fin n,
      matMulVec n (ch14ext_gjeExactQPEnvelope F t) w a <=
        matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) w a +
          gje_c₃ (F.model t) n *
            matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) w a := by
    intro a
    exact ch14ext_gjeExactQPEnvelope_matMulVec_le_printed_add_correction
      F t w hw a
  have hExactAbs : absMatrix n (ch14ext_gjeExactQPEnvelope F t) =
      ch14ext_gjeExactQPEnvelope F t := by
    funext a k
    exact abs_of_nonneg (ch14ext_gjeExactQPEnvelope_nonneg F t a k)
  have hPrintedAbs : absMatrix n (ch14ext_gjePrintedUinvEnvelope F t) =
      ch14ext_gjePrintedUinvEnvelope F t := by
    funext a k
    exact abs_of_nonneg (ch14ext_gjePrintedUinvEnvelope_nonneg F t a k)
  let p := matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) w
  let cvec := matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) w
  have hlin :
      matMulVec n (absMatrix n (L t))
          (fun a => p a + gje_c₃ (F.model t) n * cvec a) i =
        matMulVec n (absMatrix n (L t)) p i +
          gje_c₃ (F.model t) n *
            matMulVec n (absMatrix n (L t)) cvec i := by
    unfold matMulVec
    calc
      ∑ a : Fin n,
          absMatrix n (L t) i a *
            (p a + gje_c₃ (F.model t) n * cvec a) =
        ∑ a : Fin n,
          (absMatrix n (L t) i a * p a +
            gje_c₃ (F.model t) n *
              (absMatrix n (L t) i a * cvec a)) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
      _ = (∑ a : Fin n, absMatrix n (L t) i a * p a) +
          ∑ a : Fin n,
            gje_c₃ (F.model t) n *
              (absMatrix n (L t) i a * cvec a) :=
        Finset.sum_add_distrib
      _ = (∑ a : Fin n, absMatrix n (L t) i a * p a) +
          gje_c₃ (F.model t) n *
            ∑ a : Fin n, absMatrix n (L t) i a * cvec a := by
        rw [Finset.mul_sum]
  rw [ch14ext_gjeResidualS2, ch14ext_gjeResidualS2,
    hExactAbs, hPrintedAbs]
  change matMulVec n (absMatrix n (L t))
      (matMulVec n (ch14ext_gjeExactQPEnvelope F t) w) i <= _
  calc
    matMulVec n (absMatrix n (L t))
        (matMulVec n (ch14ext_gjeExactQPEnvelope F t) w) i <=
      matMulVec n (absMatrix n (L t))
        (fun a =>
          matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) w a +
            gje_c₃ (F.model t) n *
              matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) w a) i := by
        unfold matMulVec absMatrix
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hinner a) (abs_nonneg _)
    _ = matMulVec n (absMatrix n (L t))
          (matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) w) i +
        gje_c₃ (F.model t) n *
          ch14ext_gjeResidualPrintedEnvelopeCorrection F L x_hat t i := by
      simpa [p, cvec, w, ch14ext_gjeResidualPrintedEnvelopeCorrection] using hlin

theorem ch14ext_gjeResidualPrintedEnvelopeCorrection_isBigOOne
    {iota : Type*} {l : Filter iota} {n : Nat}
    (F : Ch14GJEPrintedEnvelopeFamily iota l n)
    (L : iota -> Fin n -> Fin n -> Real)
    (x_hat : iota -> Fin n -> Real)
    (hL : MatrixFamilyIsBigOOne l L)
    (hx : VectorFamilyIsBigOOne l x_hat) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeResidualPrintedEnvelopeCorrection F L x_hat t i) := by
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne F.U_hat_isBigO_one)
    (ch14ext_vectorFamily_abs_isBigOOne hx)
  have hCux := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (ch14ext_gjePrintedEnvelopeCorrection_isBigOOne F) hUx
  have hLCux := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hL) hCux
  simpa [ch14ext_gjeResidualPrintedEnvelopeCorrection] using hLCux

theorem ch14ext_gjeSourceResidual1431PrintedRemainder_isBigO_unit_sq
    {iota : Type*} {l : Filter iota} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (U_inv : iota -> Fin n -> Fin n -> Real)
    (hUinv : forall t, IsRightInverse n (R.state t).matrix (U_inv t))
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv)
    (i : Fin n) :
    (fun t => ch14ext_gjeResidual1431PrintedRemainder R
      (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv hUinv_one)
      t i) =O[l] (fun t => (R.model t).u ^ 2) := by
  let F := ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv hUinv_one
  have hHigher := ch14ext_gjeResidualHigherOrder_family_isBigO n R.model
    R.L_hat (ch14ext_gjeSourceFamilyXabs R)
    (fun t => (R.state t).matrix) (fun t => (R.state t).rhs) R.x_hat
    R.unit_tendsto_zero R.L_hat_isBigO_one
    (ch14ext_gjeSourceFamilyXabs_isBigOOne R) R.U_hat_isBigO_one
    R.y_isBigO_one R.x_hat_isBigO_one i
  have hCorr := ch14ext_gjeResidualPrintedEnvelopeCorrection_isBigOOne
    F R.L_hat R.x_hat R.L_hat_isBigO_one R.x_hat_isBigO_one
  have hu : (fun t => (R.model t).u) =O[l] (fun t => (R.model t).u) :=
    Asymptotics.isBigO_refl _ l
  have hc3 := ch14ext_gje_c3_family_isBigO_unit n R.model R.unit_tendsto_zero
  have hcoeff :
      (fun t => 8 * (n : Real) * (R.model t).u * gje_c₃ (R.model t) n)
        =O[l] (fun t => (R.model t).u ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (hu.mul hc3).const_mul_left (8 * (n : Real))
  have hterm :
      (fun t =>
        8 * (n : Real) * (R.model t).u * gje_c₃ (R.model t) n *
          ch14ext_gjeResidualPrintedEnvelopeCorrection F R.L_hat R.x_hat t i)
        =O[l] (fun t => (R.model t).u ^ 2) := by
    simpa only [mul_one] using hcoeff.mul (hCorr i)
  simpa [F, ch14ext_gjeResidual1431PrintedRemainder] using hHigher.add hterm

/-- Higham (14.31), source-active and with the exact printed leading object
`8*n*u*|Lhat||Uhat||Uhat^-1||Uhat||xhat|`. -/
theorem ch14ext_gjeSourceTrace_residual_14_31_printed_vanishing_family_endpoint
    {iota : Type*} {l : Filter iota} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (U_inv : iota -> Fin n -> Fin n -> Real)
    (hUinv : forall t, IsRightInverse n (R.state t).matrix (U_inv t))
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv) :
    (forall t i,
      |b i - matMulVec n A (R.x_hat t) i| <=
        8 * (n : Real) * (R.model t).u *
          ch14ext_gjeResidualS2 n (R.L_hat t)
            (ch14ext_gjePrintedUinvEnvelope
              (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv
                hUinv_one) t)
            (R.state t).matrix (R.x_hat t) i +
        ch14ext_gjeResidual1431PrintedRemainder R
          (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv hUinv_one)
          t i) /\
      forall i,
        (fun t => ch14ext_gjeResidual1431PrintedRemainder R
          (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv hUinv_one)
          t i) =O[l] (fun t => (R.model t).u ^ 2) := by
  let F := ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv hUinv_one
  constructor
  . intro t i
    have hRaw := ch14ext_gjeSourceTrace_overall_residual_14_31
      (R.model t) A (R.L_hat t) b (R.x_hat t) (R.state t)
      (R.lu_certificate t) (R.valid_n t) R.dimension_pos (R.valid_three t)
      (R.final_matrix t) (R.final_vector t) (R.forward_start t)
      (R.pivots_nonzero t) i
    have hRaw' :
        |b i - matMulVec n A (R.x_hat t) i| <=
          8 * (n : Real) * (R.model t).u *
              ch14ext_gjeResidualS2 n (R.L_hat t)
                (ch14ext_gjeSourceFamilyXabs R t)
                (R.state t).matrix (R.x_hat t) i +
            ch14ext_gjeResidualHigherOrder n (R.model t) (R.L_hat t)
              (ch14ext_gjeSourceFamilyXabs R t) (R.state t).matrix
              (R.state t).rhs (R.x_hat t) i := by
      simpa [ch14ext_gjeSourceFamilyXabs] using hRaw
    have hEnvelope : ch14ext_gjeSourceFamilyXabs R t =
        ch14ext_gjeExactQPEnvelope F t := by rfl
    have hCompare := ch14ext_gjeResidualS2_exact_le_printed_add_correction
      F R.L_hat R.x_hat t i
    rw [<- hEnvelope] at hCompare
    have hLeadNonneg : 0 <= 8 * (n : Real) * (R.model t).u :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        (R.model t).u_nonneg
    have hScaled := mul_le_mul_of_nonneg_left hCompare hLeadNonneg
    have hScaled' :
        8 * (n : Real) * (R.model t).u *
            ch14ext_gjeResidualS2 n (R.L_hat t)
              (ch14ext_gjeSourceFamilyXabs R t)
              (R.state t).matrix (R.x_hat t) i <=
          8 * (n : Real) * (R.model t).u *
            (ch14ext_gjeResidualS2 n (R.L_hat t)
                (ch14ext_gjePrintedUinvEnvelope F t)
                (R.state t).matrix (R.x_hat t) i +
              gje_c₃ (R.model t) n *
                ch14ext_gjeResidualPrintedEnvelopeCorrection
                  F R.L_hat R.x_hat t i) := by
      simpa [F, ch14ext_gjeSourcePrintedEnvelopeFamily] using hScaled
    change |b i - matMulVec n A (R.x_hat t) i| <=
      8 * (n : Real) * (R.model t).u *
          ch14ext_gjeResidualS2 n (R.L_hat t)
            (ch14ext_gjePrintedUinvEnvelope F t)
            (R.state t).matrix (R.x_hat t) i +
        (ch14ext_gjeResidualHigherOrder n (R.model t) (R.L_hat t)
            (ch14ext_gjeSourceFamilyXabs R t) (R.state t).matrix
            (R.state t).rhs (R.x_hat t) i +
          8 * (n : Real) * (R.model t).u * gje_c₃ (R.model t) n *
            ch14ext_gjeResidualPrintedEnvelopeCorrection
              F R.L_hat R.x_hat t i)
    calc
      |b i - matMulVec n A (R.x_hat t) i| <=
          8 * (n : Real) * (R.model t).u *
              ch14ext_gjeResidualS2 n (R.L_hat t)
                (ch14ext_gjeSourceFamilyXabs R t)
                (R.state t).matrix (R.x_hat t) i +
            ch14ext_gjeResidualHigherOrder n (R.model t) (R.L_hat t)
              (ch14ext_gjeSourceFamilyXabs R t) (R.state t).matrix
              (R.state t).rhs (R.x_hat t) i := hRaw'
      _ <= 8 * (n : Real) * (R.model t).u *
              (ch14ext_gjeResidualS2 n (R.L_hat t)
                  (ch14ext_gjePrintedUinvEnvelope F t)
                  (R.state t).matrix (R.x_hat t) i +
                gje_c₃ (R.model t) n *
                  ch14ext_gjeResidualPrintedEnvelopeCorrection
                    F R.L_hat R.x_hat t i) +
            ch14ext_gjeResidualHigherOrder n (R.model t) (R.L_hat t)
              (ch14ext_gjeSourceFamilyXabs R t) (R.state t).matrix
              (R.state t).rhs (R.x_hat t) i :=
        add_le_add hScaled' (le_refl _)
      _ = _ := by ring
  . intro i
    exact ch14ext_gjeSourceResidual1431PrintedRemainder_isBigO_unit_sq
      R U_inv hUinv hUinv_one i

/-- Higham (14.32), source-active and with the exact printed leading object

`2*n*u*(|A^-1||Lhat||Uhat| + 3|Uhat^-1||Uhat|)|xhat|`.

The absolute cumulative-product family used only inside the remainder is
proved `O(1)` from the finite source-stage family. -/
theorem ch14ext_gjeSourceTrace_forward_14_32_printed_vanishing_family_endpoint
    {iota : Type*} {l : Filter iota} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (A_inv : Fin n -> Fin n -> Real)
    (U_inv : iota -> Fin n -> Fin n -> Real)
    (x : Fin n -> Real) (z : iota -> Fin n -> Real)
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : forall t, IsRightInverse n (R.state t).matrix (U_inv t))
    (hExact : forall i, matMulVec n A x i = b i)
    (hUz : forall t i,
      matMulVec n (R.state t).matrix (z t) i = (R.state t).rhs i)
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv)
    (hz_one : VectorFamilyIsBigOOne l z) :
    (forall t i,
      |x i - R.x_hat t i| <=
        2 * (n : Real) * (R.model t).u *
          (ch14ext_gjeForwardT1 n A_inv (R.L_hat t)
              (R.state t).matrix (R.x_hat t) i +
            3 * ch14ext_gjeForwardT2 n (absMatrix n (U_inv t))
              (R.state t).matrix (R.x_hat t) i) +
        ch14ext_gjeForwardLiteralHigherOrder n (R.model t) A_inv
          (R.L_hat t) (R.state t).matrix
          (ch14ext_gjeSourceFamilyPabs R t) (U_inv t) (z t)
          (R.state t).rhs (R.x_hat t) i) /\
      forall i,
        (fun t => ch14ext_gjeForwardLiteralHigherOrder n (R.model t) A_inv
          (R.L_hat t) (R.state t).matrix
          (ch14ext_gjeSourceFamilyPabs R t) (U_inv t) (z t)
          (R.state t).rhs (R.x_hat t) i)
          =O[l] (fun t => (R.model t).u ^ 2) := by
  constructor
  . intro t i
    simpa [ch14ext_gjeSourceFamilyPabs] using
      ch14ext_gjeSourceTrace_overall_forward_14_32
        (R.model t) A A_inv (R.L_hat t) (U_inv t) b x (z t)
        (R.x_hat t) (R.state t) (R.lu_certificate t) hAinv (hUinv t)
        (R.valid_n t) R.dimension_pos (R.valid_three t)
        (R.final_matrix t) (R.final_vector t) (R.forward_start t)
        hExact (hUz t) (R.pivots_nonzero t) i
  . intro i
    exact ch14ext_gjeForwardLiteralHigherOrder_family_isBigO n R.model
      (fun _ => A_inv) R.L_hat (fun t => (R.state t).matrix)
      (ch14ext_gjeSourceFamilyPabs R) U_inv z
      (fun t => (R.state t).rhs) R.x_hat R.unit_tendsto_zero
      (ch14ext_fixedMatrix_family_isBigOOne l A_inv)
      R.L_hat_isBigO_one R.U_hat_isBigO_one
      (ch14ext_gjeSourceFamilyPabs_isBigOOne R) hUinv_one hz_one
      R.y_isBigO_one R.x_hat_isBigO_one i

/-- **Higham Theorem 14.5, source-active vanishing-roundoff endpoint.**

Returns both printed equations (14.31) and (14.32), each with its explicit
remainder and a genuine `O(u^2)` proof on a nontrivial filter. -/
theorem ch14ext_gjeSourceTrace_theorem14_5_printed_vanishing_family_endpoint
    {iota : Type*} {l : Filter iota} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (A_inv : Fin n -> Fin n -> Real)
    (U_inv : iota -> Fin n -> Fin n -> Real)
    (x : Fin n -> Real) (z : iota -> Fin n -> Real)
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : forall t, IsRightInverse n (R.state t).matrix (U_inv t))
    (hExact : forall i, matMulVec n A x i = b i)
    (hUz : forall t i,
      matMulVec n (R.state t).matrix (z t) i = (R.state t).rhs i)
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv)
    (hz_one : VectorFamilyIsBigOOne l z) :
    ((forall t i,
      |b i - matMulVec n A (R.x_hat t) i| <=
        8 * (n : Real) * (R.model t).u *
          ch14ext_gjeResidualS2 n (R.L_hat t)
            (ch14ext_gjePrintedUinvEnvelope
              (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv
                hUinv_one) t)
            (R.state t).matrix (R.x_hat t) i +
        ch14ext_gjeResidual1431PrintedRemainder R
          (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv hUinv_one)
          t i) /\
      (forall i,
        (fun t => ch14ext_gjeResidual1431PrintedRemainder R
          (ch14ext_gjeSourcePrintedEnvelopeFamily R U_inv hUinv hUinv_one)
          t i) =O[l] (fun t => (R.model t).u ^ 2))) /\
    ((forall t i,
      |x i - R.x_hat t i| <=
        2 * (n : Real) * (R.model t).u *
          (ch14ext_gjeForwardT1 n A_inv (R.L_hat t)
              (R.state t).matrix (R.x_hat t) i +
            3 * ch14ext_gjeForwardT2 n (absMatrix n (U_inv t))
              (R.state t).matrix (R.x_hat t) i) +
        ch14ext_gjeForwardLiteralHigherOrder n (R.model t) A_inv
          (R.L_hat t) (R.state t).matrix
          (ch14ext_gjeSourceFamilyPabs R t) (U_inv t) (z t)
          (R.state t).rhs (R.x_hat t) i) /\
      (forall i,
        (fun t => ch14ext_gjeForwardLiteralHigherOrder n (R.model t) A_inv
          (R.L_hat t) (R.state t).matrix
          (ch14ext_gjeSourceFamilyPabs R t) (U_inv t) (z t)
          (R.state t).rhs (R.x_hat t) i)
          =O[l] (fun t => (R.model t).u ^ 2))) := by
  exact ⟨
    ch14ext_gjeSourceTrace_residual_14_31_printed_vanishing_family_endpoint
      R U_inv hUinv hUinv_one,
    ch14ext_gjeSourceTrace_forward_14_32_printed_vanishing_family_endpoint
      R A_inv U_inv x z hAinv hUinv hExact hUz hUinv_one hz_one⟩

end Ch14Ext
end NumStability
