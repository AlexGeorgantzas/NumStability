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
import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
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
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.Closure
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.Concrete
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.GaussJordanSPDCorollary
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Basic
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Closure
import NumStability.Source.Higham.Chapter14.Problem15

/-!
# Chapter14 Theorem05 ForwardError GJEFinalDivisionClosure

Canonical destination for material split out of
`NumStability.Algorithms.Ch14GJEFinalDivisionClosure` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open Finset BigOperators
open scoped Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- General-diagonal version of Higham (14.29).  The exact row scaling
`D⁻¹` is retained in the envelope, and the only new first-order summand is
the componentwise error of the literal final divisions. -/
theorem ch14ext_gjeFinalizedSourceTrace_stage2_forward_error_14_29_with_final_division
    {n : Nat} (fp : FPModel) (s : Ch14GJEState n) (z : Fin n -> Real)
    (hn : 1 <= n) (h3 : gammaValid fp 3) (h1 : gammaValid fp 1)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hdiag : forall i : Fin n, s.matrix i i ≠ 0)
    (hUz : forall i : Fin n, matMulVec n s.matrix z i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |z i - ch14ext_gjeFinalizedDivOutput fp s i| <=
        gje_c₃ fp n * ch14ext_gjeForwardRaw n
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          s.matrix z s.rhs i +
        gamma fp 1 * |ch14ext_gjeFinalizedDivOutput fp s i| := by
  let V := ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s
  let xseq := ch14ext_gjeFinalizedSourceTraceRhs fp 1 s
  let Nhat := ch14ext_gjeFinalizedSourceStages fp s
  let P := gje_cumulative_product n Nhat 1 (1 + (n - 1))
  let Pabs := ch14ext_gjeFinalizedSourcePabs fp s
  let D := ch14ext_gjeBeforeFinalDivision fp s |>.matrix
  let R := ch14ext_gjeDiagonalInv n D
  let X := ch14ext_gjeNormalizedPabs n D Pabs
  let xhat := ch14ext_gjeFinalizedDivOutput fp s
  let E : Fin n -> Fin n -> Real := fun a j =>
    V (1 + (n - 1)) a j - matMul n P s.matrix a j
  let e : Fin n -> Real := fun a =>
    xseq (1 + (n - 1)) a - matMulVec n P s.rhs a
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hpiv' : forall t : Nat, (ht : t < n - 1) ->
      V (1 + t) ⟨1 + t, hidx t ht⟩ ⟨1 + t, hidx t ht⟩ ≠ 0 := by
    intro t ht
    simpa [V] using hpiv t ht
  have hrec :=
    ch14ext_gjeFinalizedSourceTrace_recurrence_bounds_14_25b_14_26
      fp s hidx hUpper hpiv' h3
  have hE : forall a j : Fin n, |E a j| <= gje_c₃ fp n *
      ch14ext_boundObj n Nhat s.matrix 1 (n - 1) a j := by
    exact ch14ext_matrixAccumulation_c3 n fp Nhat V 1 hn h3 hidx hrec.1
  have he : forall a : Fin n, |e a| <= gje_c₃ fp n *
      ch14ext_boundVec n Nhat s.rhs 1 (n - 1) a := by
    exact ch14ext_rhsAccumulation_c3 n fp Nhat xseq 1 hn h3 hidx hrec.2
  obtain ⟨DeltaD, hDeltaD0, hDeltaDoff0, hFinal0⟩ :=
    ch14ext_gjeFinalizedDivOutput_diagonal_backward_error_of_upper
      fp s hn hUpper hdiag h1
  have hsum : 1 + (n - 1) = n := by omega
  have hDfinal : V (1 + (n - 1)) = D := by
    funext a j
    rw [hsum]
    rfl
  have hDdiag : forall a : Fin n, D a a ≠ 0 := by
    intro a
    exact ch14ext_gjeBeforeFinalDivision_diag_ne_zero fp s hdiag a
  have hDoff : forall a j : Fin n, a ≠ j -> D a j = 0 := by
    intro a j haj
    have hf := ch14ext_gjeFinalizedSourceTrace_final_diagonal fp s hn hUpper
    change (ch14ext_gjeFinalizedSourceTrace fp 1 s (n - 1)).matrix a j = 0
    rw [hf]
    simp [ch14ext_gjeFinalDiagonal, haj]
  have hDeltaD : forall a j : Fin n,
      |DeltaD a j| <= gamma fp 1 * |D a j| := by
    intro a j
    simpa [D] using hDeltaD0 a j
  have hDeltaDoff : forall a j : Fin n, a ≠ j -> DeltaD a j = 0 :=
    hDeltaDoff0
  have hFinal : forall a : Fin n,
      matMulVec n D xhat a + matMulVec n DeltaD xhat a =
        xseq (1 + (n - 1)) a := by
    intro a
    have hf := hFinal0 a
    have hsplit :
        Finset.univ.sum (fun j : Fin n => (D a j + DeltaD a j) * xhat j) =
          matMulVec n D xhat a + matMulVec n DeltaD xhat a := by
      unfold matMulVec
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    calc
      matMulVec n D xhat a + matMulVec n DeltaD xhat a =
          Finset.univ.sum (fun j : Fin n =>
            (D a j + DeltaD a j) * xhat j) := hsplit.symm
      _ = xseq (1 + (n - 1)) a := by
        simpa [D, xhat, xseq, ch14ext_gjeBeforeFinalDivision,
          ch14ext_gjeFinalizedSourceTraceRhs, hsum] using hf
  have hRD : matMul n R D = idMatrix n := by
    exact ch14ext_gjeDiagonalInv_mul_diagonal n D hDdiag hDoff
  have hUzFn : matMulVec n s.matrix z = s.rhs := by
    funext a
    exact hUz a
  have hEz : forall a : Fin n,
      matMulVec n E z a = matMulVec n D z a - matMulVec n P s.rhs a := by
    intro a
    have hmul : matMulVec n (matMul n P s.matrix) z a =
        matMulVec n P s.rhs a := by
      rw [matMulVec_matMul, hUzFn]
    change (Finset.univ.sum (fun j : Fin n =>
      (V (1 + (n - 1)) a j - matMul n P s.matrix a j) * z j)) = _
    rw [show (Finset.univ.sum (fun j : Fin n =>
        (V (1 + (n - 1)) a j - matMul n P s.matrix a j) * z j)) =
      matMulVec n (V (1 + (n - 1))) z a -
        matMulVec n (matMul n P s.matrix) z a by
          unfold matMulVec
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [hDfinal, hmul]
  have hCore : forall a : Fin n,
      matMulVec n D (fun j => xhat j - z j) a =
        e a - matMulVec n E z a - matMulVec n DeltaD xhat a := by
    intro a
    have hDsub : matMulVec n D (fun j => xhat j - z j) a =
        matMulVec n D xhat a - matMulVec n D z a := by
      unfold matMulVec
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hDsub, hEz]
    change _ =
      (xseq (1 + (n - 1)) a - matMulVec n P s.rhs a) -
        _ - _
    linarith [hFinal a]
  have hDiff : forall a : Fin n,
      xhat a - z a = matMulVec n R
        (fun k => e k - matMulVec n E z k - matMulVec n DeltaD xhat k) a := by
    intro a
    have hcoreFn : matMulVec n D (fun j => xhat j - z j) =
        (fun k => e k - matMulVec n E z k - matMulVec n DeltaD xhat k) := by
      funext k
      exact hCore k
    have hleft : matMulVec n R (matMulVec n D (fun j => xhat j - z j)) a =
        xhat a - z a := by
      rw [← matMulVec_matMul, hRD, matMulVec_id]
    rw [hcoreFn] at hleft
    exact hleft.symm
  have hc : 0 <= gje_c₃ fp n := gje_c3_nonneg fp n hn h3
  have hd : 0 <= gamma fp 1 := gamma_nonneg fp h1
  have hPabs : forall a j : Fin n, 0 <= Pabs a j := by
    intro a j
    exact gje_cumulative_product_abs_nonneg n Nhat 1 (1 + (n - 1)) a j
  have hX : forall a j : Fin n, 0 <= X a j := by
    exact ch14ext_gjeNormalizedPabs_nonneg n D Pabs hPabs
  have hBoundVec : ch14ext_boundVec n Nhat s.rhs 1 (n - 1) =
      matMulVec n Pabs (absVec n s.rhs) := by
    rfl
  have hBoundObj : ch14ext_boundObj n Nhat s.matrix 1 (n - 1) =
      matMul n Pabs (absMatrix n s.matrix) := by
    rfl
  have hRe0 := ch14ext_abs_matMulVec_le_of_vec_bound n R e
    (fun a => gje_c₃ fp n * ch14ext_boundVec n Nhat s.rhs 1 (n - 1) a)
    he
  have hRe : forall a : Fin n,
      |matMulVec n R e a| <= gje_c₃ fp n *
        matMulVec n X (absVec n s.rhs) a := by
    intro a
    calc
      |matMulVec n R e a| <= matMulVec n (absMatrix n R)
          (fun k => gje_c₃ fp n *
            ch14ext_boundVec n Nhat s.rhs 1 (n - 1) k) a := hRe0 a
      _ = gje_c₃ fp n * matMulVec n X (absVec n s.rhs) a := by
        rw [ch14ext_matMulVec_scale, hBoundVec]
        rw [← matMulVec_matMul]
        rfl
  have hEzBound : forall a : Fin n, |matMulVec n E z a| <=
      gje_c₃ fp n * matMulVec n
        (ch14ext_boundObj n Nhat s.matrix 1 (n - 1)) (absVec n z) a := by
    intro a
    exact ch14ext_abs_matMulVec_le_scaled n E
      (ch14ext_boundObj n Nhat s.matrix 1 (n - 1)) z
      (gje_c₃ fp n) hE a
  have hREz0 := ch14ext_abs_matMulVec_le_of_vec_bound n R
    (matMulVec n E z)
    (fun a => gje_c₃ fp n * matMulVec n
      (ch14ext_boundObj n Nhat s.matrix 1 (n - 1)) (absVec n z) a)
    hEzBound
  have hREz : forall a : Fin n,
      |matMulVec n R (matMulVec n E z) a| <= gje_c₃ fp n *
        matMulVec n X
          (matMulVec n (absMatrix n s.matrix) (absVec n z)) a := by
    intro a
    calc
      |matMulVec n R (matMulVec n E z) a| <=
          matMulVec n (absMatrix n R)
            (fun k => gje_c₃ fp n * matMulVec n
              (ch14ext_boundObj n Nhat s.matrix 1 (n - 1))
              (absVec n z) k) a := hREz0 a
      _ = gje_c₃ fp n * matMulVec n X
          (matMulVec n (absMatrix n s.matrix) (absVec n z)) a := by
        rw [ch14ext_matMulVec_scale, hBoundObj]
        unfold X ch14ext_gjeNormalizedPabs R
        rw [matMulVec_matMul]
        congr 1
        apply congrArg (fun v : Fin n -> Real =>
          matMulVec n (absMatrix n (ch14ext_gjeDiagonalInv n D)) v a)
        funext k
        exact matMulVec_matMul n Pabs (absMatrix n s.matrix) (absVec n z) k
  have hRDelta := ch14ext_gjeDiagonalInv_delta_action n D DeltaD xhat
    (gamma fp 1) hd hDdiag hDoff hDeltaDoff hDeltaD
  intro i
  rw [abs_sub_comm, hDiff i]
  have hlin : matMulVec n R
      (fun k => e k - matMulVec n E z k - matMulVec n DeltaD xhat k) i =
      matMulVec n R e i - matMulVec n R (matMulVec n E z) i -
        matMulVec n R (matMulVec n DeltaD xhat) i := by
    unfold matMulVec
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hlin]
  have htri :
      |matMulVec n R e i - matMulVec n R (matMulVec n E z) i -
          matMulVec n R (matMulVec n DeltaD xhat) i| <=
        |matMulVec n R e i| + |matMulVec n R (matMulVec n E z) i| +
          |matMulVec n R (matMulVec n DeltaD xhat) i| := by
    calc
      |matMulVec n R e i - matMulVec n R (matMulVec n E z) i -
          matMulVec n R (matMulVec n DeltaD xhat) i| <=
          |matMulVec n R e i - matMulVec n R (matMulVec n E z) i| +
            |matMulVec n R (matMulVec n DeltaD xhat) i| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le
            (matMulVec n R e i - matMulVec n R (matMulVec n E z) i)
            (-(matMulVec n R (matMulVec n DeltaD xhat) i))
      _ <= (|matMulVec n R e i| +
          |matMulVec n R (matMulVec n E z) i|) +
            |matMulVec n R (matMulVec n DeltaD xhat) i| := by
        apply add_le_add
        . simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (matMulVec n R e i)
              (-(matMulVec n R (matMulVec n E z) i))
        . exact le_rfl
  unfold ch14ext_gjeForwardRaw
  change _ <= gje_c₃ fp n *
      (matMulVec n X
          (matMulVec n (absMatrix n s.matrix) (absVec n z)) i +
        matMulVec n X (absVec n s.rhs) i) + gamma fp 1 * |xhat i|
  nlinarith [htri, hRe i, hREz i, hRDelta i]

/-- **Higham (14.32) for the literal Algorithm 14.4 executor.**  This theorem
uses the actual `fl_div` return vector and has no unit-final-matrix or supplied
final-vector premise. -/
theorem ch14ext_gjeFinalizedSourceTrace_overall_forward_14_32
    {n : Nat} (fp : FPModel)
    (A A_inv L_hat U_inv : Fin n -> Fin n -> Real)
    (b x z : Fin n -> Real) (s : Ch14GJEState n)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : IsRightInverse n s.matrix U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hdiagU : forall i : Fin n, s.matrix i i ≠ 0)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n, matMulVec n s.matrix z i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |x i - ch14ext_gjeFinalizedDivOutput fp s i| <=
        2 * (n : Real) * fp.u *
          (ch14ext_gjeForwardT1 n A_inv L_hat s.matrix
              (ch14ext_gjeFinalizedDivOutput fp s) i +
            3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv) s.matrix
              (ch14ext_gjeFinalizedDivOutput fp s) i) +
        ch14ext_gjeForwardFinalDivisionHigherOrder n fp A_inv L_hat
          s.matrix
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          U_inv z s.rhs (ch14ext_gjeFinalizedDivOutput fp s) i := by
  intro i
  let xhat := ch14ext_gjeFinalizedDivOutput fp s
  let X := ch14ext_gjeNormalizedPabs n
    (ch14ext_gjeBeforeFinalDivision fp s).matrix
    (ch14ext_gjeFinalizedSourcePabs fp s)
  let g := gamma fp n
  let c := gje_c₃ fp n
  let d := gamma fp 1
  let DeltaA : Fin n -> Fin n -> Real := fun a j =>
    matMul n L_hat s.matrix a j - A a j
  have hDeltaA : forall a j : Fin n, |DeltaA a j| <= g *
      Finset.univ.sum (fun k : Fin n => |L_hat a k| * |s.matrix k j|) := by
    intro a j
    simpa [g] using hLU.backward_bound a j
  have hFactor : forall a j : Fin n,
      A a j + DeltaA a j = matMul n L_hat s.matrix a j := by
    intro a j
    unfold DeltaA
    ring
  obtain ⟨DeltaL, hDeltaL0, hForwardRaw⟩ :=
    forwardSub_backward_error fp n L_hat b
      (fun a => by rw [hLU.L_diag a]; norm_num) hLU.L_upper_zero hn
  have hDeltaL : forall a j : Fin n, |DeltaL a j| <= g * |L_hat a j| := by
    intro a j
    simpa [g] using hDeltaL0 a j
  have hForward : forall a : Fin n,
      matMulVec n L_hat s.rhs a + matMulVec n DeltaL s.rhs a = b a := by
    intro a
    have h := hForwardRaw a
    rw [← hyStart] at h
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  have hg : 0 <= g := by simpa [g] using gamma_nonneg fp hn
  have hc : 0 <= c := by simpa [c] using gje_c3_nonneg fp n hnpos h3
  have hd : 0 <= d := by simpa [d] using gamma_nonneg fp h1
  have hFirst := ch14ext_gje_first_stage_forward_split_with_error n
    A A_inv L_hat s.matrix DeltaA DeltaL b x z s.rhs xhat g hg
    hAinv hExact hFactor hForward hUz hDeltaA hDeltaL i
  have hErr : forall a : Fin n, |z a - xhat a| <=
      c * ch14ext_gjeForwardRaw n X s.matrix z s.rhs a + d * |xhat a| := by
    intro a
    simpa [c, d, X, xhat] using
      ch14ext_gjeFinalizedSourceTrace_stage2_forward_error_14_29_with_final_division
        fp s z hnpos h3 h1 hLU.U_lower_zero hdiagU hUz hpiv a
  have hP : forall a j : Fin n,
      0 <= ch14ext_gjeFinalizedSourcePabs fp s a j := by
    intro a j
    exact gje_cumulative_product_abs_nonneg n
      (ch14ext_gjeFinalizedSourceStages fp s) 1 (1 + (n - 1)) a j
  have hX : forall a j : Fin n, 0 <= X a j := by
    exact ch14ext_gjeNormalizedPabs_nonneg n
      (ch14ext_gjeBeforeFinalDivision fp s).matrix
      (ch14ext_gjeFinalizedSourcePabs fp s) hP
  have hSecond := ch14ext_gje_stage2_forward_split_with_final_division n
    s.matrix X z s.rhs xhat c d hc hd hX hUz hErr i
  have hCompare : forall a j : Fin n, X a j <= |U_inv a j| +
      c * matMul n (matMul n X (absMatrix n s.matrix))
        (absMatrix n U_inv) a j := by
    intro a j
    simpa [X, c] using
      ch14ext_gjeFinalizedNormalizedPabs_le_abs_Uinv_add
        fp s U_inv hnpos h3 hLU.U_lower_zero hdiagU hpiv hUinv a j
  have hT2 := ch14ext_gjeForwardT2_le_printed_add_correction n X
    s.matrix U_inv xhat c hCompare i
  have hT2Scaled : 2 * c * ch14ext_gjeForwardT2 n X s.matrix xhat i <=
      2 * c * (ch14ext_gjeForwardT2 n (absMatrix n U_inv)
          s.matrix xhat i +
        c * ch14ext_gjeForwardUinvCorrection n X s.matrix U_inv xhat i) :=
    mul_le_mul_of_nonneg_left hT2 (mul_nonneg (by norm_num) hc)
  have hAbsX := ch14ext_absVec_le_inverse_product n s.matrix U_inv xhat hUinv i
  have hAbsXScaled := mul_le_mul_of_nonneg_left hAbsX hd
  have hTri : |x i - xhat i| <= |x i - z i| + |z i - xhat i| := by
    have heq : x i - xhat i = (x i - z i) + (z i - xhat i) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hCombined : |x i - xhat i| <=
      2 * g * ch14ext_gjeForwardT1 n A_inv L_hat s.matrix xhat i +
      2 * g * ch14ext_gjeForwardFirstStageErrorAction
        n A_inv L_hat s.matrix z xhat i +
      2 * c * ch14ext_gjeForwardT2 n X s.matrix xhat i +
      2 * c * c * ch14ext_gjeForwardQ2 n X s.matrix z s.rhs i +
      2 * c * d * ch14ext_gjeForwardT2 n X s.matrix xhat i +
      d * |xhat i| := by
    linarith [hTri, hFirst, hSecond]
  have hAfterCompare : |x i - xhat i| <=
      2 * g * ch14ext_gjeForwardT1 n A_inv L_hat s.matrix xhat i +
      (2 * c + d) * ch14ext_gjeForwardT2 n (absMatrix n U_inv)
        s.matrix xhat i +
      2 * g * ch14ext_gjeForwardFirstStageErrorAction
        n A_inv L_hat s.matrix z xhat i +
      2 * c * c * ch14ext_gjeForwardQ2 n X s.matrix z s.rhs i +
      2 * c * d * ch14ext_gjeForwardT2 n X s.matrix xhat i +
      2 * c * c * ch14ext_gjeForwardUinvCorrection
        n X s.matrix U_inv xhat i := by
    nlinarith [hCombined, hT2Scaled, hAbsXScaled]
  have hT1nn := ch14ext_gjeForwardT1_nonneg n A_inv L_hat s.matrix xhat i
  have hT2nn := ch14ext_gjeForwardT2_nonneg n (absMatrix n U_inv)
    s.matrix xhat i (fun a j => by simp [absMatrix])
  have hGsplit := ch14ext_gamma_split fp n hn
  have hCcoeff := ch14ext_gje_forward_second_coeff_with_final_division
    fp n h1 h3
  have hCcoeff' : 2 * c + d <=
      6 * (n : Real) * fp.u +
        2 * gje_c3_quadratic_remainder fp n + ch14ext_gammaRem fp 1 := by
    simpa [c, d] using hCcoeff
  have hCscaled := mul_le_mul_of_nonneg_right hCcoeff' hT2nn
  have hFinal : |x i - xhat i| <=
      2 * (n : Real) * fp.u *
        (ch14ext_gjeForwardT1 n A_inv L_hat s.matrix xhat i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv)
            s.matrix xhat i) +
      ch14ext_gjeForwardFinalDivisionHigherOrder n fp A_inv L_hat
        s.matrix X U_inv z s.rhs xhat i := by
    unfold ch14ext_gjeForwardFinalDivisionHigherOrder
    dsimp [g, c, d] at hAfterCompare
    dsimp [c, d] at hCscaled
    rw [hGsplit] at hAfterCompare
    nlinarith [hAfterCompare, hCscaled]
  simpa [xhat, X] using hFinal

/-- **Higham Theorem 14.5, literal successful-run endpoint.**

This pairs (14.31) and (14.32) for the actual Algorithm 14.4 return vector.
All higher-order terms are named explicit expressions; the theorem assumes
neither unit terminal storage nor an externally supplied output vector. -/
theorem ch14ext_gjeFinalizedSourceTrace_theorem14_5
    {n : Nat} (fp : FPModel)
    (A A_inv L_hat U_inv : Fin n -> Fin n -> Real)
    (b x z : Fin n -> Real) (s : Ch14GJEState n)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : IsRightInverse n s.matrix U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hdiagU : forall i : Fin n, s.matrix i i ≠ 0)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n, matMulVec n s.matrix z i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    (forall i : Fin n,
      |b i - matMulVec n A (ch14ext_gjeFinalizedDivOutput fp s) i| <=
        8 * (n : Real) * fp.u *
          ch14ext_gjeResidualS2 n L_hat
            (ch14ext_gjeFinalizedSourceXabs fp s) s.matrix
            (ch14ext_gjeFinalizedDivOutput fp s) i +
        ch14ext_gjeResidualFinalDivisionHigherOrder n fp L_hat
          (ch14ext_gjeFinalizedSourceXabs fp s) s.matrix s.rhs
          (ch14ext_gjeFinalizedDivOutput fp s) i) /\
    (forall i : Fin n,
      |x i - ch14ext_gjeFinalizedDivOutput fp s i| <=
        2 * (n : Real) * fp.u *
          (ch14ext_gjeForwardT1 n A_inv L_hat s.matrix
              (ch14ext_gjeFinalizedDivOutput fp s) i +
            3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv) s.matrix
              (ch14ext_gjeFinalizedDivOutput fp s) i) +
        ch14ext_gjeForwardFinalDivisionHigherOrder n fp A_inv L_hat
          s.matrix
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          U_inv z s.rhs (ch14ext_gjeFinalizedDivOutput fp s) i) := by
  constructor
  . exact ch14ext_gjeFinalizedSourceTrace_overall_residual_14_31
      fp A L_hat b s hLU hn hnpos h1 h3 hdiagU hyStart hpiv
  . exact ch14ext_gjeFinalizedSourceTrace_overall_forward_14_32
      fp A A_inv L_hat U_inv b x z s hLU hAinv hUinv hn hnpos h1 h3
      hdiagU hyStart hExact hUz hpiv

/-- **Higham Theorem 14.5 in the literal printed form.**  This is the paired
successful-run endpoint with printed (14.31), printed (14.32), the actual
componentwise divisions, and explicit named higher-order terms. -/
theorem ch14ext_gjeFinalizedSourceTrace_theorem14_5_printed
    {n : Nat} (fp : FPModel)
    (A A_inv L_hat U_inv : Fin n -> Fin n -> Real)
    (b x z : Fin n -> Real) (s : Ch14GJEState n)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : IsRightInverse n s.matrix U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hdiagU : forall i : Fin n, s.matrix i i ≠ 0)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n, matMulVec n s.matrix z i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    (forall i : Fin n,
      |b i - matMulVec n A (ch14ext_gjeFinalizedDivOutput fp s) i| <=
        8 * (n : Real) * fp.u *
          ch14ext_gjeResidualS2 n L_hat
            (matMul n (absMatrix n s.matrix) (absMatrix n U_inv))
            s.matrix (ch14ext_gjeFinalizedDivOutput fp s) i +
        ch14ext_gjeResidualFinalizedPrintedHigherOrder fp L_hat s.matrix
          U_inv (ch14ext_gjeFinalizedSourceXabs fp s)
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          s.rhs (ch14ext_gjeFinalizedDivOutput fp s) i) /\
    (forall i : Fin n,
      |x i - ch14ext_gjeFinalizedDivOutput fp s i| <=
        2 * (n : Real) * fp.u *
          (ch14ext_gjeForwardT1 n A_inv L_hat s.matrix
              (ch14ext_gjeFinalizedDivOutput fp s) i +
            3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv) s.matrix
              (ch14ext_gjeFinalizedDivOutput fp s) i) +
        ch14ext_gjeForwardFinalDivisionHigherOrder n fp A_inv L_hat
          s.matrix
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          U_inv z s.rhs (ch14ext_gjeFinalizedDivOutput fp s) i) := by
  constructor
  . exact ch14ext_gjeFinalizedSourceTrace_overall_residual_14_31_printed
      fp A L_hat U_inv b s hLU hUinv hn hnpos h1 h3 hdiagU hyStart hpiv
  . exact ch14ext_gjeFinalizedSourceTrace_overall_forward_14_32
      fp A A_inv L_hat U_inv b x z s hLU hAinv hUinv hn hnpos h1 h3
      hdiagU hyStart hExact hUz hpiv

/-- **Corollary 14.6 forward adapter for the literal final-division
executor.**  The leading SPD factors are obtained from the printed (14.32)
objects, and the last vector is the actual terminal `O(u²)` remainder. -/
theorem ch14ext_cor146Finalized_forward_norm2
    {n : Nat} (fp : FPModel)
    (A A_inv L_hat U_inv R_inv : Fin n -> Fin n -> Real)
    (b x z : Fin n -> Real) (s : Ch14GJEState n)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hpivPos : forall i : Fin n, 0 < s.matrix i i)
    (hsym : forall i j : Fin n,
      s.matrix i j = s.matrix i i * L_hat j i)
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : IsInverse n s.matrix U_inv)
    (hRinv : IsInverse n (ch14ext_cor146_scaledUpper n s.matrix) R_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hsmall : (n : Real) * gamma fp n < 1)
    (hdiagU : forall i : Fin n, s.matrix i i ≠ 0)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n, matMulVec n s.matrix z i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    vecNorm2 (fun i : Fin n =>
      x i - ch14ext_gjeFinalizedDivOutput fp s i) <=
      2 * (n : Real) * fp.u *
        ((n : Real) * Real.sqrt n *
            (1 - (n : Real) * gamma fp n)⁻¹ * kappa2 A A_inv +
          3 * (n : Real) *
            Real.sqrt
              (kappa2
                (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
                (nonsingInv n (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)))) *
        vecNorm2 (ch14ext_gjeFinalizedDivOutput fp s) +
      vecNorm2 (fun i =>
        ch14ext_gjeForwardFinalDivisionHigherOrder n fp A_inv L_hat
          s.matrix
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          U_inv z s.rhs (ch14ext_gjeFinalizedDivOutput fp s) i) := by
  let xhat := ch14ext_gjeFinalizedDivOutput fp s
  let X := ch14ext_gjeNormalizedPabs n
    (ch14ext_gjeBeforeFinalDivision fp s).matrix
    (ch14ext_gjeFinalizedSourcePabs fp s)
  let rho : Fin n -> Real := fun i =>
    ch14ext_gjeForwardFinalDivisionHigherOrder n fp A_inv L_hat
      s.matrix X U_inv z s.rhs xhat i
  let lead : Fin n -> Real := fun i =>
    2 * (n : Real) * fp.u *
      (ch14ext_gjeForwardT1 n A_inv L_hat s.matrix xhat i +
        3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv) s.matrix xhat i)
  let xLead : Fin n -> Real := fun i => xhat i + lead i
  let factor := (1 - (n : Real) * gamma fp n)⁻¹
  let R := ch14ext_cor146_scaledUpper n s.matrix
  have hden : 0 < 1 - (n : Real) * gamma fp n := by linarith
  have hfactor : 0 <= factor := le_of_lt (inv_pos.mpr hden)
  have hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n s.matrix))
      ((n : Real) * factor * opNorm2 A) := by
    simpa [factor] using ch14ext_cor146_absLU_budget
      n fp A L_hat s.matrix hLU hpivPos hsym hn hsmall
  have hCond : opNorm2Le
      (matMul n (absMatrix n U_inv) (absMatrix n s.matrix))
      ((n : Real) * kappa2 R R_inv) := by
    simpa [R] using ch14ext_cor146_positivePivot_condU_opNorm2Le
      n L_hat s.matrix U_inv R_inv hpivPos hsym hRinv hUinv
  have hleadNonneg : forall i : Fin n, 0 <= lead i := by
    intro i
    have hT1 := ch14ext_gjeForwardT1_nonneg n A_inv L_hat s.matrix xhat i
    have hT2 := ch14ext_gjeForwardT2_nonneg n (absMatrix n U_inv)
      s.matrix xhat i (fun a j => by simp [absMatrix])
    unfold lead
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg)
      (add_nonneg hT1 (mul_nonneg (by norm_num) hT2))
  have hLeadFwd : forall i : Fin n,
      |xLead i - xhat i| <=
        2 * (n : Real) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n s.matrix)))
              (absVec n xhat) i +
            3 * matMulVec n
              (matMul n (absMatrix n U_inv) (absMatrix n s.matrix))
              (absVec n xhat) i) := by
    intro i
    rw [show xLead i - xhat i = lead i by simp [xLead]]
    rw [abs_of_nonneg (hleadNonneg i)]
    unfold lead
    rw [ch14ext_gjePrintedForwardT1_eq_matrix_action,
      ch14ext_gjePrintedForwardT2_eq_matrix_action]
  have hLeadNormRaw := ch14ext_cor146_forward_twoFactor_of_cond_bound
    n fp A A_inv L_hat s.matrix U_inv xLead xhat factor (kappa2 R R_inv)
    hfactor hAbsLU hCond hLeadFwd
  have hLeadVector : (fun i : Fin n => xLead i - xhat i) = lead := by
    funext i
    simp [xLead]
  have hGram :
      matMul n (fun i j => R j i) R =
        (fun i j => A i j +
          ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j) := by
    have hstruct := ch14ext_cor146_positivePivot_cholesky_backward_error
      n fp A L_hat s.matrix hSPD hLU hpivPos hsym
    funext i j
    simpa only [R] using (hstruct.2.1 i j).symm
  have hkappa := ch14ext_cor146_kappa2_eq_sqrt_kappa2_gram
    n R R_inv hRinv
  have hkappa' : kappa2 R R_inv =
      Real.sqrt
        (kappa2
          (fun i j => A i j +
            ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
          (nonsingInv n (fun i j => A i j +
            ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j))) := by
    simpa only [hGram] using hkappa
  have hLeadNorm : vecNorm2 lead <=
      2 * (n : Real) * fp.u *
        ((n : Real) * Real.sqrt n * factor * kappa2 A A_inv +
          3 * (n : Real) *
            Real.sqrt
              (kappa2
                (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
                (nonsingInv n (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)))) *
        vecNorm2 xhat := by
    rw [← hLeadVector]
    simpa only [hkappa'] using hLeadNormRaw
  have hActual := ch14ext_gjeFinalizedSourceTrace_overall_forward_14_32
    fp A A_inv L_hat U_inv b x z s hLU hAinv hUinv.2 hn hnpos h1 h3
      hdiagU hyStart hExact hUz hpiv
  have hEntry : forall i : Fin n, |x i - xhat i| <= lead i + rho i := by
    intro i
    simpa only [lead, rho, X, xhat] using hActual i
  have hNorm := vecNorm2_le_of_abs_le (fun i : Fin n => x i - xhat i)
    (fun i => lead i + rho i) hEntry
  calc
    vecNorm2 (fun i : Fin n => x i - xhat i) <=
        vecNorm2 (fun i => lead i + rho i) := hNorm
    _ <= vecNorm2 lead + vecNorm2 rho := vecNorm2_add_le lead rho
    _ <= 2 * (n : Real) * fp.u *
          ((n : Real) * Real.sqrt n * factor * kappa2 A A_inv +
            3 * (n : Real) *
              Real.sqrt
                (kappa2
                  (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
                  (nonsingInv n (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)))) *
          vecNorm2 xhat + vecNorm2 rho := by linarith [hLeadNorm]
    _ = _ := by rfl

/-- **Corollary 14.7 forward adapter for the literal final-division
executor.**  The printed `4*n³*(κ∞(A)+3)` leading constant is retained, and
the actual terminal (14.32) remainder is added explicitly. -/
theorem ch14ext_cor147Finalized_forward_relative_infNorm
    {n : Nat} (fp : FPModel)
    (A A_inv L_hat U_inv : Fin n -> Fin n -> Real)
    (b x z : Fin n -> Real) (s : Ch14GJEState n)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLUexact : LUFactSpec n A L_hat s.matrix)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : IsInverse n s.matrix U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hdiagU : forall i : Fin n, s.matrix i i ≠ 0)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n, matMulVec n s.matrix z i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0)
    (hxpos : 0 < infNormVec x) :
    infNormVec (fun i : Fin n =>
        x i - ch14ext_gjeFinalizedDivOutput fp s i) / infNormVec x <=
      4 * (n : Real) ^ 3 * fp.u *
          (kappaInf n (by omega) A A_inv + 3) *
          (infNormVec (ch14ext_gjeFinalizedDivOutput fp s) / infNormVec x) +
        infNormVec (fun i =>
          ch14ext_gjeForwardFinalDivisionHigherOrder n fp A_inv L_hat
            s.matrix
            (ch14ext_gjeNormalizedPabs n
              (ch14ext_gjeBeforeFinalDivision fp s).matrix
              (ch14ext_gjeFinalizedSourcePabs fp s))
            U_inv z s.rhs (ch14ext_gjeFinalizedDivOutput fp s) i) /
          infNormVec x := by
  let xhat := ch14ext_gjeFinalizedDivOutput fp s
  let X := ch14ext_gjeNormalizedPabs n
    (ch14ext_gjeBeforeFinalDivision fp s).matrix
    (ch14ext_gjeFinalizedSourcePabs fp s)
  let rho : Fin n -> Real := fun i =>
    ch14ext_gjeForwardFinalDivisionHigherOrder n fp A_inv L_hat
      s.matrix X U_inv z s.rhs xhat i
  let lead : Fin n -> Real := fun i =>
    2 * (n : Real) * fp.u *
      (ch14ext_gjeForwardT1 n A_inv L_hat s.matrix xhat i +
        3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv) s.matrix xhat i)
  let MLU := matMul n (absMatrix n L_hat) (absMatrix n s.matrix)
  let M1 := matMul n (absMatrix n A_inv) MLU
  let M2 := matMul n (absMatrix n U_inv) (absMatrix n s.matrix)
  let sx := infNormVec xhat
  let kap := kappaInf n (by omega) A A_inv
  let C := 4 * (n : Real) ^ 3 * fp.u * (kap + 3)
  have hURow : higham8_8_rowDiagDominantUpper n s.matrix :=
    ch14ext_exactNoPivotLU_upper_higham8_8 A L_hat s.matrix
      hRow hdet hLUexact
  have hnNat : 0 < n := by omega
  have hn1 : (1 : Real) <= (n : Real) := Nat.one_le_cast.mpr hnNat
  have hsx : 0 <= sx := infNormVec_nonneg xhat
  have hkapEq : kap = infNorm A * infNorm A_inv := by
    exact kappaInf_eq_infNorm_mul_infNorm n hnNat A A_inv
  have hkap0 : 0 <= kap := kappaInf_nonneg n hnNat A A_inv
  have hM2norm : infNorm M2 <= 2 * (n : Real) - 1 := by
    simpa [M2] using
      ch14ext_cor147_condU_infNorm_le n hnNat s.matrix U_inv hURow hUinv
  have hMLUnorm : infNorm MLU <=
      (2 * (n : Real) - 1) * infNorm A := by
    simpa [MLU] using
      ch14ext_cor147_absLU_infNorm_le n hnNat A L_hat s.matrix hLUexact hURow
  have hM1norm : infNorm M1 <= (2 * (n : Real) - 1) * kap := by
    calc
      infNorm M1 <= infNorm (absMatrix n A_inv) * infNorm MLU := by
        simpa [M1] using infNorm_matMul_le hnNat (absMatrix n A_inv) MLU
      _ = infNorm A_inv * infNorm MLU := by
        rw [infNorm_absMatrix hnNat A_inv]
      _ <= infNorm A_inv * ((2 * (n : Real) - 1) * infNorm A) :=
        mul_le_mul_of_nonneg_left hMLUnorm (infNorm_nonneg A_inv)
      _ = (2 * (n : Real) - 1) * kap := by rw [hkapEq]; ring
  have hMV : forall (M : Fin n -> Fin n -> Real) (i : Fin n),
      matMulVec n M (absVec n xhat) i <= infNorm M * sx := by
    intro M i
    calc
      matMulVec n M (absVec n xhat) i <=
          |matMulVec n M (absVec n xhat) i| := le_abs_self _
      _ <= infNormVec (matMulVec n M (absVec n xhat)) := abs_le_infNormVec _ i
      _ <= infNorm M * infNormVec (absVec n xhat) :=
        infNormVec_matMulVec_le hnNat M _
      _ = infNorm M * sx := by rw [infNormVec_absVec hnNat xhat]
  have h2nu : 0 <= 2 * (n : Real) * fp.u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  have hLeadTight : forall i : Fin n, lead i <=
      2 * (n : Real) * fp.u * (2 * (n : Real) - 1) * (kap + 3) * sx := by
    intro i
    have hm1 : matMulVec n M1 (absVec n xhat) i <=
        (2 * (n : Real) - 1) * kap * sx := by
      calc
        matMulVec n M1 (absVec n xhat) i <= infNorm M1 * sx := hMV M1 i
        _ <= ((2 * (n : Real) - 1) * kap) * sx :=
          mul_le_mul_of_nonneg_right hM1norm hsx
        _ = _ := by ring
    have hm2 : matMulVec n M2 (absVec n xhat) i <=
        (2 * (n : Real) - 1) * sx := by
      calc
        matMulVec n M2 (absVec n xhat) i <= infNorm M2 * sx := hMV M2 i
        _ <= (2 * (n : Real) - 1) * sx :=
          mul_le_mul_of_nonneg_right hM2norm hsx
    have hleadEq : lead i = 2 * (n : Real) * fp.u *
        (matMulVec n M1 (absVec n xhat) i +
          3 * matMulVec n M2 (absVec n xhat) i) := by
      unfold lead M1 MLU M2
      rw [ch14ext_gjePrintedForwardT1_eq_matrix_action,
        ch14ext_gjePrintedForwardT2_eq_matrix_action]
    rw [hleadEq]
    calc
      2 * (n : Real) * fp.u *
          (matMulVec n M1 (absVec n xhat) i +
            3 * matMulVec n M2 (absVec n xhat) i) <=
          2 * (n : Real) * fp.u *
            ((2 * (n : Real) - 1) * kap * sx +
              3 * ((2 * (n : Real) - 1) * sx)) := by
        apply mul_le_mul_of_nonneg_left _ h2nu
        linarith
      _ = _ := by ring
  have hpoly : 2 * (n : Real) * (2 * (n : Real) - 1) <=
      4 * (n : Real) ^ 3 := by
    nlinarith [mul_nonneg (show (0 : Real) <= (n : Real) by linarith)
      (sq_nonneg ((n : Real) - 1)),
      mul_nonneg (show (0 : Real) <= (n : Real) by linarith)
        (show (0 : Real) <= 2 * (n : Real) - 1 by linarith)]
  have htail : 0 <= fp.u * (kap + 3) * sx :=
    mul_nonneg (mul_nonneg fp.u_nonneg (by linarith)) hsx
  have hLeadPrinted : forall i : Fin n, lead i <= C * sx := by
    intro i
    calc
      lead i <= 2 * (n : Real) * fp.u * (2 * (n : Real) - 1) *
          (kap + 3) * sx := hLeadTight i
      _ = (2 * (n : Real) * (2 * (n : Real) - 1)) *
          (fp.u * (kap + 3) * sx) := by ring
      _ <= (4 * (n : Real) ^ 3) * (fp.u * (kap + 3) * sx) :=
        mul_le_mul_of_nonneg_right hpoly htail
      _ = C * sx := by unfold C; ring
  have hActual := ch14ext_gjeFinalizedSourceTrace_overall_forward_14_32
    fp A A_inv L_hat U_inv b x z s hLU hAinv hUinv.2 hn hnpos h1 h3
      hdiagU hyStart hExact hUz hpiv
  have hEntry : forall i : Fin n, |x i - xhat i| <= lead i + rho i := by
    intro i
    simpa only [lead, rho, X, xhat] using hActual i
  have hAbs : forall i : Fin n,
      |x i - xhat i| <= C * sx + infNormVec rho := by
    intro i
    linarith [hEntry i, hLeadPrinted i, le_abs_self (rho i),
      abs_le_infNormVec rho i]
  have hC : 0 <= C := by
    unfold C
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg n) 3))
        fp.u_nonneg)
      (by linarith)
  have hNorm : infNormVec (fun i : Fin n => x i - xhat i) <=
      C * sx + infNormVec rho :=
    infNormVec_le_of_abs_le _ hAbs
      (add_nonneg (mul_nonneg hC hsx) (infNormVec_nonneg rho))
  have hdiv := div_le_div_of_nonneg_right hNorm hxpos.le
  calc
    infNormVec (fun i : Fin n => x i - xhat i) / infNormVec x <=
        (C * sx + infNormVec rho) / infNormVec x := hdiv
    _ = C * (sx / infNormVec x) + infNormVec rho / infNormVec x := by
      rw [add_div, mul_div_assoc]
    _ = _ := by rfl

/-- Corollary 14.6 absolute forward bound with the literal printed
`8*n^2*sqrt(n)*u*kappa2(A)` coefficient, for the actual returned vector. -/
theorem ch14ext_cor146Finalized_forward_absolute_source_literal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) (t : I) :
    vecNorm2 (fun i : Fin n =>
      x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) <=
      8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
          kappa2 A A_inv *
          vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t) +
        ch14ext_cor146FinalizedForwardAbsoluteRemainder F t := by
  let factor := (1 - (n : Real) * gamma (F.gje.model t) n)⁻¹
  let khat := ch14ext_cor146ClosureSqrtKappa n A F.gje.L_hat
    (fun s => (F.gje.initial s).matrix) t
  let ksrc := Real.sqrt (kappa2 A A_inv)
  let kap := kappa2 A A_inv
  let a := 2 * (n : Real) ^ 2 * Real.sqrt n * kap
  let d := 6 * (n : Real) ^ 2
  let raw := a * factor + d * khat
  let printed := 8 * (n : Real) ^ 2 * Real.sqrt n * kap
  let corr := ch14ext_cor146ForwardCoefficientCorrection n F.gje.model
    A A_inv F.gje.L_hat (fun s => (F.gje.initial s).matrix) t
  let xhat := ch14ext_gjeFinalizedFamilyOutput F.gje t
  let rho := ch14ext_cor146FinalizedForwardTerminal F t
  have hbase := ch14ext_cor146Finalized_forward_norm2
    (F.gje.model t) A A_inv (F.gje.L_hat t) (F.gje.U_inv t)
      (F.R_inv t) b x (F.gje.z t) (F.gje.initial t) F.spd
      (F.gje.lu_certificate t) (F.computed_pivots_pos t)
      (F.symmetric_factor_relation t) F.uniform_inverse.source_inverse.1
      (F.gje.computed_upper_inverse t) (F.scaled_upper_inverse t)
      (F.gje.valid_n t) F.gje.dimension_pos (F.gje.valid_one t)
      (F.gje.valid_three t) (F.gamma_small t)
      (F.gje.diagonal_nonzero t) (F.gje.forward_start t) F.exact_solution
      (F.gje.upper_solve t) (F.gje.pivots_nonzero t)
  have hAhat : ch14ext_cor146ClosureAhat n A F.gje.L_hat
      (fun s => (F.gje.initial s).matrix) t =
      (fun i j => A i j + ch14ext_cor146_symmetricGEDelta n A
        (F.gje.L_hat t) (F.gje.initial t).matrix i j) := rfl
  have hkap1 := ch14ext_cor146_one_le_kappa2_of_isInverse
    n A A_inv F.gje.dimension_pos F.uniform_inverse.source_inverse
  have hkap0 : 0 <= kap := by
    simpa [kap] using le_trans (by norm_num) hkap1
  have hksrc : ksrc <= kap := by
    simpa [ksrc, kap] using
      ch14ext_cor146_sqrt_kappa2_le_kappa2_of_isInverse
        n A A_inv F.gje.dimension_pos F.uniform_inverse.source_inverse
  have hnR : (1 : Real) <= (n : Real) := by
    exact_mod_cast F.gje.dimension_pos
  have hsqrtn : (1 : Real) <= Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hnR
    simpa using h
  have hksrcScaled : ksrc <= Real.sqrt n * kap := by
    calc
      ksrc <= kap := hksrc
      _ = 1 * kap := by ring
      _ <= Real.sqrt n * kap := mul_le_mul_of_nonneg_right hsqrtn hkap0
  have ha0 : 0 <= a := by
    dsimp [a]
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg n)) hkap0
  have hd0 : 0 <= d := by dsimp [d]; positivity
  have hfactor : factor <= 1 + |factor - 1| := by
    linarith [le_abs_self (factor - 1)]
  have hkhat : khat <= ksrc + |khat - ksrc| := by
    linarith [le_abs_self (khat - ksrc)]
  have hperturbed :
      raw <= a * (1 + |factor - 1|) + d * (ksrc + |khat - ksrc|) := by
    dsimp [raw]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hfactor ha0)
      (mul_le_mul_of_nonneg_left hkhat hd0)
  have hsecond : d * ksrc <= d * (Real.sqrt n * kap) :=
    mul_le_mul_of_nonneg_left hksrcScaled hd0
  have hbaseline : a + d * ksrc <= printed := by
    calc
      a + d * ksrc <= a + d * (Real.sqrt n * kap) :=
        add_le_add (le_refl a) hsecond
      _ = printed := by dsimp [a, d, printed]; ring
  have hcorr : corr = a * |factor - 1| + d * |khat - ksrc| := by
    dsimp [corr, a, d, factor, khat, ksrc, kap]
    rfl
  have hraw : raw <= printed + corr := by
    calc
      raw <= a * (1 + |factor - 1|) +
          d * (ksrc + |khat - ksrc|) := hperturbed
      _ = (a + d * ksrc) +
          (a * |factor - 1| + d * |khat - ksrc|) := by ring
      _ <= printed + (a * |factor - 1| + d * |khat - ksrc|) :=
        add_le_add hbaseline (le_refl _)
      _ = printed + corr := by rw [hcorr]
  have hbase' :
      vecNorm2 (fun i : Fin n => x i - xhat i) <=
        raw * ((F.gje.model t).u * vecNorm2 xhat) + rho := by
    convert hbase using 1 <;>
      simp [raw, a, d, factor, khat, kap, rho, xhat,
        ch14ext_cor146FinalizedForwardTerminal,
        ch14ext_gjeFinalizedFamilyOutput,
        ch14ext_gjeFinalizedFamilyNormalizedPabs,
        ch14ext_cor146ClosureSqrtKappa, hAhat] <;> ring
  have hmult0 : 0 <= (F.gje.model t).u * vecNorm2 xhat :=
    mul_nonneg (F.gje.model t).u_nonneg (vecNorm2_nonneg xhat)
  calc
    vecNorm2 (fun i : Fin n =>
        x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) <=
        raw * ((F.gje.model t).u * vecNorm2 xhat) + rho := hbase'
    _ <= (printed + corr) *
          ((F.gje.model t).u * vecNorm2 xhat) + rho :=
      add_le_add (mul_le_mul_of_nonneg_right hraw hmult0) (le_refl rho)
    _ = 8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
          kappa2 A A_inv *
          vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t) +
        ch14ext_cor146FinalizedForwardAbsoluteRemainder F t := by
      simp only [ch14ext_cor146FinalizedForwardAbsoluteRemainder,
        printed, corr, rho, kap, xhat]
      ring

/-- Corollary 14.6 relative forward bound for the actual returned vector.
The computed/exact norm ratio is removed by the standard `q < 1` bootstrap.
-/
theorem ch14ext_cor146Finalized_forward_relative_source_literal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) (t : I)
    (hbootstrap :
      8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
        kappa2 A A_inv < 1) :
    vecNorm2 (fun i : Fin n =>
        x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) / vecNorm2 x <=
      8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
          kappa2 A A_inv +
        ch14ext_cor146FinalizedForwardRelativeRemainder F t := by
  let xhat := ch14ext_gjeFinalizedFamilyOutput F.gje t
  let e := vecNorm2 (fun i : Fin n => x i - xhat i)
  let xn := vecNorm2 x
  let xhn := vecNorm2 xhat
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  let q := c * (F.gje.model t).u
  let r := ch14ext_cor146FinalizedForwardAbsoluteRemainder F t
  have habs := ch14ext_cor146Finalized_forward_absolute_source_literal F t
  have habs' : e <= q * xhn + r := by
    dsimp [e, xhn, r, xhat]
    calc
      vecNorm2 (fun i : Fin n =>
          x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) <=
          8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
              kappa2 A A_inv *
              vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t) +
            ch14ext_cor146FinalizedForwardAbsoluteRemainder F t := habs
      _ = q * vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t) +
          ch14ext_cor146FinalizedForwardAbsoluteRemainder F t := by
        dsimp [q, c, ch14ext_cor146ForwardPrintedCoefficient]
        ring
  have hxhat : xhn <= xn + e := by
    calc
      xhn = vecNorm2 (fun i : Fin n => x i + (xhat i - x i)) := by
        dsimp [xhn]
        apply congrArg vecNorm2
        funext i
        ring
      _ <= vecNorm2 x + vecNorm2 (fun i : Fin n => xhat i - x i) :=
        vecNorm2_add_le x (fun i : Fin n => xhat i - x i)
      _ = xn + e := by
        dsimp [xn, e]
        rw [vecNorm2_sub_comm]
  have hkap1 := ch14ext_cor146_one_le_kappa2_of_isInverse
    n A A_inv F.gje.dimension_pos F.uniform_inverse.source_inverse
  have hkap0 : 0 <= kappa2 A A_inv := le_trans (by norm_num) hkap1
  have hc0 : 0 <= c := by
    dsimp [c, ch14ext_cor146ForwardPrintedCoefficient]
    positivity
  have hq0 : 0 <= q := mul_nonneg hc0 (F.gje.model t).u_nonneg
  have hq1 : q < 1 := by
    dsimp [q, c, ch14ext_cor146ForwardPrintedCoefficient]
    convert hbootstrap using 1 <;> ring
  have hself : e <= q * (xn + e) + r := by
    exact le_trans habs'
      (add_le_add (mul_le_mul_of_nonneg_left hxhat hq0) (le_refl r))
  have hlinear : e * (1 - q) <= q * xn + r := by
    nlinarith
  have hden : 0 < 1 - q := by linarith
  have hsolve : e <= (q * xn + r) / (1 - q) := by
    rw [le_div_iff₀ hden]
    exact hlinear
  have hrelative : e / xn <= ((q * xn + r) / (1 - q)) / xn :=
    div_le_div_of_nonneg_right hsolve F.exact_solution_nonzero.le
  have hxn : xn = 0 -> False := by
    dsimp [xn]
    exact F.exact_solution_nonzero.ne'
  calc
    vecNorm2 (fun i : Fin n =>
        x i - ch14ext_gjeFinalizedFamilyOutput F.gje t i) / vecNorm2 x =
        e / xn := rfl
    _ <= ((q * xn + r) / (1 - q)) / xn := hrelative
    _ = q + (q ^ 2 * (1 - q)⁻¹ + r * (1 - q)⁻¹ * xn⁻¹) := by
      field_simp [hden.ne', hxn]
      ring
    _ = 8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
          kappa2 A A_inv +
        ch14ext_cor146FinalizedForwardRelativeRemainder F t := by
      simp only [ch14ext_cor146FinalizedForwardRelativeRemainder,
        c, q, r, xn, ch14ext_cor146ForwardPrintedCoefficient]
      ring

end Ch14Ext
end NumStability
