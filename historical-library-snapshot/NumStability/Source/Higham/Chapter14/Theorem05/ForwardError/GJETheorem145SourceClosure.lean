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
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
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
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GJESourceAccumulationBridge
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GaussJordanSourceClosure
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEAsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEPrintedEnvelopeClosure

/-!
# Chapter14 Theorem05 ForwardError GJETheorem145SourceClosure

Canonical destination for material split out of
`NumStability.Algorithms.Ch14GJETheorem145SourceClosure` by wave W08 of the August 2026 repository reorganization.
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

noncomputable def ch14ext_gjeSourceV {n : Nat} (fp : FPModel)
    (s : Ch14GJEState n) : Nat -> Fin n -> Fin n -> Real :=
  ch14ext_gjeSourceTraceMatrix fp 1 s

noncomputable def ch14ext_gjeSourceXseq {n : Nat} (fp : FPModel)
    (s : Ch14GJEState n) : Nat -> Fin n -> Real :=
  ch14ext_gjeSourceTraceRhs fp 1 s

noncomputable def ch14ext_gjeSourceStages {n : Nat} (fp : FPModel)
    (s : Ch14GJEState n) : Fin n -> Fin n -> Fin n -> Real :=
  ch14ext_gjeSeqStages n (ch14ext_gjeSourceV fp s)

noncomputable def ch14ext_gjeSourceQ {n : Nat} (fp : FPModel)
    (s : Ch14GJEState n) : Fin n -> Fin n -> Real :=
  ch14ext_gjeConstructedQ n (ch14ext_gjeSourceV fp s) 1

noncomputable def ch14ext_gjeSourcePabs {n : Nat} (fp : FPModel)
    (s : Ch14GJEState n) : Fin n -> Fin n -> Real :=
  ch14ext_absCumProd n (ch14ext_gjeSourceStages fp s) 1 (n - 1)

noncomputable def ch14ext_gjeSourceXabs {n : Nat} (fp : FPModel)
    (s : Ch14GJEState n) : Fin n -> Fin n -> Real :=
  ch14ext_gjeXabs n (ch14ext_gjeSourceStages fp s)
    (ch14ext_gjeSourceQ fp s) 1 (n - 1)

/-- Higham (14.30a-c) on the recursively executed source trace.

The matrix and right-hand-side recurrence bounds are obtained from
`ch14ext_gjeSourceTrace_recurrence_bounds_14_25b_14_26`.  The inverse of the
signed cumulative stage product is the explicit reverse product
`ch14ext_gjeSourceQ`; neither unrestricted GJE recurrences nor a backward
error conclusion is assumed. -/
theorem ch14ext_gjeSourceTrace_stage2_backward_error_14_30abc {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) (x_hat : Fin n -> Real)
    (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat i = ch14ext_gjeSourceTraceRhs fp 1 s n i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t)
          ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    exists DeltaU : Fin n -> Fin n -> Real, exists Deltay : Fin n -> Real,
      (forall i : Fin n,
        ∑ j : Fin n, (s.matrix i j + DeltaU i j) * x_hat j =
          s.rhs i + Deltay i) /\
      (forall i j : Fin n, |DeltaU i j| <= gje_c₃ fp n *
        ∑ k : Fin n,
          |ch14ext_gjeSourceXabs fp s i k| * |s.matrix k j|) /\
      (forall i : Fin n, |Deltay i| <= gje_c₃ fp n *
        ∑ j : Fin n,
          |ch14ext_gjeSourceXabs fp s i j| * |s.rhs j|) := by
  let V := ch14ext_gjeSourceV fp s
  let xseq := ch14ext_gjeSourceXseq fp s
  let N_hat := ch14ext_gjeSourceStages fp s
  let Q := ch14ext_gjeSourceQ fp s
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hrec := ch14ext_gjeSourceTrace_recurrence_bounds_14_25b_14_26
    fp s hidx hUpper hpiv h3
  have hsum : 1 + (n - 1) = n := by omega
  have hVfinal : V (1 + (n - 1)) = idMatrix n := by
    rw [hsum]
    simpa [V, ch14ext_gjeSourceV] using hfinal
  have hxfinal' : forall i : Fin n, x_hat i = xseq (1 + (n - 1)) i := by
    intro i
    rw [hsum]
    simpa [xseq, ch14ext_gjeSourceXseq] using hxfinal i
  have hQP :
      matMul n Q
        (gje_cumulative_product n N_hat 1 (1 + (n - 1))) = idMatrix n := by
    simpa [Q, N_hat, ch14ext_gjeSourceQ, ch14ext_gjeSourceStages] using
      ch14ext_gjeConstructedQ_isLeftInverse n V 1 hidx
  obtain ⟨DeltaU, Deltay, hEq, hDeltaU, hDeltay⟩ :=
    ch14ext_gje_stage2_backward_error_of_accumulation n fp x_hat N_hat V xseq Q 1
      hnpos h3 hidx hVfinal hxfinal' hQP hrec.1 hrec.2
  refine ⟨DeltaU, Deltay, ?_, ?_, ?_⟩
  . intro i
    simpa [V, xseq, ch14ext_gjeSourceV, ch14ext_gjeSourceXseq,
      ch14ext_gjeSourceTraceMatrix, ch14ext_gjeSourceTraceRhs,
      ch14ext_gjeSourceTrace] using hEq i
  . intro i j
    simpa [V, N_hat, Q, ch14ext_gjeSourceXabs, ch14ext_gjeSourceStages,
      ch14ext_gjeSourceQ, ch14ext_gjeSourceV,
      ch14ext_gjeSourceTraceMatrix, ch14ext_gjeSourceTrace] using hDeltaU i j
  . intro i
    simpa [V, xseq, N_hat, Q, ch14ext_gjeSourceXabs,
      ch14ext_gjeSourceStages, ch14ext_gjeSourceQ, ch14ext_gjeSourceV,
      ch14ext_gjeSourceXseq, ch14ext_gjeSourceTraceMatrix,
      ch14ext_gjeSourceTraceRhs, ch14ext_gjeSourceTrace] using hDeltay i

/-- The constructed cumulative-product inverse differs from the computed
upper-triangular factor by the accumulated source-trace matrix error. -/
theorem ch14ext_gjeSource_constructedQ_sub_U_bound {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n)
    (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t)
          ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0)
    (i j : Fin n) :
    |ch14ext_gjeSourceQ fp s i j - s.matrix i j| <=
      gje_c₃ fp n *
        matMul n (ch14ext_gjeSourceXabs fp s) (absMatrix n s.matrix) i j := by
  let V := ch14ext_gjeSourceV fp s
  let N := ch14ext_gjeSourceStages fp s
  let Q := ch14ext_gjeSourceQ fp s
  let P := gje_cumulative_product n N 1 n
  let E : Fin n -> Fin n -> Real := fun a k =>
    ch14ext_gjeSourceTraceMatrix fp 1 s n a k - matMul n P s.matrix a k
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hrec := ch14ext_gjeSourceTrace_recurrence_bounds_14_25b_14_26
    fp s hidx hUpper hpiv h3
  have hsum : 1 + (n - 1) = n := by omega
  have hE : forall a k : Fin n, |E a k| <=
      gje_c₃ fp n * ch14ext_boundObj n N s.matrix 1 (n - 1) a k := by
    intro a k
    have h := ch14ext_matrixAccumulation_c3 n fp N V 1 hnpos h3 hidx hrec.1 a k
    simpa [E, P, V, N, hsum, ch14ext_gjeSourceV,
      ch14ext_gjeSourceStages, ch14ext_gjeSourceTraceMatrix,
      ch14ext_gjeSourceTrace] using h
  have hQP : matMul n Q P = idMatrix n := by
    have h := ch14ext_gjeConstructedQ_isLeftInverse n V 1 hidx
    rw [hsum] at h
    simpa [Q, P, N, V, ch14ext_gjeSourceQ,
      ch14ext_gjeSourceStages] using h
  have hfinalQ :
      matMul n Q (ch14ext_gjeSourceTraceMatrix fp 1 s n) = Q := by
    rw [hfinal, matMul_id_right]
  have hproductQ : matMul n Q (matMul n P s.matrix) = s.matrix := by
    rw [<- matMul_assoc, hQP, matMul_id_left]
  have hkey : matMul n Q E = fun a k => Q a k - s.matrix a k := by
    funext a k
    have hexpand : matMul n Q E a k =
        matMul n Q (ch14ext_gjeSourceTraceMatrix fp 1 s n) a k -
          matMul n Q (matMul n P s.matrix) a k := by
      show (∑ q : Fin n, Q a q * E q k) =
        (∑ q : Fin n,
          Q a q * ch14ext_gjeSourceTraceMatrix fp 1 s n q k) -
        ∑ q : Fin n, Q a q * matMul n P s.matrix q k
      rw [<- Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun q _ => by
        show Q a q *
          (ch14ext_gjeSourceTraceMatrix fp 1 s n q k -
            matMul n P s.matrix q k) = _
        ring)
    rw [hexpand, hfinalQ, hproductQ]
  have hbound := ch14ext_matMul_abs_bound n Q E
    (ch14ext_boundObj n N s.matrix 1 (n - 1)) (gje_c₃ fp n) hE i j
  have hreassoc :
      matMul n (absMatrix n Q)
          (ch14ext_boundObj n N s.matrix 1 (n - 1)) =
        matMul n (ch14ext_gjeSourceXabs fp s) (absMatrix n s.matrix) := by
    show matMul n (absMatrix n Q)
        (matMul n (ch14ext_absCumProd n N 1 (n - 1))
          (absMatrix n s.matrix)) = _
    rw [<- matMul_assoc]
    rfl
  rw [hreassoc, hkey] at hbound
  simpa [Q, ch14ext_gjeSourceQ] using hbound

/-- The absolute source-stage product is bounded by the exact inverse of the
computed upper-triangular factor plus its explicitly accumulated correction. -/
theorem ch14ext_gjeSource_Pabs_le_abs_Uinv_add {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n)
    (U_inv : Fin n -> Fin n -> Real)
    (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t)
          ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0)
    (hUinv : IsRightInverse n s.matrix U_inv)
    (i j : Fin n) :
    ch14ext_gjeSourcePabs fp s i j <= |U_inv i j| +
      gje_c₃ fp n *
        matMul n
          (matMul n (ch14ext_gjeSourcePabs fp s) (absMatrix n s.matrix))
          (absMatrix n U_inv) i j := by
  let V := ch14ext_gjeSourceV fp s
  let N := ch14ext_gjeSourceStages fp s
  let X := ch14ext_gjeSourcePabs fp s
  let S := gje_cumulative_product n N 1 n
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hrec := ch14ext_gjeSourceTrace_recurrence_bounds_14_25b_14_26
    fp s hidx hUpper hpiv h3
  have hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (1 + (t + 1)) =
        ch14ext_gjeSourceStepMatrix fp n (V (1 + t)) ⟨1 + t, hidx t ht⟩ := by
    intro t ht
    simpa [V, ch14ext_gjeSourceV] using
      ch14ext_gjeSourceTraceMatrix_rec fp 1 s t (hidx t ht)
  have hV0 : forall a k : Fin n, k.val < a.val -> V 1 a k = 0 := by
    intro a k hka
    simpa [V, ch14ext_gjeSourceV, ch14ext_gjeSourceTraceMatrix,
      ch14ext_gjeSourceTrace] using hUpper a k hka
  have hUpperSeq : forall q : Nat, q <= n - 1 ->
      forall a k : Fin n, k.val < a.val -> V (1 + q) a k = 0 :=
    ch14ext_gjeSourceSeq_upper fp V 1 (n - 1) hidx hV0 hVrec
  have hsum : 1 + (n - 1) = n := by omega
  have hX : forall a k : Fin n, X a k = |S a k| := by
    intro a k
    have h := ch14ext_gje_absCumProd_eq_abs_signed n V 1 (n - 1)
      hidx hUpperSeq a k
    rw [hsum] at h
    simpa [X, S, V, N, ch14ext_gjeSourcePabs,
      ch14ext_gjeSourceStages, ch14ext_gjeSourceV] using h
  have hAccum := ch14ext_matrixAccumulation_c3 n fp N V 1 hnpos h3 hidx hrec.1
  have hResidual : forall a k : Fin n,
      |idMatrix n a k - matMul n S s.matrix a k| <=
        gje_c₃ fp n * matMul n X (absMatrix n s.matrix) a k := by
    intro a k
    have h := hAccum a k
    rw [hsum] at h
    change
      |ch14ext_gjeSourceTraceMatrix fp 1 s n a k -
          matMul n S s.matrix a k| <=
        gje_c₃ fp n * matMul n X (absMatrix n s.matrix) a k at h
    rw [hfinal] at h
    exact h
  simpa [X] using
    ch14ext_abs_signed_le_abs_rightInverse_add n S X s.matrix U_inv
      (gje_c₃ fp n) hX hUinv hResidual i j

/-- Higham (14.31) before the first-order printed-envelope replacement.

All LU, forward-substitution, and GJE perturbations are constructed from the
corresponding algorithms.  In particular, the second-stage witnesses come
from `ch14ext_gjeSourceTrace_stage2_backward_error_14_30abc`. -/
theorem ch14ext_gjeSourceTrace_overall_residual_14_31 {n : Nat}
    (fp : FPModel) (A L_hat : Fin n -> Fin n -> Real)
    (b x_hat : Fin n -> Real) (s : Ch14GJEState n)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat i = ch14ext_gjeSourceTraceRhs fp 1 s n i)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t)
          ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |b i - matMulVec n A x_hat i| <=
        8 * (n : Real) * fp.u *
          ch14ext_gjeResidualS2 n L_hat (ch14ext_gjeSourceXabs fp s)
            s.matrix x_hat i +
        ch14ext_gjeResidualHigherOrder n fp L_hat
          (ch14ext_gjeSourceXabs fp s) s.matrix s.rhs x_hat i := by
  intro i
  let X := ch14ext_gjeSourceXabs fp s
  let DeltaA1 : Fin n -> Fin n -> Real := fun a j =>
    matMul n L_hat s.matrix a j - A a j
  have hDeltaA1 : forall a j : Fin n, |DeltaA1 a j| <= gamma fp n *
      ∑ k : Fin n, |L_hat a k| * |s.matrix k j| := by
    intro a j
    exact hLU.backward_bound a j
  have hFactor : forall a j : Fin n,
      A a j + DeltaA1 a j = matMul n L_hat s.matrix a j := by
    intro a j
    unfold DeltaA1
    ring
  obtain ⟨DeltaL, hDeltaL, hForwardRaw⟩ := forwardSub_backward_error fp n L_hat b
    (fun a => by rw [hLU.L_diag a]; norm_num) hLU.L_upper_zero hn
  have hForward : forall a : Fin n,
      matMulVec n L_hat s.rhs a + matMulVec n DeltaL s.rhs a = b a := by
    intro a
    have h := hForwardRaw a
    rw [<- hyStart] at h
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  obtain ⟨DeltaU, Deltay, hStageRaw, hDeltaUraw, hDeltayraw⟩ :=
    ch14ext_gjeSourceTrace_stage2_backward_error_14_30abc fp s x_hat
      hnpos h3 hLU.U_lower_zero hfinal hxfinal hpiv
  have hStage : forall a : Fin n,
      matMulVec n s.matrix x_hat a + matMulVec n DeltaU x_hat a =
        s.rhs a + Deltay a := by
    intro a
    have h := hStageRaw a
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  have hDeltaU : forall a j : Fin n, |DeltaU a j| <= gje_c₃ fp n *
      ∑ k : Fin n, |X a k| * |s.matrix k j| := by
    intro a j
    simpa [X] using hDeltaUraw a j
  have hDeltay : forall a : Fin n, |Deltay a| <= gje_c₃ fp n *
      ∑ j : Fin n, |X a j| * |s.rhs j| := by
    intro a
    simpa [X] using hDeltayraw a
  have hResidual := ch14ext_gje_residual_decomposition_14_33 n A L_hat s.matrix
    DeltaA1 DeltaL DeltaU b s.rhs x_hat Deltay hFactor hForward hStage
  have hR := ch14ext_gjeResidual1433_bound_corrected n L_hat s.matrix X
    DeltaA1 DeltaL DeltaU s.rhs x_hat Deltay (gamma fp n) (gje_c₃ fp n)
    (gamma_nonneg fp hn) (gje_c3_nonneg fp n hnpos h3)
    hDeltaA1 hDeltaL hDeltaU hDeltay hStage i
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hdiag : forall k : Fin n, 1 <= X k k := by
    intro k
    simpa [X, ch14ext_gjeSourceXabs, ch14ext_gjeSourceStages,
      ch14ext_gjeSourceQ] using
      ch14ext_gjeXabs_diag_ge_one n (ch14ext_gjeSourceStages fp s)
        (ch14ext_gjeSourceQ fp s) 1 (n - 1) hidx
        (by
          simpa [ch14ext_gjeSourceQ, ch14ext_gjeSourceStages,
            ch14ext_gjeSourceV] using
            ch14ext_gjeConstructedQ_isLeftInverse n
              (ch14ext_gjeSourceV fp s) 1 hidx)
        k
  have hS12 := ch14ext_gjeResidualS1_le_S2 n L_hat X s.matrix x_hat i hdiag
  have hS2nn := ch14ext_gjeResidualS2_nonneg n L_hat X s.matrix x_hat i
  have hAbsorb :
      2 * gamma fp n * ch14ext_gjeResidualS1 n L_hat s.matrix x_hat i <=
        2 * gamma fp n * ch14ext_gjeResidualS2 n L_hat X s.matrix x_hat i :=
    mul_le_mul_of_nonneg_left hS12
      (mul_nonneg (by norm_num) (gamma_nonneg fp hn))
  have hCoeff := ch14ext_gje_residual_coeff_budget_corrected fp n hn h3
  have hCoeffS2 := mul_le_mul_of_nonneg_right hCoeff hS2nn
  have hresEq : b i - matMulVec n A x_hat i =
      ch14ext_gjeResidual1433 n L_hat s.matrix DeltaA1 DeltaL DeltaU
        x_hat Deltay i := by
    linarith [hResidual i]
  rw [hresEq]
  have hFinal :
      |ch14ext_gjeResidual1433 n L_hat s.matrix DeltaA1 DeltaL DeltaU
          x_hat Deltay i| <=
        8 * (n : Real) * fp.u *
            ch14ext_gjeResidualS2 n L_hat X s.matrix x_hat i +
          ch14ext_gjeResidualHigherOrder n fp L_hat X s.matrix
            s.rhs x_hat i := by
    unfold ch14ext_gjeResidualHigherOrder
    nlinarith [hR, hAbsorb, hCoeffS2]
  simpa [X] using hFinal

/-- Source-active stage-envelope form of Higham (14.32).  The second leading
object is still the absolute cumulative stage product; the next theorem
replaces it by the exact inverse of the computed upper factor. -/
theorem ch14ext_gjeSourceTrace_overall_forward_stage_envelope {n : Nat}
    (fp : FPModel) (A A_inv L_hat : Fin n -> Fin n -> Real)
    (b x z x_hat : Fin n -> Real) (s : Ch14GJEState n)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat i = ch14ext_gjeSourceTraceRhs fp 1 s n i)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n, matMulVec n s.matrix z i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t)
          ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |x i - x_hat i| <=
        2 * (n : Real) * fp.u *
          ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i +
        6 * (n : Real) * fp.u *
          ch14ext_gjeForwardT2 n (ch14ext_gjeSourcePabs fp s)
            s.matrix x_hat i +
        ch14ext_gjeForwardHigherOrder n fp A_inv L_hat s.matrix
          (ch14ext_gjeSourcePabs fp s) z s.rhs x_hat i := by
  intro i
  let P := ch14ext_gjeSourcePabs fp s
  have hP : forall a j : Fin n, 0 <= P a j := by
    intro a j
    exact gje_cumulative_product_abs_nonneg n (ch14ext_gjeSourceStages fp s)
      1 (1 + (n - 1)) a j
  let DeltaA1 : Fin n -> Fin n -> Real := fun a j =>
    matMul n L_hat s.matrix a j - A a j
  have hDeltaA1 : forall a j : Fin n, |DeltaA1 a j| <= gamma fp n *
      ∑ k : Fin n, |L_hat a k| * |s.matrix k j| := by
    intro a j
    exact hLU.backward_bound a j
  have hFactor : forall a j : Fin n,
      A a j + DeltaA1 a j = matMul n L_hat s.matrix a j := by
    intro a j
    unfold DeltaA1
    ring
  obtain ⟨DeltaL, hDeltaL, hForwardRaw⟩ := forwardSub_backward_error fp n L_hat b
    (fun a => by rw [hLU.L_diag a]; norm_num) hLU.L_upper_zero hn
  have hForward : forall a : Fin n,
      matMulVec n L_hat s.rhs a + matMulVec n DeltaL s.rhs a = b a := by
    intro a
    have h := hForwardRaw a
    rw [<- hyStart] at h
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  have hErr : forall a : Fin n, |z a - x_hat a| <=
      gje_c₃ fp n * ch14ext_gjeForwardRaw n P s.matrix z s.rhs a := by
    intro a
    have h := ch14ext_gjeSourceTrace_stage2_forward_error_14_29
      fp s z hnpos h3 hLU.U_lower_zero hfinal hUz hpiv a
    rw [<- hxfinal a] at h
    simpa [P, ch14ext_gjeSourcePabs, ch14ext_gjeSourceStages,
      ch14ext_gjeSourceV, ch14ext_gjeForwardRaw,
      ch14ext_gjeForwardEnvelope, ch14ext_gjeSourceTraceMatrix,
      ch14ext_gjeSourceTraceRhs, ch14ext_gjeSourceTrace] using h
  have hFirst := ch14ext_gje_first_stage_forward_split n A A_inv L_hat s.matrix
    DeltaA1 DeltaL b x z s.rhs x_hat (gamma fp n) (gje_c₃ fp n)
    (gamma_nonneg fp hn) hAinv hExact hFactor hForward hUz hDeltaA1 hDeltaL P hErr i
  have hSecond := ch14ext_gje_stage2_forward_split n s.matrix P z s.rhs
    x_hat (gje_c₃ fp n) (gje_c3_nonneg fp n hnpos h3) hP hUz hErr i
  have htri : |x i - x_hat i| <= |x i - z i| + |z i - x_hat i| := by
    have heq : x i - x_hat i = (x i - z i) + (z i - x_hat i) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hCombined : |x i - x_hat i| <=
      2 * gamma fp n * ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i +
      2 * gje_c₃ fp n * ch14ext_gjeForwardT2 n P s.matrix x_hat i +
      2 * gamma fp n * gje_c₃ fp n *
        ch14ext_gjeForwardQ1 n A_inv L_hat s.matrix P z s.rhs i +
      2 * gje_c₃ fp n * gje_c₃ fp n *
        ch14ext_gjeForwardQ2 n P s.matrix z s.rhs i := by
    linarith
  have hT1nn := ch14ext_gjeForwardT1_nonneg n A_inv L_hat s.matrix x_hat i
  have hT2nn := ch14ext_gjeForwardT2_nonneg n P s.matrix x_hat i hP
  have hGammaTerm :
      2 * gamma fp n * ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i =
        2 * (n : Real) * fp.u *
            ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i +
          2 * ch14ext_gammaRem fp n *
            ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i := by
    rw [ch14ext_gamma_split fp n hn]
    ring
  have hCcoeff : 2 * gje_c₃ fp n <=
      6 * (n : Real) * fp.u + 2 * gje_c3_quadratic_remainder fp n := by
    have h := ch14ext_gje_forward_second_coeff fp n h3
    nlinarith
  have hCterm := mul_le_mul_of_nonneg_right hCcoeff hT2nn
  unfold ch14ext_gjeForwardHigherOrder
  nlinarith [hCombined, hGammaTerm, hCterm]

/-- Higham (14.32) on the recursively executed source trace, with the exact
printed first-order objects

`2*n*u*(|A^-1||Lhat||Uhat| + 3|Uhat^-1||Uhat|)|xhat|`.

The inverse-envelope correction is retained in
`ch14ext_gjeForwardLiteralHigherOrder`. -/
theorem ch14ext_gjeSourceTrace_overall_forward_14_32 {n : Nat}
    (fp : FPModel)
    (A A_inv L_hat U_inv : Fin n -> Fin n -> Real)
    (b x z x_hat : Fin n -> Real) (s : Ch14GJEState n)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : IsRightInverse n s.matrix U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat i = ch14ext_gjeSourceTraceRhs fp 1 s n i)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n, matMulVec n s.matrix z i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t)
          ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |x i - x_hat i| <=
        2 * (n : Real) * fp.u *
          (ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i +
            3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv)
              s.matrix x_hat i) +
        ch14ext_gjeForwardLiteralHigherOrder n fp A_inv L_hat s.matrix
          (ch14ext_gjeSourcePabs fp s) U_inv z s.rhs x_hat i := by
  intro i
  let X := ch14ext_gjeSourcePabs fp s
  have hStage : |x i - x_hat i| <=
      2 * (n : Real) * fp.u *
          ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i +
        6 * (n : Real) * fp.u *
          ch14ext_gjeForwardT2 n X s.matrix x_hat i +
        ch14ext_gjeForwardHigherOrder n fp A_inv L_hat s.matrix X
          z s.rhs x_hat i := by
    simpa [X] using
      ch14ext_gjeSourceTrace_overall_forward_stage_envelope fp A A_inv L_hat
        b x z x_hat s hLU hAinv hn hnpos h3 hfinal hxfinal hyStart hExact
        hUz hpiv i
  have hCompare : forall a j : Fin n,
      X a j <= |U_inv a j| +
        gje_c₃ fp n *
          matMul n (matMul n X (absMatrix n s.matrix))
            (absMatrix n U_inv) a j := by
    intro a j
    simpa [X] using
      ch14ext_gjeSource_Pabs_le_abs_Uinv_add fp s U_inv hnpos h3
        hLU.U_lower_zero hfinal hpiv hUinv a j
  have hT2 := ch14ext_gjeForwardT2_le_printed_add_correction n X s.matrix
    U_inv x_hat (gje_c₃ fp n) hCompare i
  have hLeadNonneg : 0 <= 6 * (n : Real) * fp.u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  have hScaled := mul_le_mul_of_nonneg_left hT2 hLeadNonneg
  have hFinal : |x i - x_hat i| <=
      2 * (n : Real) * fp.u *
        (ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv)
            s.matrix x_hat i) +
      (ch14ext_gjeForwardHigherOrder n fp A_inv L_hat s.matrix X
          z s.rhs x_hat i +
        6 * (n : Real) * fp.u * gje_c₃ fp n *
          ch14ext_gjeForwardUinvCorrection n X s.matrix U_inv x_hat i) := by
    calc
      |x i - x_hat i| <=
          2 * (n : Real) * fp.u *
              ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i +
            6 * (n : Real) * fp.u *
              ch14ext_gjeForwardT2 n X s.matrix x_hat i +
            ch14ext_gjeForwardHigherOrder n fp A_inv L_hat s.matrix X
              z s.rhs x_hat i := hStage
      _ <= 2 * (n : Real) * fp.u *
              ch14ext_gjeForwardT1 n A_inv L_hat s.matrix x_hat i +
            6 * (n : Real) * fp.u *
              (ch14ext_gjeForwardT2 n (absMatrix n U_inv) s.matrix x_hat i +
                gje_c₃ fp n *
                  ch14ext_gjeForwardUinvCorrection n X s.matrix U_inv x_hat i) +
            ch14ext_gjeForwardHigherOrder n fp A_inv L_hat s.matrix X
              z s.rhs x_hat i := by
          nlinarith [hScaled]
      _ = _ := by ring
  simpa [X, ch14ext_gjeForwardLiteralHigherOrder] using hFinal

/-- A fixed finite cumulative product of entrywise `O(1)` stage families is
entrywise `O(1)`. -/
theorem ch14ext_gjeCumulativeProduct_family_isBigOOne
    {iota : Type*} {l : Filter iota} {n : Nat}
    (N : iota -> Fin n -> Fin n -> Fin n -> Real)
    (start steps : Nat)
    (hidx : forall q : Nat, q < steps -> start + q < n)
    (hN : forall q : Nat, (hq : q < steps) ->
      MatrixFamilyIsBigOOne l (fun t => N t ⟨start + q, hidx q hq⟩)) :
    MatrixFamilyIsBigOOne l
      (fun t => gje_cumulative_product n (N t) start (start + steps)) := by
  induction steps with
  | zero =>
      have heq :
          (fun t => gje_cumulative_product n (N t) start (start + 0)) =
            (fun _ : iota => idMatrix n) := by
        funext t
        simpa using gje_cumulative_product_base n (N t) (le_refl start)
      rw [heq]
      exact ch14ext_fixedMatrix_family_isBigOOne l (idMatrix n)
  | succ steps ih =>
      have htop : start + steps < n := hidx steps (Nat.lt_succ_self steps)
      have hidxPrev : forall q : Nat, q < steps -> start + q < n :=
        fun q hq => hidx q (Nat.lt_trans hq (Nat.lt_succ_self steps))
      have hNPrev : forall q : Nat, (hq : q < steps) ->
          MatrixFamilyIsBigOOne l (fun t => N t ⟨start + q, hidxPrev q hq⟩) := by
        intro q hq
        simpa using hN q (Nat.lt_trans hq (Nat.lt_succ_self steps))
      have hPrev := ih hidxPrev hNPrev
      have hTop := hN steps (Nat.lt_succ_self steps)
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfinEq : start + (steps + 1) - 1 = start + steps := by omega
      have hfinLt : start + (steps + 1) - 1 < n := by
        simpa [hfinEq] using htop
      have hfin : (⟨start + (steps + 1) - 1, hfinLt⟩ : Fin n) =
          ⟨start + steps, htop⟩ := by
        apply Fin.ext
        simp [hfinEq]
      have heq :
          (fun t => gje_cumulative_product n (N t) start
            (start + (steps + 1))) =
          (fun t => matMul n (N t ⟨start + steps, htop⟩)
            (gje_cumulative_product n (N t) start (start + steps))) := by
        funext t
        rw [gje_cumulative_product_step n (N t) hstep hfinLt, hfin, hfinEq]
      rw [heq]
      exact ch14ext_matrixFamily_mul_family_isBigOOne hTop hPrev

/-- A fixed finite reverse product of entrywise `O(1)` inverse-stage families
is entrywise `O(1)`. -/
theorem ch14ext_gjeInvCumProd_family_isBigOOne
    {iota : Type*} {l : Filter iota} {n : Nat}
    (Ninv : iota -> Fin n -> Fin n -> Fin n -> Real)
    (start steps : Nat)
    (hidx : forall q : Nat, q < steps -> start + q < n)
    (hN : forall q : Nat, (hq : q < steps) ->
      MatrixFamilyIsBigOOne l (fun t => Ninv t ⟨start + q, hidx q hq⟩)) :
    MatrixFamilyIsBigOOne l
      (fun t => ch14ext_gjeInvCumProd n (Ninv t) start (start + steps)) := by
  induction steps with
  | zero =>
      have heq :
          (fun t => ch14ext_gjeInvCumProd n (Ninv t) start (start + 0)) =
            (fun _ : iota => idMatrix n) := by
        funext t
        simpa using ch14ext_gjeInvCumProd_base n (Ninv t) (le_refl start)
      rw [heq]
      exact ch14ext_fixedMatrix_family_isBigOOne l (idMatrix n)
  | succ steps ih =>
      have htop : start + steps < n := hidx steps (Nat.lt_succ_self steps)
      have hidxPrev : forall q : Nat, q < steps -> start + q < n :=
        fun q hq => hidx q (Nat.lt_trans hq (Nat.lt_succ_self steps))
      have hNPrev : forall q : Nat, (hq : q < steps) ->
          MatrixFamilyIsBigOOne l
            (fun t => Ninv t ⟨start + q, hidxPrev q hq⟩) := by
        intro q hq
        simpa using hN q (Nat.lt_trans hq (Nat.lt_succ_self steps))
      have hPrev := ih hidxPrev hNPrev
      have hTop := hN steps (Nat.lt_succ_self steps)
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfinEq : start + (steps + 1) - 1 = start + steps := by omega
      have hfinLt : start + (steps + 1) - 1 < n := by
        simpa [hfinEq] using htop
      have hfin : (⟨start + (steps + 1) - 1, hfinLt⟩ : Fin n) =
          ⟨start + steps, htop⟩ := by
        apply Fin.ext
        simp [hfinEq]
      have heq :
          (fun t => ch14ext_gjeInvCumProd n (Ninv t) start
            (start + (steps + 1))) =
          (fun t => matMul n
            (ch14ext_gjeInvCumProd n (Ninv t) start (start + steps))
            (Ninv t ⟨start + steps, htop⟩)) := by
        funext t
        rw [ch14ext_gjeInvCumProd_step n (Ninv t) hstep hfinLt,
          hfin, hfinEq]
      rw [heq]
      exact ch14ext_matrixFamily_mul_family_isBigOOne hPrev hTop

noncomputable def ch14ext_gjeSourceInvStages {n : Nat} (fp : FPModel)
    (s : Ch14GJEState n) : Fin n -> Fin n -> Fin n -> Real :=
  ch14ext_gjeSeqStagesInv n (ch14ext_gjeSourceV fp s)

/-- A vanishing-roundoff family of successful executions of Algorithm 14.4.

The two stage-boundedness fields expose concrete finite data.  Global
boundedness of `Pabs`, `Q`, or `Xabs` is deliberately absent and is derived
below by finite-product closure. -/
structure Ch14GJETheorem145SourceFamily
    (iota : Type*) (l : Filter iota) (n : Nat)
    (A : Fin n -> Fin n -> Real) (b : Fin n -> Real) where
  model : iota -> FPModel
  state : iota -> Ch14GJEState n
  L_hat : iota -> Fin n -> Fin n -> Real
  x_hat : iota -> Fin n -> Real
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (nhds 0)
  dimension_pos : 1 <= n
  valid_n : forall t, gammaValid (model t) n
  valid_three : forall t, gammaValid (model t) 3
  lu_certificate : forall t,
    LUBackwardError n A (L_hat t) (state t).matrix (gamma (model t) n)
  final_matrix : forall t,
    ch14ext_gjeSourceTraceMatrix (model t) 1 (state t) n = idMatrix n
  final_vector : forall t i,
    x_hat t i = ch14ext_gjeSourceTraceRhs (model t) 1 (state t) n i
  forward_start : forall t,
    (state t).rhs = fl_forwardSub (model t) n (L_hat t) b
  pivots_nonzero : forall t q, (hq : q < n - 1) ->
    ch14ext_gjeSourceTraceMatrix (model t) 1 (state t) (1 + q)
      ⟨1 + q, by omega⟩ ⟨1 + q, by omega⟩ ≠ 0
  L_hat_isBigO_one : MatrixFamilyIsBigOOne l L_hat
  U_hat_isBigO_one : MatrixFamilyIsBigOOne l (fun t => (state t).matrix)
  y_isBigO_one : VectorFamilyIsBigOOne l (fun t => (state t).rhs)
  x_hat_isBigO_one : VectorFamilyIsBigOOne l x_hat
  stage_isBigO_one : forall k : Fin n,
    MatrixFamilyIsBigOOne l
      (fun t => ch14ext_gjeSourceStages (model t) (state t) k)
  inverse_stage_isBigO_one : forall k : Fin n,
    MatrixFamilyIsBigOOne l
      (fun t => ch14ext_gjeSourceInvStages (model t) (state t) k)

noncomputable def ch14ext_gjeSourceFamilyPabs
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (t : iota) : Fin n -> Fin n -> Real :=
  ch14ext_gjeSourcePabs (R.model t) (R.state t)

noncomputable def ch14ext_gjeSourceFamilyQ
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (t : iota) : Fin n -> Fin n -> Real :=
  ch14ext_gjeSourceQ (R.model t) (R.state t)

noncomputable def ch14ext_gjeSourceFamilyXabs
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (t : iota) : Fin n -> Fin n -> Real :=
  ch14ext_gjeSourceXabs (R.model t) (R.state t)

theorem ch14ext_gjeSourceFamilyPabs_isBigOOne
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b) :
    MatrixFamilyIsBigOOne l (ch14ext_gjeSourceFamilyPabs R) := by
  have hidx : forall q : Nat, q < n - 1 -> 1 + q < n := by omega
  let Nabs : iota -> Fin n -> Fin n -> Fin n -> Real := fun t k i j =>
    |ch14ext_gjeSourceStages (R.model t) (R.state t) k i j|
  have hN : forall q : Nat, (hq : q < n - 1) ->
      MatrixFamilyIsBigOOne l (fun t => Nabs t ⟨1 + q, hidx q hq⟩) := by
    intro q hq
    simpa [Nabs] using
      matrixFamily_abs_isBigOOne
        (R.stage_isBigO_one ⟨1 + q, hidx q hq⟩)
  have hprod := ch14ext_gjeCumulativeProduct_family_isBigOOne
    Nabs 1 (n - 1) hidx hN
  simpa [ch14ext_gjeSourceFamilyPabs, ch14ext_gjeSourcePabs,
    ch14ext_absCumProd, Nabs] using hprod

theorem ch14ext_gjeSourceFamilyQ_isBigOOne
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b) :
    MatrixFamilyIsBigOOne l (ch14ext_gjeSourceFamilyQ R) := by
  have hidx : forall q : Nat, q < n - 1 -> 1 + q < n := by omega
  let Ninv : iota -> Fin n -> Fin n -> Fin n -> Real := fun t =>
    ch14ext_gjeSourceInvStages (R.model t) (R.state t)
  have hN : forall q : Nat, (hq : q < n - 1) ->
      MatrixFamilyIsBigOOne l (fun t => Ninv t ⟨1 + q, hidx q hq⟩) := by
    intro q hq
    simpa [Ninv] using R.inverse_stage_isBigO_one ⟨1 + q, hidx q hq⟩
  have hprod := ch14ext_gjeInvCumProd_family_isBigOOne
    Ninv 1 (n - 1) hidx hN
  simpa [ch14ext_gjeSourceFamilyQ, ch14ext_gjeSourceQ,
    ch14ext_gjeSourceInvStages, Ninv] using hprod

theorem ch14ext_gjeSourceFamilyXabs_isBigOOne
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b) :
    MatrixFamilyIsBigOOne l (ch14ext_gjeSourceFamilyXabs R) := by
  have hQ := matrixFamily_abs_isBigOOne
    (ch14ext_gjeSourceFamilyQ_isBigOOne R)
  have hP := ch14ext_gjeSourceFamilyPabs_isBigOOne R
  have hmul := ch14ext_matrixFamily_mul_family_isBigOOne hQ hP
  simpa [ch14ext_gjeSourceFamilyXabs, ch14ext_gjeSourceXabs,
    ch14ext_gjeXabs, ch14ext_gjeSourceFamilyQ,
    ch14ext_gjeSourceFamilyPabs] using hmul

/-- Instantiate the generic printed-envelope closure with the actual source
trace.  Both proximity fields are proved by the source-active accumulation;
all global boundedness fields are consequences of finite-stage boundedness. -/
noncomputable def ch14ext_gjeSourcePrintedEnvelopeFamily
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (U_inv : iota -> Fin n -> Fin n -> Real)
    (hUinv : forall t, IsRightInverse n (R.state t).matrix (U_inv t))
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv) :
    Ch14GJEPrintedEnvelopeFamily iota l n where
  model := R.model
  U_hat := fun t => (R.state t).matrix
  Q := ch14ext_gjeSourceFamilyQ R
  Pabs := ch14ext_gjeSourceFamilyPabs R
  U_inv := U_inv
  Q_error := fun t =>
    matMul n (ch14ext_gjeSourceFamilyXabs R t)
      (absMatrix n (R.state t).matrix)
  P_error := fun t =>
    matMul n
      (matMul n (ch14ext_gjeSourceFamilyPabs R t)
        (absMatrix n (R.state t).matrix))
      (absMatrix n (U_inv t))
  unit_tendsto_zero := R.unit_tendsto_zero
  dimension_pos := R.dimension_pos
  valid_three := R.valid_three
  inverse_certificate := hUinv
  Pabs_nonneg := by
    intro t i j
    exact gje_cumulative_product_abs_nonneg n
      (ch14ext_gjeSourceStages (R.model t) (R.state t))
      1 (1 + (n - 1)) i j
  Q_error_nonneg := by
    intro t i j
    unfold matMul absMatrix
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg
        (ch14ext_gjeXabs_nonneg n
          (ch14ext_gjeSourceStages (R.model t) (R.state t))
          (ch14ext_gjeSourceQ (R.model t) (R.state t)) 1 (n - 1) i k)
        (abs_nonneg _)
  P_error_nonneg := by
    intro t i j
    unfold matMul absMatrix
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg
    . exact Finset.sum_nonneg fun q _ =>
        mul_nonneg
          (gje_cumulative_product_abs_nonneg n
            (ch14ext_gjeSourceStages (R.model t) (R.state t))
            1 (1 + (n - 1)) i q)
          (abs_nonneg _)
    . exact abs_nonneg _
  Q_proximity := by
    intro t i j
    simpa [ch14ext_gjeSourceFamilyQ, ch14ext_gjeSourceFamilyXabs] using
      ch14ext_gjeSource_constructedQ_sub_U_bound
        (R.model t) (R.state t) R.dimension_pos (R.valid_three t)
        (R.lu_certificate t).U_lower_zero (R.final_matrix t)
        (R.pivots_nonzero t) i j
  P_upper := by
    intro t i j
    simpa [ch14ext_gjeSourceFamilyPabs] using
      ch14ext_gjeSource_Pabs_le_abs_Uinv_add
        (R.model t) (R.state t) (U_inv t) R.dimension_pos (R.valid_three t)
        (R.lu_certificate t).U_lower_zero (R.final_matrix t)
        (R.pivots_nonzero t) (hUinv t) i j
  U_hat_isBigO_one := R.U_hat_isBigO_one
  U_inv_isBigO_one := hUinv_one
  Q_error_isBigO_one := by
    exact ch14ext_matrixFamily_mul_family_isBigOOne
      (ch14ext_gjeSourceFamilyXabs_isBigOOne R)
      (matrixFamily_abs_isBigOOne R.U_hat_isBigO_one)
  P_error_isBigO_one := by
    exact ch14ext_matrixFamily_mul_family_isBigOOne
      (ch14ext_matrixFamily_mul_family_isBigOOne
        (ch14ext_gjeSourceFamilyPabs_isBigOOne R)
        (matrixFamily_abs_isBigOOne R.U_hat_isBigO_one))
      (matrixFamily_abs_isBigOOne hUinv_one)
  exact_envelope_isBigO_one := by
    simpa [ch14ext_gjeExactQPEnvelope, ch14ext_gjeSourceFamilyQ,
      ch14ext_gjeSourceFamilyPabs, ch14ext_gjeSourceFamilyXabs,
      ch14ext_gjeSourceXabs, ch14ext_gjeXabs] using
      ch14ext_gjeSourceFamilyXabs_isBigOOne R

noncomputable def ch14ext_gjeResidualPrintedEnvelopeCorrection
    {iota : Type*} {l : Filter iota} {n : Nat}
    (F : Ch14GJEPrintedEnvelopeFamily iota l n)
    (L : iota -> Fin n -> Fin n -> Real)
    (x_hat : iota -> Fin n -> Real)
    (t : iota) (i : Fin n) : Real :=
  matMulVec n (absMatrix n (L t))
    (matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t)
      (matMulVec n (absMatrix n (F.U_hat t)) (absVec n (x_hat t)))) i

noncomputable def ch14ext_gjeResidual1431PrintedRemainder
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (R : Ch14GJETheorem145SourceFamily iota l n A b)
    (F : Ch14GJEPrintedEnvelopeFamily iota l n)
    (t : iota) (i : Fin n) : Real :=
  ch14ext_gjeResidualHigherOrder n (R.model t) (R.L_hat t)
      (ch14ext_gjeSourceFamilyXabs R t) (R.state t).matrix
      (R.state t).rhs (R.x_hat t) i +
    8 * (n : Real) * (R.model t).u * gje_c₃ (R.model t) n *
      ch14ext_gjeResidualPrintedEnvelopeCorrection F R.L_hat R.x_hat t i

end Ch14Ext
end NumStability
