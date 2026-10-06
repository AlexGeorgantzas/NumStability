/-
# Higham, Chapter 14, Corollary 14.6: residual-envelope closure

This file closes the fixed-model comparison between the concrete GJE envelope
and Higham's printed `|L_hat||U_hat||U_hat^-1||U_hat|` object.  It also proves
genuine family-level Landau bounds for the resulting explicit remainder under
uniformly bounded algorithm data.
-/

import NumStability.Algorithms.Ch14Corollary146Concrete
import NumStability.Algorithms.Ch14GaussJordanQConstruction
import Mathlib.Analysis.Asymptotics.Lemmas

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

set_option maxHeartbeats 1000000

/-! ## Exact envelope comparison -/

/-- If `Q*S = I` and `I-S*U` is bounded by `c*P*|U|`, then
`Q = U + Q*(I-S*U)` gives the corresponding absolute comparison. -/
theorem ch14ext_cor146_abs_constructedQ_le_abs_U_add
    (n : ℕ) (Q S P X U : Fin n → Fin n → ℝ) (c : ℝ)
    (hQS : matMul n Q S = idMatrix n)
    (hX : X = matMul n (absMatrix n Q) P)
    (hResidual : ∀ i j : Fin n,
      |idMatrix n i j - matMul n S U i j| ≤
        c * matMul n P (absMatrix n U) i j) :
    ∀ i j : Fin n,
      |Q i j| ≤ |U i j| + c * matMul n X (absMatrix n U) i j := by
  intro i j
  let E : Fin n → Fin n → ℝ := fun a b =>
    idMatrix n a b - matMul n S U a b
  let B : Fin n → Fin n → ℝ := matMul n P (absMatrix n U)
  have hQSU : matMul n Q (matMul n S U) = U := by
    rw [← matMul_assoc n Q S U, hQS, matMul_id_left]
  have hQE : matMul n Q E i j = Q i j - U i j := by
    calc
      matMul n Q E i j =
          matMul n Q (idMatrix n) i j -
            matMul n Q (matMul n S U) i j := by
        unfold E matMul
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
      _ = Q i j - U i j := by rw [matMul_id_right, hQSU]
  have hTransport := ch14ext_matMul_abs_bound n Q E B c
    (by intro a b; simpa [E, B] using hResidual a b) i j
  have hTransport' : |Q i j - U i j| ≤
      c * matMul n X (absMatrix n U) i j := by
    rw [← hQE]
    calc
      |matMul n Q E i j| ≤
          c * matMul n (absMatrix n Q) B i j := hTransport
      _ = c * matMul n X (absMatrix n U) i j := by
        simp only [B]
        rw [← matMul_assoc n (absMatrix n Q) P (absMatrix n U), ← hX]
  calc
    |Q i j| = |U i j + (Q i j - U i j)| := by ring_nf
    _ ≤ |U i j| + |Q i j - U i j| := abs_add_le _ _
    _ ≤ |U i j| + c * matMul n X (absMatrix n U) i j := by
      linarith

/-- Combining the two exact inverse comparisons gives the fixed-model bridge

`X <= |U||U^-1| + 2*c*X|U||U^-1|`.

The two `c` terms respectively account for replacing the signed cumulative
product by `U^-1` and replacing the constructed inverse `Q` by `U`. -/
theorem ch14ext_cor146_envelope_le_printed_add_correction
    (n : ℕ) (Q P X U U_inv : Fin n → Fin n → ℝ) (c : ℝ)
    (hX : X = matMul n (absMatrix n Q) P)
    (hP : ∀ i j : Fin n,
      P i j ≤ |U_inv i j| +
        c * matMul n (matMul n P (absMatrix n U))
          (absMatrix n U_inv) i j)
    (hQ : ∀ i j : Fin n,
      |Q i j| ≤ |U i j| + c * matMul n X (absMatrix n U) i j) :
    ∀ i j : Fin n,
      X i j ≤
        matMul n (absMatrix n U) (absMatrix n U_inv) i j +
        2 * c * matMul n (matMul n X (absMatrix n U))
          (absMatrix n U_inv) i j := by
  intro i j
  let AU := absMatrix n U
  let AI := absMatrix n U_inv
  let D := matMul n (matMul n P AU) AI
  let C := matMul n (matMul n X AU) AI
  have hCorr : matMul n (absMatrix n Q) D = C := by
    simp only [D, C]
    rw [← matMul_assoc n (absMatrix n Q) (matMul n P AU) AI,
      ← matMul_assoc n (absMatrix n Q) P AU, ← hX]
  have hPstep : X i j ≤
      matMul n (absMatrix n Q) AI i j + c * C i j := by
    calc
      X i j = ∑ k : Fin n, |Q i k| * P k j := by
        rw [hX]
        rfl
      _ ≤ ∑ k : Fin n, |Q i k| * (|U_inv k j| + c * D k j) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (by simpa [D, AU, AI] using hP k j)
          (abs_nonneg _)
      _ = matMul n (absMatrix n Q) AI i j +
          c * matMul n (absMatrix n Q) D i j := by
        unfold matMul absMatrix
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = matMul n (absMatrix n Q) AI i j + c * C i j := by rw [hCorr]
  have hQstep : matMul n (absMatrix n Q) AI i j ≤
      matMul n AU AI i j + c * C i j := by
    calc
      matMul n (absMatrix n Q) AI i j =
          ∑ k : Fin n, |Q i k| * |U_inv k j| := rfl
      _ ≤ ∑ k : Fin n,
          (|U i k| + c * matMul n X AU i k) * |U_inv k j| := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (by simpa [AU] using hQ i k)
          (abs_nonneg _)
      _ = matMul n AU AI i j +
          c * matMul n (matMul n X AU) AI i j := by
        unfold matMul
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        simp only [AI, absMatrix]
        ring
      _ = matMul n AU AI i j + c * C i j := rfl
  simpa [AU, AI, C] using (show X i j ≤
      matMul n AU AI i j + 2 * c * C i j by linarith)

/-- The printed first-order object in (14.31). -/
noncomputable def ch14ext_cor146PrintedResidualObject
    (n : ℕ) (L U U_inv : Fin n → Fin n → ℝ)
    (x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n
    (matMul n
      (matMul n (absMatrix n L) (absMatrix n U))
      (matMul n (absMatrix n U_inv) (absMatrix n U)))
    (absVec n x_hat) i

/-- The exact correction object generated by the fixed-model envelope bridge:
`|L| X |U| |U^-1| |U| |x_hat|`. -/
noncomputable def ch14ext_cor146ResidualBridgeCorrection
    (n : ℕ) (L X U U_inv : Fin n → Fin n → ℝ)
    (x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n L)
    (matMulVec n X
      (matMulVec n (absMatrix n U)
        (matMulVec n (absMatrix n U_inv)
          (matMulVec n (absMatrix n U) (absVec n x_hat))))) i

/-- The concrete GJE construction supplies both comparisons needed by the
fixed-model envelope bridge.  In particular, this theorem has no hypothesis
whose conclusion is the target residual estimate. -/
theorem ch14ext_cor146_concrete_envelope_le_printed_add_correction
    (n : Nat) (fp : FPModel)
    (V : Nat -> Fin n -> Fin n -> Real) (start : Nat)
    (U_inv : Fin n -> Fin n -> Real)
    (hLower : forall i j : Fin n, j.val < i.val -> V start i j = 0)
    (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hidx : forall t : Nat, t < n - 1 -> start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t))
          ⟨start + t, hidx t ht⟩)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      Not (V (start + t) ⟨start + t, hidx t ht⟩
        ⟨start + t, hidx t ht⟩ = 0))
    (hUinv : IsRightInverse n (V start) U_inv) :
    forall i j : Fin n,
      ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
          (ch14ext_gjeConstructedQ n V start) start (n - 1) i j <=
        matMul n (absMatrix n (V start)) (absMatrix n U_inv) i j +
          2 * gje_c₃ fp n *
            matMul n
              (matMul n
                (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                  (ch14ext_gjeConstructedQ n V start) start (n - 1))
                (absMatrix n (V start)))
              (absMatrix n U_inv) i j := by
  let S := gje_cumulative_product n (ch14ext_gjeSeqStages n V)
    start (start + (n - 1))
  let P := ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1)
  let Q := ch14ext_gjeConstructedQ n V start
  let X := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V) Q start (n - 1)
  let U := V start
  let c := gje_c₃ fp n
  have hUpper : forall t : Nat, t <= n - 1 ->
      forall i j : Fin n, j.val < i.val -> V (start + t) i j = 0 :=
    ch14ext_gjeSeq_upper_triangular fp n V start hidx hLower hVrec hpiv
  have hPabs : forall i j : Fin n, P i j = |S i j| := by
    intro i j
    simpa [P, S] using
      ch14ext_gje_absCumProd_eq_abs_signed n V start (n - 1)
        hidx hUpper i j
  have hAccum := ch14ext_gjeConcrete_matrixAccumulation fp n V start
    hnpos h3 hidx hVrec hpiv
  have hResidual : forall i j : Fin n,
      |idMatrix n i j - matMul n S U i j| <=
        c * matMul n P (absMatrix n U) i j := by
    intro i j
    have h := hAccum i j
    rw [hVfinal] at h
    simpa [S, P, U, c, ch14ext_boundObj] using h
  have hPcompare : forall i j : Fin n,
      P i j <= |U_inv i j| +
        c * matMul n (matMul n P (absMatrix n U))
          (absMatrix n U_inv) i j :=
    ch14ext_abs_signed_le_abs_rightInverse_add n S P U U_inv c
      hPabs hUinv hResidual
  have hQS : matMul n Q S = idMatrix n := by
    simpa [Q, S] using ch14ext_gjeConstructedQ_isLeftInverse n V start hidx
  have hXdef : X = matMul n (absMatrix n Q) P := by
    rfl
  have hQcompare : forall i j : Fin n,
      |Q i j| <= |U i j| + c * matMul n X (absMatrix n U) i j :=
    ch14ext_cor146_abs_constructedQ_le_abs_U_add n Q S P X U c
      hQS hXdef hResidual
  simpa [X, Q, P, U, c] using
    ch14ext_cor146_envelope_le_printed_add_correction
      n Q P X U U_inv c hXdef hPcompare hQcompare

/-- Action form of Higham's printed residual object. -/
theorem ch14ext_cor146PrintedResidualObject_action
    (n : Nat) (L U U_inv : Fin n -> Fin n -> Real)
    (x_hat : Fin n -> Real) (i : Fin n) :
    ch14ext_cor146PrintedResidualObject n L U U_inv x_hat i =
      matMulVec n (absMatrix n L)
        (matMulVec n (absMatrix n U)
          (matMulVec n (absMatrix n U_inv)
            (matMulVec n (absMatrix n U) (absVec n x_hat)))) i := by
  unfold ch14ext_cor146PrintedResidualObject
  simp only [matMulVec_matMul]
  have hinner :
      matMulVec n (matMul n (absMatrix n U_inv) (absMatrix n U))
          (absVec n x_hat) =
        matMulVec n (absMatrix n U_inv)
          (matMulVec n (absMatrix n U) (absVec n x_hat)) := by
    funext a
    exact matMulVec_matMul n (absMatrix n U_inv) (absMatrix n U)
      (absVec n x_hat) a
  rw [hinner]

theorem ch14ext_cor146PrintedResidualObject_nonneg
    (n : Nat) (L U U_inv : Fin n -> Fin n -> Real)
    (x_hat : Fin n -> Real) (i : Fin n) :
    0 <= ch14ext_cor146PrintedResidualObject n L U U_inv x_hat i := by
  rw [ch14ext_cor146PrintedResidualObject_action]
  apply ch14ext_absMatrix_action_nonneg
  intro a
  apply ch14ext_absMatrix_action_nonneg
  intro b
  apply ch14ext_absMatrix_action_nonneg
  intro c
  apply ch14ext_absMatrix_action_nonneg
  intro d
  exact abs_nonneg (x_hat d)

/-- Monotone propagation of the fixed-model matrix bridge through the exact
residual source object. -/
theorem ch14ext_cor146_gjeResidualS2_le_printed_add_correction
    (n : Nat) (L X U U_inv : Fin n -> Fin n -> Real)
    (x_hat : Fin n -> Real) (c : Real)
    (hX : forall i j : Fin n, 0 <= X i j)
    (hBridge : forall i j : Fin n,
      X i j <= matMul n (absMatrix n U) (absMatrix n U_inv) i j +
        2 * c * matMul n (matMul n X (absMatrix n U))
          (absMatrix n U_inv) i j) :
    forall i : Fin n,
      ch14ext_gjeResidualS2 n L X U x_hat i <=
        ch14ext_cor146PrintedResidualObject n L U U_inv x_hat i +
          2 * c *
            ch14ext_cor146ResidualBridgeCorrection n L X U U_inv x_hat i := by
  intro i
  let B := matMul n (absMatrix n U) (absMatrix n U_inv)
  let C := matMul n (matMul n X (absMatrix n U)) (absMatrix n U_inv)
  let w := matMulVec n (absMatrix n U) (absVec n x_hat)
  have hw : forall j : Fin n, 0 <= w j := by
    intro j
    exact ch14ext_absMatrix_action_nonneg n U (absVec n x_hat)
      (fun k => abs_nonneg (x_hat k)) j
  have hXabs : absMatrix n X = X := by
    funext a j
    exact abs_of_nonneg (hX a j)
  have hinner : forall a : Fin n,
      matMulVec n X w a <=
        matMulVec n B w a + 2 * c * matMulVec n C w a := by
    intro a
    calc
      matMulVec n X w a <=
          matMulVec n (fun p q => B p q + 2 * c * C p q) w a := by
        unfold matMulVec
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (hw j)
        simpa [B, C] using hBridge a j
      _ = matMulVec n B w a + 2 * c * matMulVec n C w a := by
        unfold matMulVec
        simp only [add_mul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have houter := ch14ext_matMulVec_mono_nonneg n (absMatrix n L)
    (matMulVec n X w)
    (fun a => matMulVec n B w a + 2 * c * matMulVec n C w a)
    (fun a j => abs_nonneg (L a j)) hinner i
  have hlinear :
      matMulVec n (absMatrix n L)
          (fun a => matMulVec n B w a + 2 * c * matMulVec n C w a) i =
        matMulVec n (absMatrix n L) (matMulVec n B w) i +
          2 * c * matMulVec n (absMatrix n L) (matMulVec n C w) i := by
    unfold matMulVec
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hBaction :
      matMulVec n B w =
        matMulVec n (absMatrix n U)
          (matMulVec n (absMatrix n U_inv) w) := by
    funext a
    simpa [B] using matMulVec_matMul n (absMatrix n U)
      (absMatrix n U_inv) w a
  have hCaction :
      matMulVec n C w =
        matMulVec n X
          (matMulVec n (absMatrix n U)
            (matMulVec n (absMatrix n U_inv) w)) := by
    funext a
    calc
      matMulVec n C w a =
          matMulVec n (matMul n X (absMatrix n U))
            (matMulVec n (absMatrix n U_inv) w) a := by
        simpa [C] using matMulVec_matMul n
          (matMul n X (absMatrix n U)) (absMatrix n U_inv) w a
      _ = matMulVec n X
          (matMulVec n (absMatrix n U)
            (matMulVec n (absMatrix n U_inv) w)) a :=
        matMulVec_matMul n X (absMatrix n U)
          (matMulVec n (absMatrix n U_inv) w) a
  unfold ch14ext_gjeResidualS2
  change matMulVec n (absMatrix n L)
      (matMulVec n (absMatrix n X) w) i <= _
  rw [hXabs]
  rw [hlinear] at houter
  rw [hBaction, hCaction] at houter
  rw [ch14ext_cor146PrintedResidualObject_action]
  unfold ch14ext_cor146ResidualBridgeCorrection
  simpa [w] using houter

/-! ## Exact Corollary 14.6 residual closure -/

/-- The complete explicit remainder after replacing the concrete Theorem 14.5
envelope by Higham's printed Corollary 14.6 object. -/
noncomputable def ch14ext_cor146ResidualClosureRemainder
    (n : Nat) (fp : FPModel)
    (L X U U_inv : Fin n -> Fin n -> Real)
    (y x_hat : Fin n -> Real) (i : Fin n) : Real :=
  ch14ext_gjeResidualHigherOrder n fp L X U y x_hat i +
    16 * (n : Real) * fp.u * gje_c₃ fp n *
      ch14ext_cor146ResidualBridgeCorrection n L X U U_inv x_hat i

theorem ch14ext_cor146ResidualBridgeCorrection_nonneg
    (n : Nat) (L X U U_inv : Fin n -> Fin n -> Real)
    (x_hat : Fin n -> Real)
    (hX : forall i j : Fin n, 0 <= X i j) (i : Fin n) :
    0 <= ch14ext_cor146ResidualBridgeCorrection n L X U U_inv x_hat i := by
  unfold ch14ext_cor146ResidualBridgeCorrection
  apply ch14ext_absMatrix_action_nonneg
  intro a
  apply ch14ext_matMulVec_action_nonneg n X _ hX
  intro b
  apply ch14ext_absMatrix_action_nonneg
  intro c
  apply ch14ext_absMatrix_action_nonneg
  intro d
  apply ch14ext_absMatrix_action_nonneg
  intro e
  exact abs_nonneg (x_hat e)

theorem ch14ext_cor146ResidualClosureRemainder_nonneg
    (n : Nat) (fp : FPModel)
    (L X U U_inv : Fin n -> Fin n -> Real)
    (y x_hat : Fin n -> Real) (i : Fin n)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h3 : gammaValid fp 3)
    (hX : forall a j : Fin n, 0 <= X a j) :
    0 <= ch14ext_cor146ResidualClosureRemainder
      n fp L X U U_inv y x_hat i := by
  have hHigher := ch14ext_gjeResidualHigherOrder_nonneg
    n fp L X U y x_hat i hn hnpos h3
  have hc : 0 <= gje_c₃ fp n := gje_c3_nonneg fp n hnpos h3
  have hCorrection := ch14ext_cor146ResidualBridgeCorrection_nonneg
    n L X U U_inv x_hat hX i
  have hcoef : 0 <= 16 * (n : Real) * fp.u * gje_c₃ fp n :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg) hc
  unfold ch14ext_cor146ResidualClosureRemainder
  exact add_nonneg hHigher (mul_nonneg hcoef hCorrection)

/-- **Primary exact residual endpoint for Corollary 14.6.**

The concrete (14.31) theorem is used directly.  The printed leading object is
obtained from the constructed cumulative product and constructed inverse, and
all discarded terms are retained in an explicit nonnegative vector.  No
residual or forward-error endpoint is assumed. -/
theorem ch14ext_cor146_concrete_residual_printed_with_explicit_remainder
    (n : Nat) (fp : FPModel)
    (A L_hat U_inv : Fin n -> Fin n -> Real)
    (b x_hat : Fin n -> Real)
    (V : Nat -> Fin n -> Fin n -> Real)
    (xseq : Nat -> Fin n -> Real) (start : Nat)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hUinv : IsRightInverse n (V start) U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h3 : gammaValid fp 3)
    (hidx : forall t : Nat, t < n - 1 -> start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat i = xseq (start + (n - 1)) i)
    (hyStart : xseq start = fl_forwardSub fp n L_hat b)
    (hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t))
          ⟨start + t, hidx t ht⟩)
    (hxrec : forall t : Nat, (ht : t < n - 1) ->
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t))
          ⟨start + t, hidx t ht⟩ (xseq (start + t)))
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      Not (V (start + t) ⟨start + t, hidx t ht⟩
        ⟨start + t, hidx t ht⟩ = 0)) :
    forall i : Fin n,
      |b i - matMulVec n A x_hat i| <=
        8 * (n : Real) * fp.u *
          ch14ext_cor146PrintedResidualObject
            n L_hat (V start) U_inv x_hat i +
        ch14ext_cor146ResidualClosureRemainder n fp L_hat
          (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
            (ch14ext_gjeConstructedQ n V start) start (n - 1))
          (V start) U_inv (xseq start) x_hat i := by
  intro i
  let X := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeConstructedQ n V start) start (n - 1)
  have hX : forall a j : Fin n, 0 <= X a j := by
    intro a j
    exact ch14ext_gjeXabs_nonneg n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1) a j
  have hEnvelope :=
    ch14ext_cor146_concrete_envelope_le_printed_add_correction
      n fp V start U_inv hLU.U_lower_zero hnpos h3 hidx hVfinal hVrec hpiv hUinv
  have hS2 := ch14ext_cor146_gjeResidualS2_le_printed_add_correction
    n L_hat X (V start) U_inv x_hat (gje_c₃ fp n) hX
      (by simpa [X] using hEnvelope) i
  have hBase := ch14ext_gjeConcrete_overall_residual_14_31
    n fp A L_hat b x_hat V xseq start hLU hn hnpos h3 hidx hVfinal
      hxfinal hyStart hVrec hxrec hpiv i
  have hlead : 0 <= 8 * (n : Real) * fp.u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  calc
    |b i - matMulVec n A x_hat i| <=
        8 * (n : Real) * fp.u *
            ch14ext_gjeResidualS2 n L_hat X (V start) x_hat i +
          ch14ext_gjeResidualHigherOrder n fp L_hat X
            (V start) (xseq start) x_hat i := by
      simpa [X] using hBase
    _ <= 8 * (n : Real) * fp.u *
          (ch14ext_cor146PrintedResidualObject
              n L_hat (V start) U_inv x_hat i +
            2 * gje_c₃ fp n *
              ch14ext_cor146ResidualBridgeCorrection
                n L_hat X (V start) U_inv x_hat i) +
          ch14ext_gjeResidualHigherOrder n fp L_hat X
            (V start) (xseq start) x_hat i := by
      exact add_le_add (mul_le_mul_of_nonneg_left hS2 hlead) (le_refl _)
    _ = 8 * (n : Real) * fp.u *
          ch14ext_cor146PrintedResidualObject
            n L_hat (V start) U_inv x_hat i +
        ch14ext_cor146ResidualClosureRemainder n fp L_hat X
          (V start) U_inv (xseq start) x_hat i := by
      unfold ch14ext_cor146ResidualClosureRemainder
      ring
    _ = _ := by rfl

/-- **Normwise source-facing Corollary 14.6 with an exact remainder.**

Positive pivots and the symmetric factor relation supply the exact Gram
condition factor.  The LU absolute-product budget is derived by
`ch14ext_cor146_absLU_budget`.  Only inverse certificates, gamma validity, and
the algorithm/model certificates are assumptions; the residual conclusion is
not. -/
theorem ch14ext_cor146_concrete_residual_norm2_with_explicit_remainder
    (n : Nat) (fp : FPModel)
    (A L_hat U_inv R_inv : Fin n -> Fin n -> Real)
    (b x_hat : Fin n -> Real)
    (V : Nat -> Fin n -> Fin n -> Real)
    (xseq : Nat -> Fin n -> Real) (start : Nat)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hpivPos : forall i : Fin n, 0 < V start i i)
    (hsym : forall i j : Fin n,
      V start i j = V start i i * L_hat j i)
    (hUInv : IsInverse n (V start) U_inv)
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n (V start)) R_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h3 : gammaValid fp 3)
    (hsmall : (n : Real) * gamma fp n < 1)
    (hidx : forall t : Nat, t < n - 1 -> start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat i = xseq (start + (n - 1)) i)
    (hyStart : xseq start = fl_forwardSub fp n L_hat b)
    (hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t))
          ⟨start + t, hidx t ht⟩)
    (hxrec : forall t : Nat, (ht : t < n - 1) ->
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t))
          ⟨start + t, hidx t ht⟩ (xseq (start + t)))
    (hpivLoop : forall t : Nat, (ht : t < n - 1) ->
      Not (V (start + t) ⟨start + t, hidx t ht⟩
        ⟨start + t, hidx t ht⟩ = 0)) :
    vecNorm2 (fun i : Fin n => b i - matMulVec n A x_hat i) <=
      8 * (n : Real) ^ 3 * fp.u *
          (1 - (n : Real) * gamma fp n)⁻¹ *
          Real.sqrt
            (kappa2
              (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta
                  n A L_hat (V start) i j)
              (nonsingInv n (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta
                  n A L_hat (V start) i j))) *
          opNorm2 A * vecNorm2 x_hat +
        vecNorm2 (fun i =>
          ch14ext_cor146ResidualClosureRemainder n fp L_hat
            (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1))
            (V start) U_inv (xseq start) x_hat i) := by
  let X := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeConstructedQ n V start) start (n - 1)
  let factor := (1 - (n : Real) * gamma fp n)⁻¹
  let lead : Fin n -> Real := fun i =>
    8 * (n : Real) * fp.u *
      ch14ext_cor146PrintedResidualObject n L_hat (V start) U_inv x_hat i
  let rho : Fin n -> Real := fun i =>
    ch14ext_cor146ResidualClosureRemainder
      n fp L_hat X (V start) U_inv (xseq start) x_hat i
  have hden : 0 < 1 - (n : Real) * gamma fp n := by linarith
  have hfactor : 0 <= factor := le_of_lt (inv_pos.mpr hden)
  have hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n (V start)))
      ((n : Real) * factor * opNorm2 A) := by
    simpa [factor] using ch14ext_cor146_absLU_budget
      n fp A L_hat (V start) hLU hpivPos hsym hn hsmall
  have hlead : forall i : Fin n, 0 <= lead i := by
    intro i
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg)
      (ch14ext_cor146PrintedResidualObject_nonneg
        n L_hat (V start) U_inv x_hat i)
  let bLead : Fin n -> Real := fun i => matMulVec n A x_hat i + lead i
  have hLeadResidual : forall i : Fin n,
      |bLead i - matMulVec n A x_hat i| <=
        8 * (n : Real) * fp.u *
          ch14ext_cor146PrintedResidualObject
            n L_hat (V start) U_inv x_hat i := by
    intro i
    change |matMulVec n A x_hat i + lead i - matMulVec n A x_hat i| <= _
    rw [show matMulVec n A x_hat i + lead i - matMulVec n A x_hat i =
      lead i by ring, abs_of_nonneg (hlead i)]
  have hLeadNormRaw :=
    ch14ext_cor146_residual_positivePivot_exactGram_of_theorem14_5
      n fp A L_hat (V start) U_inv R_inv bLead x_hat factor
      hSPD hLU hpivPos hsym hUInv hRInv hfactor hAbsLU hLeadResidual
  have hLeadVector :
      (fun i : Fin n => bLead i - ∑ j : Fin n, A i j * x_hat j) = lead := by
    funext i
    change matMulVec n A x_hat i + lead i - matMulVec n A x_hat i = lead i
    ring
  have hLeadNorm : vecNorm2 lead <=
      8 * (n : Real) ^ 3 * fp.u * factor *
          Real.sqrt
            (kappa2
              (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta
                  n A L_hat (V start) i j)
              (nonsingInv n (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta
                  n A L_hat (V start) i j))) *
          opNorm2 A * vecNorm2 x_hat := by
    rw [hLeadVector] at hLeadNormRaw
    exact hLeadNormRaw
  have hEntry : forall i : Fin n,
      |b i - matMulVec n A x_hat i| <= lead i + rho i := by
    intro i
    simpa [lead, rho, X] using
      ch14ext_cor146_concrete_residual_printed_with_explicit_remainder
        n fp A L_hat U_inv b x_hat V xseq start hLU hUInv.2 hn hnpos h3
          hidx hVfinal hxfinal hyStart hVrec hxrec hpivLoop i
  have hNorm := vecNorm2_le_of_abs_le
    (fun i : Fin n => b i - matMulVec n A x_hat i)
    (fun i => lead i + rho i) hEntry
  calc
    vecNorm2 (fun i : Fin n => b i - matMulVec n A x_hat i) <=
        vecNorm2 (fun i => lead i + rho i) := hNorm
    _ <= vecNorm2 lead + vecNorm2 rho := vecNorm2_add_le lead rho
    _ <= (8 * (n : Real) ^ 3 * fp.u * factor *
          Real.sqrt
            (kappa2
              (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta
                  n A L_hat (V start) i j)
              (nonsingInv n (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta
                  n A L_hat (V start) i j))) *
          opNorm2 A * vecNorm2 x_hat) + vecNorm2 rho :=
      add_le_add hLeadNorm (le_refl _)
    _ = _ := by rfl

/-! ## Genuine vanishing-roundoff coefficient families -/

/-- Coefficient left after factoring one power of `u` from `gamma_k`. -/
noncomputable def ch14ext_cor146ClosureGammaUnitCoefficient
    (k : Nat) (u : Real) : Real :=
  (k : Real) / (1 - (k : Real) * u)

/-- Coefficient left after factoring `u^2` from the gamma remainder. -/
noncomputable def ch14ext_cor146ClosureGammaQuadraticCoefficient
    (k : Nat) (u : Real) : Real :=
  (k : Real) ^ 2 / (1 - (k : Real) * u)

theorem ch14ext_cor146Closure_gamma_factor
    (fp : FPModel) (k : Nat) :
    gamma fp k = fp.u * ch14ext_cor146ClosureGammaUnitCoefficient k fp.u := by
  unfold gamma ch14ext_cor146ClosureGammaUnitCoefficient
  ring

theorem ch14ext_cor146Closure_gammaRem_factor
    (fp : FPModel) (k : Nat) :
    ch14ext_gammaRem fp k =
      fp.u ^ 2 * ch14ext_cor146ClosureGammaQuadraticCoefficient k fp.u := by
  unfold ch14ext_gammaRem ch14ext_cor146ClosureGammaQuadraticCoefficient
  ring

theorem ch14ext_cor146ClosureGammaUnitCoefficient_continuousAt_zero
    (k : Nat) :
    ContinuousAt (ch14ext_cor146ClosureGammaUnitCoefficient k) 0 := by
  unfold ch14ext_cor146ClosureGammaUnitCoefficient
  exact continuousAt_const.div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (by norm_num)

theorem ch14ext_cor146ClosureGammaQuadraticCoefficient_continuousAt_zero
    (k : Nat) :
    ContinuousAt (ch14ext_cor146ClosureGammaQuadraticCoefficient k) 0 := by
  unfold ch14ext_cor146ClosureGammaQuadraticCoefficient
  exact continuousAt_const.div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (by norm_num)

theorem ch14ext_cor146Closure_gamma_family_isBigO_u
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (k : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => gamma (fp t) k) =O[l] (fun t => (fp t).u) := by
  have huO := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hCoeff :
      (fun t => ch14ext_cor146ClosureGammaUnitCoefficient k (fp t).u)
        =O[l] (fun _ : ι => (1 : Real)) := by
    simpa only [Function.comp_apply] using
      ((ch14ext_cor146ClosureGammaUnitCoefficient_continuousAt_zero k).tendsto.isBigO_one
        Real).comp_tendsto hu
  have hProduct := huO.mul hCoeff
  simpa only [ch14ext_cor146Closure_gamma_factor, mul_one] using hProduct

theorem ch14ext_cor146Closure_gammaRem_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (k : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => ch14ext_gammaRem (fp t) k)
      =O[l] (fun t => (fp t).u ^ 2) := by
  have huSq : (fun t => (fp t).u ^ 2)
      =O[l] (fun t => (fp t).u ^ 2) :=
    Asymptotics.isBigO_refl _ l
  have hCoeff :
      (fun t => ch14ext_cor146ClosureGammaQuadraticCoefficient k (fp t).u)
        =O[l] (fun _ : ι => (1 : Real)) := by
    simpa only [Function.comp_apply] using
      ((ch14ext_cor146ClosureGammaQuadraticCoefficient_continuousAt_zero k).tendsto.isBigO_one
        Real).comp_tendsto hu
  have hProduct := huSq.mul hCoeff
  simpa only [ch14ext_cor146Closure_gammaRem_factor, mul_one] using hProduct

/-- The bounded power multiplying `gamma_3` in the GJE accumulation constant. -/
noncomputable def ch14ext_cor146ClosureC3PowerCoefficient
    (n : Nat) (u : Real) : Real :=
  (1 + u * ch14ext_cor146ClosureGammaUnitCoefficient 3 u) ^ (n - 2)

/-- The finite geometric coefficient used to factor a second power of `u`
from the explicit `c3` remainder. -/
noncomputable def ch14ext_cor146ClosureC3GeomCoefficient
    (n : Nat) (u : Real) : Real :=
  Finset.sum (Finset.range (n - 2))
    (fun k =>
      (1 + u * ch14ext_cor146ClosureGammaUnitCoefficient 3 u) ^ k)

theorem ch14ext_cor146ClosureC3PowerCoefficient_continuousAt_zero
    (n : Nat) :
    ContinuousAt (ch14ext_cor146ClosureC3PowerCoefficient n) 0 := by
  unfold ch14ext_cor146ClosureC3PowerCoefficient
  exact (continuousAt_const.add
    (continuousAt_id.mul
      (ch14ext_cor146ClosureGammaUnitCoefficient_continuousAt_zero 3))).pow _

theorem ch14ext_cor146ClosureC3GeomCoefficient_continuousAt_zero
    (n : Nat) :
    ContinuousAt (ch14ext_cor146ClosureC3GeomCoefficient n) 0 := by
  unfold ch14ext_cor146ClosureC3GeomCoefficient
  let base : Real -> Real := fun u =>
    1 + u * ch14ext_cor146ClosureGammaUnitCoefficient 3 u
  have hbase : ContinuousAt base 0 := by
    dsimp [base]
    exact continuousAt_const.add
      (continuousAt_id.mul
        (ch14ext_cor146ClosureGammaUnitCoefficient_continuousAt_zero 3))
  change ContinuousAt
    (fun u => Finset.sum (Finset.range (n - 2)) (fun k => base u ^ k)) 0
  generalize n - 2 = p
  induction p with
  | zero => simpa using (continuousAt_const : ContinuousAt (fun _ : Real => (0 : Real)) 0)
  | succ p ih =>
      simpa [Finset.sum_range_succ] using ih.add (hbase.pow p)

theorem ch14ext_cor146Closure_c3Power_family_isBigO_one
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (n : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => (1 + gamma (fp t) 3) ^ (n - 2))
      =O[l] (fun _ : ι => (1 : Real)) := by
  have hCoeff :
      (fun t => ch14ext_cor146ClosureC3PowerCoefficient n (fp t).u)
        =O[l] (fun _ : ι => (1 : Real)) := by
    simpa only [Function.comp_apply] using
      ((ch14ext_cor146ClosureC3PowerCoefficient_continuousAt_zero n).tendsto.isBigO_one
        Real).comp_tendsto hu
  simpa only [ch14ext_cor146ClosureC3PowerCoefficient,
    ch14ext_cor146Closure_gamma_factor] using hCoeff

theorem ch14ext_cor146Closure_c3Geom_family_isBigO_one
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (n : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => Finset.sum (Finset.range (n - 2))
      (fun k => (1 + gamma (fp t) 3) ^ k))
      =O[l] (fun _ : ι => (1 : Real)) := by
  have hCoeff :
      (fun t => ch14ext_cor146ClosureC3GeomCoefficient n (fp t).u)
        =O[l] (fun _ : ι => (1 : Real)) := by
    simpa only [Function.comp_apply] using
      ((ch14ext_cor146ClosureC3GeomCoefficient_continuousAt_zero n).tendsto.isBigO_one
        Real).comp_tendsto hu
  simpa only [ch14ext_cor146ClosureC3GeomCoefficient,
    ch14ext_cor146Closure_gamma_factor] using hCoeff

theorem ch14ext_cor146Closure_c3_family_isBigO_u
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (n : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => gje_c₃ (fp t) n) =O[l] (fun t => (fp t).u) := by
  have hGamma := ch14ext_cor146Closure_gamma_family_isBigO_u fp 3 hu
  have hPower := ch14ext_cor146Closure_c3Power_family_isBigO_one fp n hu
  have hProduct := (hGamma.mul hPower).const_mul_left ((n : Real) - 1)
  simpa only [gje_c₃, mul_one, mul_assoc] using hProduct

theorem ch14ext_cor146Closure_c3_quadratic_remainder_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (n : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => gje_c3_quadratic_remainder (fp t) n)
      =O[l] (fun t => (fp t).u ^ 2) := by
  let p := n - 2
  let power : ι -> Real := fun t => (1 + gamma (fp t) 3) ^ p
  let geom : ι -> Real := fun t =>
    Finset.sum (Finset.range p) (fun k => (1 + gamma (fp t) 3) ^ k)
  have hRem3 := ch14ext_cor146Closure_gammaRem_family_isBigO_u_sq fp 3 hu
  have hPower : power =O[l] (fun _ : ι => (1 : Real)) := by
    simpa [power, p] using
      ch14ext_cor146Closure_c3Power_family_isBigO_one fp n hu
  have hGeom : geom =O[l] (fun _ : ι => (1 : Real)) := by
    simpa [geom, p] using
      ch14ext_cor146Closure_c3Geom_family_isBigO_one fp n hu
  have hTerm1 :
      (fun t => ch14ext_gammaRem (fp t) 3 * power t)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hRem3.mul hPower
  have hPowerSubEq :
      (fun t => power t - 1) =
        (fun t => gamma (fp t) 3 * geom t) := by
    funext t
    have hgeo := mul_geom_sum (1 + gamma (fp t) 3) p
    dsimp [power, geom]
    calc
      (1 + gamma (fp t) 3) ^ p - 1 =
          ((1 + gamma (fp t) 3) - 1) *
            Finset.sum (Finset.range p)
              (fun k => (1 + gamma (fp t) 3) ^ k) := hgeo.symm
      _ = gamma (fp t) 3 *
            Finset.sum (Finset.range p)
              (fun k => (1 + gamma (fp t) 3) ^ k) := by ring
  have hPowerSub : (fun t => power t - 1)
      =O[l] (fun t => (fp t).u) := by
    rw [hPowerSubEq]
    simpa only [mul_one] using
      (ch14ext_cor146Closure_gamma_family_isBigO_u fp 3 hu).mul hGeom
  have huO := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hTerm2 : (fun t => 3 * (fp t).u * (power t - 1))
      =O[l] (fun t => (fp t).u ^ 2) := by
    have h := (huO.mul hPowerSub).const_mul_left (3 : Real)
    simpa only [pow_two, mul_assoc] using h
  have hInside :
      (fun t => ch14ext_gammaRem (fp t) 3 * power t +
        3 * (fp t).u * (power t - 1))
        =O[l] (fun t => (fp t).u ^ 2) := hTerm1.add hTerm2
  have hAll := hInside.const_mul_left ((n : Real) - 1)
  simpa [gje_c3_quadratic_remainder, ch14ext_gammaRem, power, p] using hAll

/-- Coefficient of `S2` in the exact Theorem 14.5 residual remainder. -/
noncomputable def ch14ext_cor146ResidualLinearRemainderCoefficient
    (n : Nat) (fp : FPModel) : Real :=
  2 * ch14ext_gammaRem fp n +
    2 * gje_c3_quadratic_remainder fp n +
    2 * gamma fp n * gje_c₃ fp n

/-- Coefficient of `S22 + S23` in the exact Theorem 14.5 remainder. -/
noncomputable def ch14ext_cor146ResidualSquaredC3Coefficient
    (n : Nat) (fp : FPModel) : Real :=
  gje_c₃ fp n * gje_c₃ fp n * (1 + gamma fp n)

/-- Coefficient of the newly derived fixed-model envelope correction. -/
noncomputable def ch14ext_cor146ResidualBridgeCoefficient
    (n : Nat) (fp : FPModel) : Real :=
  16 * (n : Real) * fp.u * gje_c₃ fp n

theorem ch14ext_cor146ResidualLinearRemainderCoefficient_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (n : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => ch14ext_cor146ResidualLinearRemainderCoefficient n (fp t))
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hGammaRem :=
    (ch14ext_cor146Closure_gammaRem_family_isBigO_u_sq fp n hu).const_mul_left
      (2 : Real)
  have hC3Rem :=
    (ch14ext_cor146Closure_c3_quadratic_remainder_family_isBigO_u_sq
      fp n hu).const_mul_left (2 : Real)
  have hProductRaw :=
    (ch14ext_cor146Closure_gamma_family_isBigO_u fp n hu).mul
      (ch14ext_cor146Closure_c3_family_isBigO_u fp n hu)
  have hProduct :
      (fun t => 2 * gamma (fp t) n * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    have h := hProductRaw.const_mul_left (2 : Real)
    simpa only [pow_two, mul_assoc] using h
  simpa only [ch14ext_cor146ResidualLinearRemainderCoefficient] using
    (hGammaRem.add hC3Rem).add hProduct

theorem ch14ext_cor146ResidualSquaredC3Coefficient_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (n : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => ch14ext_cor146ResidualSquaredC3Coefficient n (fp t))
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hC3 := ch14ext_cor146Closure_c3_family_isBigO_u fp n hu
  have hC3sq : (fun t => gje_c₃ (fp t) n * gje_c₃ (fp t) n)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hC3.mul hC3
  have huOne : (fun t => (fp t).u)
      =O[l] (fun _ : ι => (1 : Real)) := hu.isBigO_one Real
  have hGammaOne :=
    (ch14ext_cor146Closure_gamma_family_isBigO_u fp n hu).trans huOne
  have hOne := Asymptotics.isBigO_refl (fun _ : ι => (1 : Real)) l
  have hOneGamma : (fun t => 1 + gamma (fp t) n)
      =O[l] (fun _ : ι => (1 : Real)) := hOne.add hGammaOne
  have h := hC3sq.mul hOneGamma
  simpa only [ch14ext_cor146ResidualSquaredC3Coefficient, mul_one] using h

theorem ch14ext_cor146ResidualBridgeCoefficient_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (n : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => ch14ext_cor146ResidualBridgeCoefficient n (fp t))
      =O[l] (fun t => (fp t).u ^ 2) := by
  have huO := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hProduct := huO.mul (ch14ext_cor146Closure_c3_family_isBigO_u fp n hu)
  have h := hProduct.const_mul_left (16 * (n : Real))
  simpa only [ch14ext_cor146ResidualBridgeCoefficient, pow_two, mul_assoc] using h

/-- Coefficient of the quadratic correction generated by the exact LU budget
factor `(1 - n*gamma_n)⁻¹`. -/
noncomputable def ch14ext_cor146LUFactorQuadraticCoefficient
    (n : Nat) (u : Real) : Real :=
  (n : Real) ^ 2 /
    (1 - ((n : Real) + (n : Real) ^ 2) * u)

theorem ch14ext_cor146LUFactorQuadraticCoefficient_continuousAt_zero
    (n : Nat) :
    ContinuousAt (ch14ext_cor146LUFactorQuadraticCoefficient n) 0 := by
  unfold ch14ext_cor146LUFactorQuadraticCoefficient
  exact continuousAt_const.div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (by norm_num)

theorem ch14ext_cor146_luFactor_correction_factor
    (n : Nat) (fp : FPModel)
    (hn : gammaValid fp n)
    (hsmall : (n : Real) * gamma fp n < 1) :
    fp.u * (1 - (n : Real) * gamma fp n)⁻¹ - fp.u =
      fp.u ^ 2 * ch14ext_cor146LUFactorQuadraticCoefficient n fp.u := by
  have hden1 : 0 < 1 - (n : Real) * fp.u := by
    unfold gammaValid at hn
    linarith
  have hdenMain : 0 < 1 - (n : Real) * gamma fp n := by linarith
  have hrel :
      (1 - (n : Real) * fp.u) *
          (1 - (n : Real) * gamma fp n) =
        1 - ((n : Real) + (n : Real) ^ 2) * fp.u := by
    unfold gamma
    field_simp [ne_of_gt hden1]
    ring
  have hden2 :
      0 < 1 - ((n : Real) + (n : Real) ^ 2) * fp.u := by
    rw [← hrel]
    exact mul_pos hden1 hdenMain
  have hfactor :
      (1 - (n : Real) * gamma fp n)⁻¹ =
        (1 - (n : Real) * fp.u) *
          (1 - ((n : Real) + (n : Real) ^ 2) * fp.u)⁻¹ := by
    rw [← hrel]
    field_simp [ne_of_gt hden1, ne_of_gt hdenMain]
  rw [hfactor]
  unfold ch14ext_cor146LUFactorQuadraticCoefficient
  rw [div_eq_mul_inv]
  let E := 1 - ((n : Real) + (n : Real) ^ 2) * fp.u
  have hE : Not (E = 0) := by
    exact ne_of_gt (by simpa [E] using hden2)
  change fp.u * ((1 - (n : Real) * fp.u) * E⁻¹) - fp.u =
    fp.u ^ 2 * ((n : Real) ^ 2 * E⁻¹)
  calc
    fp.u * ((1 - (n : Real) * fp.u) * E⁻¹) - fp.u =
        fp.u * ((1 - (n : Real) * fp.u) * E⁻¹) -
          fp.u * (E * E⁻¹) := by rw [mul_inv_cancel₀ hE, mul_one]
    _ = fp.u ^ 2 * ((n : Real) ^ 2 * E⁻¹) := by
      dsimp [E]
      ring

theorem ch14ext_cor146_luFactor_sub_one_factor
    (n : Nat) (fp : FPModel)
    (hn : gammaValid fp n)
    (hsmall : (n : Real) * gamma fp n < 1) :
    (1 - (n : Real) * gamma fp n)⁻¹ - 1 =
      fp.u * ch14ext_cor146LUFactorQuadraticCoefficient n fp.u := by
  by_cases hu0 : fp.u = 0
  · simp [hu0, gamma]
  · apply mul_left_cancel₀ hu0
    calc
      fp.u * ((1 - (n : Real) * gamma fp n)⁻¹ - 1) =
          fp.u * (1 - (n : Real) * gamma fp n)⁻¹ - fp.u := by ring
      _ = fp.u ^ 2 * ch14ext_cor146LUFactorQuadraticCoefficient n fp.u :=
        ch14ext_cor146_luFactor_correction_factor n fp hn hsmall
      _ = fp.u *
          (fp.u * ch14ext_cor146LUFactorQuadraticCoefficient n fp.u) := by ring

theorem ch14ext_cor146_luFactor_sub_one_family_isBigO_u
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (n : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hn : Filter.Eventually (fun t => gammaValid (fp t) n) l)
    (hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (fp t) n < 1) l) :
    (fun t => (1 - (n : Real) * gamma (fp t) n)⁻¹ - 1)
      =O[l] (fun t => (fp t).u) := by
  have hCoeff :
      (fun t => ch14ext_cor146LUFactorQuadraticCoefficient n (fp t).u)
        =O[l] (fun _ : ι => (1 : Real)) := by
    simpa only [Function.comp_apply] using
      ((ch14ext_cor146LUFactorQuadraticCoefficient_continuousAt_zero n).tendsto.isBigO_one
        Real).comp_tendsto hu
  have huO := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hProduct :
      (fun t => (fp t).u *
        ch14ext_cor146LUFactorQuadraticCoefficient n (fp t).u)
        =O[l] (fun t => (fp t).u) := by
    simpa only [mul_one] using huO.mul hCoeff
  apply hProduct.congr'
  · filter_upwards [hn, hsmall] with t hnt hst
    exact (ch14ext_cor146_luFactor_sub_one_factor n (fp t) hnt hst).symm
  · exact Filter.EventuallyEq.rfl

/-- The LU-budget prefactor changes the leading `u` term only by `O(u^2)`
along a genuine model family satisfying the standard guards eventually. -/
theorem ch14ext_cor146_luFactor_leading_correction_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (fp : ι -> FPModel) (n : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hn : Filter.Eventually (fun t => gammaValid (fp t) n) l)
    (hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (fp t) n < 1) l) :
    (fun t => (fp t).u *
        (1 - (n : Real) * gamma (fp t) n)⁻¹ - (fp t).u)
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hCoeff :
      (fun t => ch14ext_cor146LUFactorQuadraticCoefficient n (fp t).u)
        =O[l] (fun _ : ι => (1 : Real)) := by
    simpa only [Function.comp_apply] using
      ((ch14ext_cor146LUFactorQuadraticCoefficient_continuousAt_zero n).tendsto.isBigO_one
        Real).comp_tendsto hu
  have huSq := Asymptotics.isBigO_refl (fun t => (fp t).u ^ 2) l
  have hProduct :
      (fun t => (fp t).u ^ 2 *
        ch14ext_cor146LUFactorQuadraticCoefficient n (fp t).u)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using huSq.mul hCoeff
  apply hProduct.congr'
  · filter_upwards [hn, hsmall] with t hnt hst
    exact (ch14ext_cor146_luFactor_correction_factor n (fp t) hnt hst).symm
  · exact Filter.EventuallyEq.rfl

/-! ## Uniformly bounded algorithm-data families -/

/-- Entrywise local boundedness for the varying matrices in this closure. -/
def Ch14Cor146ClosureMatrixFamilyIsBigOOne
    {ι : Type*} (l : Filter ι) {n : Nat}
    (M : ι -> Fin n -> Fin n -> Real) : Prop :=
  forall i j, (fun t => M t i j) =O[l] (fun _ : ι => (1 : Real))

/-- Componentwise local boundedness for varying vectors. -/
def Ch14Cor146ClosureVectorFamilyIsBigOOne
    {ι : Type*} (l : Filter ι) {n : Nat}
    (v : ι -> Fin n -> Real) : Prop :=
  forall i, (fun t => v t i) =O[l] (fun _ : ι => (1 : Real))

theorem ch14ext_cor146Closure_matrix_abs_family_isBigO_one
    {ι : Type*} {l : Filter ι} {n : Nat}
    {M : ι -> Fin n -> Fin n -> Real}
    (hM : Ch14Cor146ClosureMatrixFamilyIsBigOOne l M) :
    Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (fun t => absMatrix n (M t)) := by
  intro i j
  simpa only [absMatrix, Real.norm_eq_abs] using (hM i j).norm_left

theorem ch14ext_cor146Closure_vector_abs_family_isBigO_one
    {ι : Type*} {l : Filter ι} {n : Nat}
    {v : ι -> Fin n -> Real}
    (hv : Ch14Cor146ClosureVectorFamilyIsBigOOne l v) :
    Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t => absVec n (v t)) := by
  intro i
  simpa only [absVec, Real.norm_eq_abs] using (hv i).norm_left

theorem ch14ext_cor146Closure_matMulVec_family_isBigO_one
    {ι : Type*} {l : Filter ι} {n : Nat}
    {M : ι -> Fin n -> Fin n -> Real}
    {v : ι -> Fin n -> Real}
    (hM : Ch14Cor146ClosureMatrixFamilyIsBigOOne l M)
    (hv : Ch14Cor146ClosureVectorFamilyIsBigOOne l v) :
    Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t => matMulVec n (M t) (v t)) := by
  intro i
  simpa only [matMulVec, mul_one] using
    (Asymptotics.IsBigO.sum (s := Finset.univ) (fun j _ =>
      (hM i j).mul (hv j)))

theorem ch14ext_cor146Closure_residualS2_family_isBigO_one
    {ι : Type*} {l : Filter ι} (n : Nat)
    {L X U : ι -> Fin n -> Fin n -> Real}
    {x_hat : ι -> Fin n -> Real}
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hX : Ch14Cor146ClosureMatrixFamilyIsBigOOne l X)
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U)
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat) :
    Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeResidualS2 n (L t) (X t) (U t) (x_hat t) i) := by
  have hxabs := ch14ext_cor146Closure_vector_abs_family_isBigO_one hx
  have hUabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hU
  have hXabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hX
  have hLabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hL
  have hUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUabs hxabs
  have hXUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hXabs hUx
  have hLXUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hLabs hXUx
  simpa only [ch14ext_gjeResidualS2] using hLXUx

theorem ch14ext_cor146Closure_residualS22_family_isBigO_one
    {ι : Type*} {l : Filter ι} (n : Nat)
    {L X U : ι -> Fin n -> Fin n -> Real}
    {x_hat : ι -> Fin n -> Real}
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hX : Ch14Cor146ClosureMatrixFamilyIsBigOOne l X)
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U)
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat) :
    Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeResidualS22 n (L t) (X t) (U t) (x_hat t) i) := by
  have hxabs := ch14ext_cor146Closure_vector_abs_family_isBigO_one hx
  have hUabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hU
  have hXabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hX
  have hLabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hL
  have hUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUabs hxabs
  have hXUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hXabs hUx
  have hXXUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hXabs hXUx
  have hLXXUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hLabs hXXUx
  simpa only [ch14ext_gjeResidualS22] using hLXXUx

theorem ch14ext_cor146Closure_residualS23_family_isBigO_one
    {ι : Type*} {l : Filter ι} (n : Nat)
    {L X : ι -> Fin n -> Fin n -> Real}
    {y : ι -> Fin n -> Real}
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hX : Ch14Cor146ClosureMatrixFamilyIsBigOOne l X)
    (hy : Ch14Cor146ClosureVectorFamilyIsBigOOne l y) :
    Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeResidualS23 n (L t) (X t) (y t) i) := by
  have hyabs := ch14ext_cor146Closure_vector_abs_family_isBigO_one hy
  have hXabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hX
  have hLabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hL
  have hXy := ch14ext_cor146Closure_matMulVec_family_isBigO_one hXabs hyabs
  have hXXy := ch14ext_cor146Closure_matMulVec_family_isBigO_one hXabs hXy
  have hLXXy := ch14ext_cor146Closure_matMulVec_family_isBigO_one hLabs hXXy
  simpa only [ch14ext_gjeResidualS23] using hLXXy

theorem ch14ext_cor146Closure_bridgeCorrection_family_isBigO_one
    {ι : Type*} {l : Filter ι} (n : Nat)
    {L X U U_inv : ι -> Fin n -> Fin n -> Real}
    {x_hat : ι -> Fin n -> Real}
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hX : Ch14Cor146ClosureMatrixFamilyIsBigOOne l X)
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U)
    (hUinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U_inv)
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat) :
    Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t i => ch14ext_cor146ResidualBridgeCorrection
        n (L t) (X t) (U t) (U_inv t) (x_hat t) i) := by
  have hxabs := ch14ext_cor146Closure_vector_abs_family_isBigO_one hx
  have hUabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hU
  have hUiabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hUinv
  have hLabs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hL
  have hUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUabs hxabs
  have hUiUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUiabs hUx
  have hUUiUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUabs hUiUx
  have hXUUiUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hX hUUiUx
  have hLXUUiUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hLabs hXUUiUx
  simpa only [ch14ext_cor146ResidualBridgeCorrection] using hLXUUiUx

/-- **Family-level `O(u^2)` certificate for the full explicit remainder.**

All floating-point models and algorithm data may vary with the family index.
The hypotheses are only entrywise/componentwise `O(1)` bounds on the data and
`u(t) -> 0`; no fixed-`u` existential constant and no residual endpoint is
used. -/
theorem ch14ext_cor146ResidualClosureRemainder_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (n : Nat)
    (fp : ι -> FPModel)
    (L X U U_inv : ι -> Fin n -> Fin n -> Real)
    (y x_hat : ι -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hX : Ch14Cor146ClosureMatrixFamilyIsBigOOne l X)
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U)
    (hUinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U_inv)
    (hy : Ch14Cor146ClosureVectorFamilyIsBigOOne l y)
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat) :
    forall i : Fin n,
      (fun t => ch14ext_cor146ResidualClosureRemainder n (fp t)
        (L t) (X t) (U t) (U_inv t) (y t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
  have hS2 := ch14ext_cor146Closure_residualS2_family_isBigO_one
    n hL hX hU hx
  have hS22 := ch14ext_cor146Closure_residualS22_family_isBigO_one
    n hL hX hU hx
  have hS23 := ch14ext_cor146Closure_residualS23_family_isBigO_one
    n hL hX hy
  have hCorrection := ch14ext_cor146Closure_bridgeCorrection_family_isBigO_one
    n hL hX hU hUinv hx
  have hAlpha :=
    ch14ext_cor146ResidualLinearRemainderCoefficient_family_isBigO_u_sq
      fp n hu
  have hBeta :=
    ch14ext_cor146ResidualSquaredC3Coefficient_family_isBigO_u_sq
      fp n hu
  have hBridge :=
    ch14ext_cor146ResidualBridgeCoefficient_family_isBigO_u_sq fp n hu
  intro i
  have hTerm1 :
      (fun t => ch14ext_cor146ResidualLinearRemainderCoefficient n (fp t) *
        ch14ext_gjeResidualS2 n (L t) (X t) (U t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hAlpha.mul (hS2 i)
  have hS23sum :
      (fun t => ch14ext_gjeResidualS22 n (L t) (X t) (U t) (x_hat t) i +
        ch14ext_gjeResidualS23 n (L t) (X t) (y t) i)
        =O[l] (fun _ : ι => (1 : Real)) := (hS22 i).add (hS23 i)
  have hTerm2 :
      (fun t => ch14ext_cor146ResidualSquaredC3Coefficient n (fp t) *
        (ch14ext_gjeResidualS22 n (L t) (X t) (U t) (x_hat t) i +
          ch14ext_gjeResidualS23 n (L t) (X t) (y t) i))
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hBeta.mul hS23sum
  have hTerm3 :
      (fun t => ch14ext_cor146ResidualBridgeCoefficient n (fp t) *
        ch14ext_cor146ResidualBridgeCorrection
          n (L t) (X t) (U t) (U_inv t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hBridge.mul (hCorrection i)
  simpa only [ch14ext_cor146ResidualClosureRemainder,
    ch14ext_gjeResidualHigherOrder,
    ch14ext_cor146ResidualLinearRemainderCoefficient,
    ch14ext_cor146ResidualSquaredC3Coefficient,
    ch14ext_cor146ResidualBridgeCoefficient] using
      (hTerm1.add hTerm2).add hTerm3

/-- Finite-dimensional componentwise `O(g)` control implies the same Landau
bound for the Euclidean norm. -/
theorem ch14ext_cor146Closure_vecNorm2_family_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {v : ι -> Fin n -> Real} {g : ι -> Real}
    (hv : forall i : Fin n, (fun t => v t i) =O[l] g) :
    (fun t => vecNorm2 (v t)) =O[l] g := by
  let total : ι -> Real := fun t => ∑ i : Fin n, |v t i|
  have htotal : total =O[l] g := by
    dsimp [total]
    apply Asymptotics.IsBigO.sum
    intro i _
    simpa only [Real.norm_eq_abs] using (hv i).norm_left
  have hnormTotal : (fun t => vecNorm2 (v t)) =O[l] total := by
    apply Asymptotics.IsBigO.of_norm_le
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (vecNorm2_nonneg (v t))]
    have hsq := vecNorm2Sq_le_sum_abs_sq (v t)
    have hnormsq := vecNorm2_sq (v t)
    have hnormNonneg := vecNorm2_nonneg (v t)
    have htotalNonneg : 0 <= total t := by
      dsimp [total]
      exact Finset.sum_nonneg (fun i _ => abs_nonneg (v t i))
    dsimp [total]
    nlinarith
  exact hnormTotal.trans htotal

/-- Normwise family form of the explicit `O(u^2)` remainder certificate. -/
theorem ch14ext_cor146ResidualClosureRemainder_norm2_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (n : Nat)
    (fp : ι -> FPModel)
    (L X U U_inv : ι -> Fin n -> Fin n -> Real)
    (y x_hat : ι -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hX : Ch14Cor146ClosureMatrixFamilyIsBigOOne l X)
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U)
    (hUinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U_inv)
    (hy : Ch14Cor146ClosureVectorFamilyIsBigOOne l y)
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat) :
    (fun t => vecNorm2 (fun i =>
      ch14ext_cor146ResidualClosureRemainder n (fp t)
        (L t) (X t) (U t) (U_inv t) (y t) (x_hat t) i))
      =O[l] (fun t => (fp t).u ^ 2) := by
  apply ch14ext_cor146Closure_vecNorm2_family_isBigO
  exact ch14ext_cor146ResidualClosureRemainder_family_isBigO_u_sq
    n fp L X U U_inv y x_hat hu hL hX hU hUinv hy hx

/-! ## The concrete (14.32) remainder as a genuine family -/

theorem ch14ext_cor146Closure_constant_matrix_family_isBigO_one
    {ι : Type*} {l : Filter ι} {n : Nat}
    (A : Fin n -> Fin n -> Real) :
    Ch14Cor146ClosureMatrixFamilyIsBigOOne l (fun _ : ι => A) := by
  intro i j
  simpa using
    (Asymptotics.isBigO_refl (fun _ : ι => (1 : Real)) l).const_mul_left
      (A i j)

theorem ch14ext_cor146ForwardLiteralHigherOrder_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (n : Nat)
    (fp : ι -> FPModel) (A_inv : Fin n -> Fin n -> Real)
    (L U X U_inv : ι -> Fin n -> Fin n -> Real)
    (z y x_hat : ι -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U)
    (hX : Ch14Cor146ClosureMatrixFamilyIsBigOOne l X)
    (hUinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U_inv)
    (hz : Ch14Cor146ClosureVectorFamilyIsBigOOne l z)
    (hy : Ch14Cor146ClosureVectorFamilyIsBigOOne l y)
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat) :
    forall i : Fin n,
      (fun t => ch14ext_gjeForwardLiteralHigherOrder n (fp t) A_inv
        (L t) (U t) (X t) (U_inv t) (z t) (y t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
  have hAinv := ch14ext_cor146Closure_constant_matrix_family_isBigO_one
    (ι := ι) (l := l) A_inv
  have hAinvAbs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hAinv
  have hLAbs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hL
  have hUAbs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hU
  have hUinvAbs := ch14ext_cor146Closure_matrix_abs_family_isBigO_one hUinv
  have hzAbs := ch14ext_cor146Closure_vector_abs_family_isBigO_one hz
  have hyAbs := ch14ext_cor146Closure_vector_abs_family_isBigO_one hy
  have hxAbs := ch14ext_cor146Closure_vector_abs_family_isBigO_one hx
  have hUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUAbs hxAbs
  have hLUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hLAbs hUx
  have hT1 := ch14ext_cor146Closure_matMulVec_family_isBigO_one hAinvAbs hLUx
  have hT2 := ch14ext_cor146Closure_matMulVec_family_isBigO_one hX hUx
  have hUz := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUAbs hzAbs
  have hXUz := ch14ext_cor146Closure_matMulVec_family_isBigO_one hX hUz
  have hXy := ch14ext_cor146Closure_matMulVec_family_isBigO_one hX hyAbs
  have hRaw : Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeForwardRaw n (X t) (U t) (z t) (y t) i) := by
    intro i
    simpa only [ch14ext_gjeForwardRaw] using (hXUz i).add (hXy i)
  have hUraw := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUAbs hRaw
  have hLUraw := ch14ext_cor146Closure_matMulVec_family_isBigO_one hLAbs hUraw
  have hQ1 := ch14ext_cor146Closure_matMulVec_family_isBigO_one hAinvAbs hLUraw
  have hQ2 := ch14ext_cor146Closure_matMulVec_family_isBigO_one hX hUraw
  have hUinvUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUinvAbs hUx
  have hUUinvUx := ch14ext_cor146Closure_matMulVec_family_isBigO_one hUAbs hUinvUx
  have hCorrection :=
    ch14ext_cor146Closure_matMulVec_family_isBigO_one hX hUUinvUx
  have hGammaRem :=
    (ch14ext_cor146Closure_gammaRem_family_isBigO_u_sq fp n hu).const_mul_left
      (2 : Real)
  have hC3Rem :=
    (ch14ext_cor146Closure_c3_quadratic_remainder_family_isBigO_u_sq
      fp n hu).const_mul_left (2 : Real)
  have hGammaC3Raw :=
    (ch14ext_cor146Closure_gamma_family_isBigO_u fp n hu).mul
      (ch14ext_cor146Closure_c3_family_isBigO_u fp n hu)
  have hGammaC3 :
      (fun t => 2 * gamma (fp t) n * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      hGammaC3Raw.const_mul_left (2 : Real)
  have hC3 := ch14ext_cor146Closure_c3_family_isBigO_u fp n hu
  have hC3sq :
      (fun t => 2 * gje_c₃ (fp t) n * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    have h := (hC3.mul hC3).const_mul_left (2 : Real)
    simpa only [pow_two, mul_assoc] using h
  have huO := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hBridge :
      (fun t => 6 * (n : Real) * (fp t).u * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    have h := (huO.mul hC3).const_mul_left (6 * (n : Real))
    simpa only [pow_two, mul_assoc] using h
  intro i
  have h1 :
      (fun t => 2 * ch14ext_gammaRem (fp t) n *
        ch14ext_gjeForwardT1 n A_inv (L t) (U t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hGammaRem.mul (hT1 i)
  have h2 :
      (fun t => 2 * gje_c3_quadratic_remainder (fp t) n *
        ch14ext_gjeForwardT2 n (X t) (U t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hC3Rem.mul (hT2 i)
  have h3 :
      (fun t => 2 * gamma (fp t) n * gje_c₃ (fp t) n *
        ch14ext_gjeForwardQ1 n A_inv (L t) (U t) (X t)
          (z t) (y t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hGammaC3.mul (hQ1 i)
  have h4 :
      (fun t => 2 * gje_c₃ (fp t) n * gje_c₃ (fp t) n *
        ch14ext_gjeForwardQ2 n (X t) (U t) (z t) (y t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hC3sq.mul (hQ2 i)
  have h5 :
      (fun t => 6 * (n : Real) * (fp t).u * gje_c₃ (fp t) n *
        ch14ext_gjeForwardUinvCorrection n (X t) (U t) (U_inv t)
          (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hBridge.mul (hCorrection i)
  simpa only [ch14ext_gjeForwardLiteralHigherOrder,
    ch14ext_gjeForwardHigherOrder] using
      (((h1.add h2).add h3).add h4).add h5

theorem ch14ext_cor146ForwardLiteralHigherOrder_norm2_family_isBigO_u_sq
    {ι : Type*} {l : Filter ι} (n : Nat)
    (fp : ι -> FPModel) (A_inv : Fin n -> Fin n -> Real)
    (L U X U_inv : ι -> Fin n -> Fin n -> Real)
    (z y x_hat : ι -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U)
    (hX : Ch14Cor146ClosureMatrixFamilyIsBigOOne l X)
    (hUinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U_inv)
    (hz : Ch14Cor146ClosureVectorFamilyIsBigOOne l z)
    (hy : Ch14Cor146ClosureVectorFamilyIsBigOOne l y)
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat) :
    (fun t => vecNorm2 (fun i =>
      ch14ext_gjeForwardLiteralHigherOrder n (fp t) A_inv
        (L t) (U t) (X t) (U_inv t) (z t) (y t) (x_hat t) i))
      =O[l] (fun t => (fp t).u ^ 2) := by
  apply ch14ext_cor146Closure_vecNorm2_family_isBigO
  exact ch14ext_cor146ForwardLiteralHigherOrder_family_isBigO_u_sq
    n fp A_inv L U X U_inv z y x_hat hu hL hU hX hUinv hz hy hx

/-! ## Uniform spectral regularity and source constants -/

/-- The symmetric matrix whose condition number occurs in the exact
Corollary 14.6 estimates. -/
noncomputable def ch14ext_cor146ClosureAhat
    {I : Type*} (n : Nat) (A : Fin n -> Fin n -> Real)
    (L U : I -> Fin n -> Fin n -> Real) (t : I) :
    Fin n -> Fin n -> Real :=
  fun i j => A i j + ch14ext_cor146_symmetricGEDelta n A (L t) (U t) i j

/-- The constructed nonnegative stage envelope used by (14.31). -/
noncomputable def ch14ext_cor146ClosureX
    {I : Type*} (n : Nat)
    (V : I -> Nat -> Fin n -> Fin n -> Real) (start : Nat) (t : I) :
    Fin n -> Fin n -> Real :=
  ch14ext_gjeXabs n (ch14ext_gjeSeqStages n (V t))
    (ch14ext_gjeConstructedQ n (V t) start) start (n - 1)

/-- The absolute cumulative stage product used by the literal (14.32)
remainder. -/
noncomputable def ch14ext_cor146ClosureP
    {I : Type*} (n : Nat)
    (V : I -> Nat -> Fin n -> Fin n -> Real) (start : Nat) (t : I) :
    Fin n -> Fin n -> Real :=
  ch14ext_absCumProd n (ch14ext_gjeSeqStages n (V t)) start (n - 1)

/-- Transparent successful-run regularity contract for the sole spectral
replacement made below.

The exact inverse certificates, local inverse boundedness, and entrywise
`Ahat-A = O(u)` fields are precisely the uniform-invertibility data.  The
finite-dimensional consequence
`sqrt(kappa2 Ahat)-sqrt(kappa2 A) = O(u)` is proved below from these fields; it
is not part of the contract.  No residual or forward-error conclusion occurs
here. -/
structure Ch14Cor146UniformInverseRegularity
    {I : Type*} (l : Filter I) (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real) (fp : I -> FPModel)
    (L U : I -> Fin n -> Fin n -> Real) : Prop where
  source_inverse : IsInverse n A A_inv
  perturbed_inverse : forall t,
    IsInverse n (ch14ext_cor146ClosureAhat n A L U t)
      (nonsingInv n (ch14ext_cor146ClosureAhat n A L U t))
  perturbed_inverse_family_isBigO_one :
    Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (fun t => nonsingInv n (ch14ext_cor146ClosureAhat n A L U t))
  perturbation_family_isBigO_u : forall i j,
    (fun t => ch14ext_cor146ClosureAhat n A L U t i j - A i j)
      =O[l] (fun t => (fp t).u)

/-- An exact inverse on a nonempty finite dimension has condition number at
least one. -/
theorem ch14ext_cor146_one_le_kappa2_of_isInverse
    (n : Nat) (A A_inv : Fin n -> Fin n -> Real)
    (hn : 1 <= n) (hInv : IsInverse n A A_inv) :
    1 <= kappa2 A A_inv := by
  let e : Fin n -> Real := finiteBasisVec (show Fin n from
    ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)
  have he : vecNorm2 e = 1 := by
    simpa [e] using vecNorm2_finiteBasisVec
      (show Fin n from ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)
  have hAAinv : matMulVec n A (matMulVec n A_inv e) = e :=
    matMulVec_of_isRightInverse A A_inv hInv.2 e
  have hA := opNorm2Le_opNorm2 A (matMulVec n A_inv e)
  have hAinv := opNorm2Le_opNorm2 A_inv e
  have hA_nonneg := opNorm2_nonneg A
  calc
    1 = vecNorm2 e := he.symm
    _ = vecNorm2 (matMulVec n A (matMulVec n A_inv e)) := by rw [hAAinv]
    _ <= opNorm2 A * vecNorm2 (matMulVec n A_inv e) := hA
    _ <= opNorm2 A * (opNorm2 A_inv * vecNorm2 e) :=
      mul_le_mul_of_nonneg_left hAinv hA_nonneg
    _ = kappa2 A A_inv := by rw [he]; unfold kappa2; ring

/-- For an exact inverse, the square-root condition number is bounded by the
condition number itself. -/
theorem ch14ext_cor146_sqrt_kappa2_le_kappa2_of_isInverse
    (n : Nat) (A A_inv : Fin n -> Fin n -> Real)
    (hn : 1 <= n) (hInv : IsInverse n A A_inv) :
    Real.sqrt (kappa2 A A_inv) <= kappa2 A A_inv := by
  have hk1 := ch14ext_cor146_one_le_kappa2_of_isInverse n A A_inv hn hInv
  have hk0 : 0 <= kappa2 A A_inv := le_trans (by norm_num) hk1
  have hs0 := Real.sqrt_nonneg (kappa2 A A_inv)
  have hs2 := Real.sq_sqrt hk0
  nlinarith

/-- Exact inverse perturbation identity
`B_inv-A_inv = -B_inv*(B-A)*A_inv`. -/
theorem ch14ext_cor146_inverse_sub_identity
    (n : Nat) (A A_inv B B_inv : Fin n -> Fin n -> Real)
    (hA : IsInverse n A A_inv) (hB : IsInverse n B B_inv) :
    (fun i j => B_inv i j - A_inv i j) =
      fun i j => -matMul n
        (matMul n B_inv (fun a b => B a b - A a b)) A_inv i j := by
  let AM : Matrix (Fin n) (Fin n) Real := A
  let AIM : Matrix (Fin n) (Fin n) Real := A_inv
  let BM : Matrix (Fin n) (Fin n) Real := B
  let BIM : Matrix (Fin n) (Fin n) Real := B_inv
  have hAAI : AM * AIM = 1 := by
    ext i j
    simpa [AM, AIM, Matrix.mul_apply] using hA.2 i j
  have hBIB : BIM * BM = 1 := by
    ext i j
    simpa [BIM, BM, Matrix.mul_apply] using hB.1 i j
  have hmatrix : BIM - AIM = -(BIM * (BM - AM) * AIM) := by
    calc
      BIM - AIM = BIM * 1 - 1 * AIM := by simp
      _ = BIM * (AM * AIM) - (BIM * BM) * AIM := by rw [hAAI, hBIB]
      _ = -(BIM * (BM - AM) * AIM) := by noncomm_ring
  ext i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) Real => M i j) hmatrix
  simpa [AM, AIM, BM, BIM, matMul, Matrix.mul_apply] using hij

/-- The Frobenius norm is bounded by the sum of all entry magnitudes. -/
theorem ch14ext_cor146_frobNorm_le_sum_abs_entries
    {n : Nat} (M : Fin n -> Fin n -> Real) :
    frobNorm M <= ∑ i : Fin n, ∑ j : Fin n, |M i j| := by
  let r : Fin n -> Real := fun i => ∑ j : Fin n, |M i j|
  have hr0 : forall i, 0 <= r i := by
    intro i
    exact Finset.sum_nonneg (fun j _ => abs_nonneg (M i j))
  have htotal0 : 0 <= ∑ i : Fin n, r i :=
    Finset.sum_nonneg (fun i _ => hr0 i)
  apply frobNorm_le_of_frobNormSq_le_sq M htotal0
  calc
    frobNormSq M = ∑ i : Fin n, vecNorm2Sq (fun j => M i j) := by
      simp [frobNormSq, vecNorm2Sq]
    _ <= ∑ i : Fin n, r i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa [r] using vecNorm2Sq_le_sum_abs_sq (fun j => M i j)
    _ = vecNorm2Sq r := by rfl
    _ <= (∑ i : Fin n, |r i|) ^ 2 := vecNorm2Sq_le_sum_abs_sq r
    _ = (∑ i : Fin n, r i) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact abs_of_nonneg (hr0 i)

/-- Entrywise Landau control implies the same control for the exact matrix
operator 2-norm in finite dimension. -/
theorem ch14ext_cor146_opNorm2_family_isBigO_of_entrywise
    {I : Type*} {l : Filter I} {n : Nat}
    {M : I -> Fin n -> Fin n -> Real} {g : I -> Real}
    (hM : forall i j, (fun t => M t i j) =O[l] g) :
    (fun t => opNorm2 (M t)) =O[l] g := by
  let total : I -> Real := fun t => ∑ i : Fin n, ∑ j : Fin n, |M t i j|
  have htotal : total =O[l] g := by
    dsimp [total]
    apply Asymptotics.IsBigO.sum
    intro i _
    apply Asymptotics.IsBigO.sum
    intro j _
    simpa only [Real.norm_eq_abs] using (hM i j).norm_left
  have hop : (fun t => opNorm2 (M t)) =O[l] total := by
    apply Asymptotics.IsBigO.of_norm_le
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (opNorm2_nonneg (M t))]
    have hopenv : opNorm2 (M t) <= frobNorm (M t) :=
      opNorm2_le_of_opNorm2Le (M t) (frobNorm_nonneg (M t))
        (opNorm2Le_of_frobNorm_self (M t))
    have htotal0 : 0 <= total t := by
      dsimp [total]
      positivity
    exact le_trans hopenv (ch14ext_cor146_frobNorm_le_sum_abs_entries (M t))
  exact hop.trans htotal

/-- Reverse triangle inequality for the repository's exact operator 2-norm. -/
theorem ch14ext_cor146_abs_opNorm2_sub_opNorm2_le
    {n : Nat} (B A : Fin n -> Fin n -> Real) :
    |opNorm2 B - opNorm2 A| <=
      opNorm2 (fun i j => B i j - A i j) := by
  simpa [opNorm2, Pi.sub_apply] using
    (@abs_norm_sub_norm_le
      (Matrix (Fin n) (Fin n) Real)
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (Matrix (Fin n) (Fin n) Real)
        (Matrix.instL2OpNormedAddCommGroup
          (m := Fin n) (n := Fin n) (𝕜 := Real)))
      (B : Matrix (Fin n) (Fin n) Real)
      (A : Matrix (Fin n) (Fin n) Real))

/-- The exact inverse identity turns an `O(u)` matrix perturbation and a
locally bounded inverse family into an entrywise `O(u)` inverse perturbation. -/
theorem ch14ext_cor146_inverse_sub_family_isBigO_u
    {I : Type*} {l : Filter I} (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real)
    (B B_inv : I -> Fin n -> Fin n -> Real) (u : I -> Real)
    (hA : IsInverse n A A_inv)
    (hB : forall t, IsInverse n (B t) (B_inv t))
    (hBinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l B_inv)
    (hDelta : forall i j,
      (fun t => B t i j - A i j) =O[l] u) :
    forall i j, (fun t => B_inv t i j - A_inv i j) =O[l] u := by
  have hBD : forall i j,
      (fun t => matMul n (B_inv t)
        (fun a b => B t a b - A a b) i j) =O[l] u := by
    intro i j
    simpa only [matMul, one_mul] using
      (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
        (hBinv i k).mul (hDelta k j)))
  have hAconst : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (fun _ : I => A_inv) :=
    ch14ext_cor146Closure_constant_matrix_family_isBigO_one A_inv
  have htriple : forall i j,
      (fun t => matMul n
        (matMul n (B_inv t) (fun a b => B t a b - A a b)) A_inv i j)
        =O[l] u := by
    intro i j
    simpa only [matMul, mul_one] using
      (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
        (hBD i k).mul (hAconst k j)))
  intro i j
  have hneg := (htriple i j).const_mul_left (-1 : Real)
  apply hneg.congr'
  · filter_upwards with t
    have hid := ch14ext_cor146_inverse_sub_identity
      n A A_inv (B t) (B_inv t) hA (hB t)
    have hij := congrArg (fun M => M i j) hid
    simpa using hij.symm
  · exact Filter.EventuallyEq.rfl

/-- The exact operator norm is one-Lipschitz with respect to its matrix
argument, hence an entrywise finite-dimensional `O(g)` perturbation gives an
`O(g)` norm perturbation. -/
theorem ch14ext_cor146_opNorm2_sub_family_isBigO
    {I : Type*} {l : Filter I} {n : Nat}
    (B : I -> Fin n -> Fin n -> Real) (A : Fin n -> Fin n -> Real)
    {g : I -> Real}
    (hDelta : forall i j, (fun t => B t i j - A i j) =O[l] g) :
    (fun t => opNorm2 (B t) - opNorm2 A) =O[l] g := by
  have hmatrix := ch14ext_cor146_opNorm2_family_isBigO_of_entrywise hDelta
  have hlip :
      (fun t => opNorm2 (B t) - opNorm2 A) =O[l]
        (fun t => opNorm2 (fun i j => B t i j - A i j)) := by
    apply Asymptotics.IsBigO.of_norm_le
    intro t
    exact ch14ext_cor146_abs_opNorm2_sub_opNorm2_le (B t) A
  exact hlip.trans hmatrix

/-- Product continuity for `kappa2`, derived from the exact inverse identity
rather than postulated as a spectral assumption. -/
theorem ch14ext_cor146_kappa2_sub_family_isBigO_u
    {I : Type*} {l : Filter I} (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real)
    (B B_inv : I -> Fin n -> Fin n -> Real) (u : I -> Real)
    (hA : IsInverse n A A_inv)
    (hB : forall t, IsInverse n (B t) (B_inv t))
    (hBinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l B_inv)
    (hDelta : forall i j, (fun t => B t i j - A i j) =O[l] u) :
    (fun t => kappa2 (B t) (B_inv t) - kappa2 A A_inv) =O[l] u := by
  have hInvDelta := ch14ext_cor146_inverse_sub_family_isBigO_u
    n A A_inv B B_inv u hA hB hBinv hDelta
  have hBnormDelta := ch14ext_cor146_opNorm2_sub_family_isBigO B A hDelta
  have hInvNormDelta :=
    ch14ext_cor146_opNorm2_sub_family_isBigO B_inv A_inv hInvDelta
  have hBinvNorm : (fun t => opNorm2 (B_inv t))
      =O[l] (fun _ : I => (1 : Real)) :=
    ch14ext_cor146_opNorm2_family_isBigO_of_entrywise hBinv
  have hAnorm : (fun _ : I => opNorm2 A)
      =O[l] (fun _ : I => (1 : Real)) := by
    simpa using
      (Asymptotics.isBigO_refl (fun _ : I => (1 : Real)) l).const_mul_left
        (opNorm2 A)
  have h1 :
      (fun t => (opNorm2 (B t) - opNorm2 A) * opNorm2 (B_inv t))
        =O[l] u := by
    simpa only [mul_one] using hBnormDelta.mul hBinvNorm
  have h2 :
      (fun t => opNorm2 A * (opNorm2 (B_inv t) - opNorm2 A_inv))
        =O[l] u := by
    simpa only [one_mul] using hAnorm.mul hInvNormDelta
  have hsum := h1.add h2
  apply hsum.congr'
  · filter_upwards with t
    unfold kappa2
    ring
  · exact Filter.EventuallyEq.rfl

/-- The varying square-root condition number in the exact concrete endpoint. -/
noncomputable def ch14ext_cor146ClosureSqrtKappa
    {I : Type*} (n : Nat) (A : Fin n -> Fin n -> Real)
    (L U : I -> Fin n -> Fin n -> Real) (t : I) : Real :=
  Real.sqrt (kappa2 (ch14ext_cor146ClosureAhat n A L U t)
    (nonsingInv n (ch14ext_cor146ClosureAhat n A L U t)))

/-- Higham's printed forward coefficient `8*n^(5/2)*kappa2(A)`, with
`n^(5/2)` represented exactly as `n^2*sqrt n`. -/
noncomputable def ch14ext_cor146ForwardPrintedCoefficient
    (n : Nat) (A A_inv : Fin n -> Fin n -> Real) : Real :=
  8 * (n : Real) ^ 2 * Real.sqrt n * kappa2 A A_inv

/-- Absolute correction for replacing the perturbed square-root condition
number and LU prefactor in the residual leading term. -/
noncomputable def ch14ext_cor146ResidualSpectralCorrection
    {I : Type*} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U : I -> Fin n -> Fin n -> Real) (t : I) : Real :=
  |(1 - (n : Real) * gamma (fp t) n)⁻¹ *
      ch14ext_cor146ClosureSqrtKappa n A L U t -
    Real.sqrt (kappa2 A A_inv)|

/-- Coefficient correction between the concrete (14.32) norm bound and the
printed `8*n^(5/2)*kappa2(A)` coefficient. -/
noncomputable def ch14ext_cor146ForwardCoefficientCorrection
    {I : Type*} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U : I -> Fin n -> Fin n -> Real) (t : I) : Real :=
  2 * (n : Real) ^ 2 * Real.sqrt n * kappa2 A A_inv *
      |(1 - (n : Real) * gamma (fp t) n)⁻¹ - 1| +
    6 * (n : Real) ^ 2 *
      |ch14ext_cor146ClosureSqrtKappa n A L U t -
        Real.sqrt (kappa2 A A_inv)|

/-- Full explicit residual remainder after replacing the concrete spectral
factor by the source matrix condition number. -/
noncomputable def ch14ext_cor146ResidualSourceRemainder
    {I : Type*} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U_inv : I -> Fin n -> Fin n -> Real)
    (V : I -> Nat -> Fin n -> Fin n -> Real)
    (xseq : I -> Nat -> Fin n -> Real) (x_hat : I -> Fin n -> Real)
    (start : Nat) (t : I) : Real :=
  vecNorm2 (fun i =>
      ch14ext_cor146ResidualClosureRemainder n (fp t) (L t)
        (ch14ext_cor146ClosureX n V start t) (V t start) (U_inv t)
        (xseq t start) (x_hat t) i) +
    8 * (n : Real) ^ 3 * (fp t).u *
      ch14ext_cor146ResidualSpectralCorrection n fp A A_inv L
        (fun s => V s start) t *
      opNorm2 A * vecNorm2 (x_hat t)

/-- Full explicit absolute forward remainder after replacing both varying
leading coefficients by Higham's printed source coefficient. -/
noncomputable def ch14ext_cor146ForwardAbsoluteSourceRemainder
    {I : Type*} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U_inv : I -> Fin n -> Fin n -> Real)
    (V : I -> Nat -> Fin n -> Fin n -> Real)
    (xseq : I -> Nat -> Fin n -> Real)
    (z x_hat : I -> Fin n -> Real) (start : Nat) (t : I) : Real :=
  vecNorm2 (ch14ext_cor146ConcreteForwardRemainder n (fp t) A_inv
      (L t) (U_inv t) (V t) (xseq t) (z t) (x_hat t) start) +
    (fp t).u *
      ch14ext_cor146ForwardCoefficientCorrection n fp A A_inv L
        (fun s => V s start) t *
      vecNorm2 (x_hat t)

/-- Explicit relative-error remainder after eliminating
`||xhat||_2/||x||_2`.  Here `q` is the printed first-order coefficient times
`u`; the endpoint below assumes only the standard successful-run bootstrap
`q < 1`. -/
noncomputable def ch14ext_cor146ForwardRelativeSourceRemainder
    {I : Type*} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U_inv : I -> Fin n -> Fin n -> Real)
    (V : I -> Nat -> Fin n -> Fin n -> Real)
    (xseq : I -> Nat -> Fin n -> Real)
    (z x_hat : I -> Fin n -> Real) (x : Fin n -> Real)
    (start : Nat) (t : I) : Real :=
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  let q := c * (fp t).u
  q ^ 2 * (1 - q)⁻¹ +
    ch14ext_cor146ForwardAbsoluteSourceRemainder n fp A A_inv L U_inv
      V xseq z x_hat start t * (1 - q)⁻¹ * (vecNorm2 x)⁻¹

/-- **Derived square-root condition-number perturbation.**

This is the spectral bridge required by the source-literal Corollary 14.6
closure.  It follows from the exact inverse identity, finite-dimensional
operator-norm Lipschitz continuity, and `kappa2 >= 1` for both exact inverse
pairs.  In particular it is not a field of the uniform-inverse contract. -/
theorem ch14ext_cor146_sqrtKappa_proximity_family_isBigO_u
    {I : Type*} {l : Filter I} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U : I -> Fin n -> Fin n -> Real) (hnpos : 1 <= n)
    (hreg : Ch14Cor146UniformInverseRegularity l n A A_inv fp L U) :
    (fun t => ch14ext_cor146ClosureSqrtKappa n A L U t -
      Real.sqrt (kappa2 A A_inv)) =O[l] (fun t => (fp t).u) := by
  let B : I -> Fin n -> Fin n -> Real :=
    ch14ext_cor146ClosureAhat n A L U
  let B_inv : I -> Fin n -> Fin n -> Real := fun t =>
    nonsingInv n (B t)
  have hkappa :
      (fun t => kappa2 (B t) (B_inv t) - kappa2 A A_inv)
        =O[l] (fun t => (fp t).u) :=
    ch14ext_cor146_kappa2_sub_family_isBigO_u n A A_inv B B_inv
      (fun t => (fp t).u) hreg.source_inverse
      (by simpa [B, B_inv] using hreg.perturbed_inverse)
      (by simpa [B, B_inv] using hreg.perturbed_inverse_family_isBigO_one)
      (by simpa [B] using hreg.perturbation_family_isBigO_u)
  have hsourceKappa := ch14ext_cor146_one_le_kappa2_of_isInverse
    n A A_inv hnpos hreg.source_inverse
  have hsourceRoot : 1 <= Real.sqrt (kappa2 A A_inv) := by
    have h := Real.sqrt_le_sqrt hsourceKappa
    simpa using h
  have hdenInv :
      (fun t => (ch14ext_cor146ClosureSqrtKappa n A L U t +
        Real.sqrt (kappa2 A A_inv))⁻¹)
        =O[l] (fun _ : I => (1 : Real)) := by
    apply Asymptotics.IsBigO.of_norm_le
    intro t
    have hpertKappa := ch14ext_cor146_one_le_kappa2_of_isInverse
      n (B t) (B_inv t) hnpos (by
        simpa [B, B_inv] using hreg.perturbed_inverse t)
    have hpertRoot : 1 <= ch14ext_cor146ClosureSqrtKappa n A L U t := by
      have h := Real.sqrt_le_sqrt hpertKappa
      simpa [ch14ext_cor146ClosureSqrtKappa, B, B_inv] using h
    have hdenOne : 1 <= ch14ext_cor146ClosureSqrtKappa n A L U t +
        Real.sqrt (kappa2 A A_inv) := by linarith
    have hdenPos : 0 < ch14ext_cor146ClosureSqrtKappa n A L U t +
        Real.sqrt (kappa2 A A_inv) := lt_of_lt_of_le (by norm_num) hdenOne
    change |(ch14ext_cor146ClosureSqrtKappa n A L U t +
      Real.sqrt (kappa2 A A_inv))⁻¹| <= 1
    rw [abs_of_pos (inv_pos.mpr hdenPos)]
    exact inv_le_one_of_one_le₀ hdenOne
  have hproduct :
      (fun t => (kappa2 (B t) (B_inv t) - kappa2 A A_inv) *
        (ch14ext_cor146ClosureSqrtKappa n A L U t +
          Real.sqrt (kappa2 A A_inv))⁻¹)
        =O[l] (fun t => (fp t).u) := by
    simpa only [mul_one] using hkappa.mul hdenInv
  apply hproduct.congr'
  · filter_upwards with t
    have hpert0 : 0 <= kappa2 (B t) (B_inv t) := by
      unfold kappa2
      exact mul_nonneg (opNorm2_nonneg (B t)) (opNorm2_nonneg (B_inv t))
    have hsource0 : 0 <= kappa2 A A_inv := by
      unfold kappa2
      exact mul_nonneg (opNorm2_nonneg A) (opNorm2_nonneg A_inv)
    have hdenPos : 0 < ch14ext_cor146ClosureSqrtKappa n A L U t +
        Real.sqrt (kappa2 A A_inv) := by
      have hpertKappa := ch14ext_cor146_one_le_kappa2_of_isInverse
        n (B t) (B_inv t) hnpos (by
          simpa [B, B_inv] using hreg.perturbed_inverse t)
      have hpertRoot : 1 <= ch14ext_cor146ClosureSqrtKappa n A L U t := by
        have h := Real.sqrt_le_sqrt hpertKappa
        simpa [ch14ext_cor146ClosureSqrtKappa, B, B_inv] using h
      linarith
    have hsqrt :
        ch14ext_cor146ClosureSqrtKappa n A L U t -
            Real.sqrt (kappa2 A A_inv) =
          (kappa2 (B t) (B_inv t) - kappa2 A A_inv) *
            (ch14ext_cor146ClosureSqrtKappa n A L U t +
              Real.sqrt (kappa2 A A_inv))⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (eq_div_iff hdenPos.ne').2
      calc
        (ch14ext_cor146ClosureSqrtKappa n A L U t -
            Real.sqrt (kappa2 A A_inv)) *
            (ch14ext_cor146ClosureSqrtKappa n A L U t +
              Real.sqrt (kappa2 A A_inv)) =
            ch14ext_cor146ClosureSqrtKappa n A L U t ^ 2 -
              Real.sqrt (kappa2 A A_inv) ^ 2 := by ring
        _ = kappa2 (B t) (B_inv t) - kappa2 A A_inv := by
          rw [Real.sq_sqrt hsource0]
          simpa [ch14ext_cor146ClosureSqrtKappa, B, B_inv] using
            congrArg (fun x => x - kappa2 A A_inv) (Real.sq_sqrt hpert0)
    exact hsqrt.symm
  · exact Filter.EventuallyEq.rfl

theorem ch14ext_cor146Closure_sqrtKappa_family_isBigO_one
    {I : Type*} {l : Filter I} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U : I -> Fin n -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (nhds 0)) (hnpos : 1 <= n)
    (hreg : Ch14Cor146UniformInverseRegularity l n A A_inv fp L U) :
    (fun t => ch14ext_cor146ClosureSqrtKappa n A L U t)
      =O[l] (fun _ : I => (1 : Real)) := by
  have hd := ch14ext_cor146_sqrtKappa_proximity_family_isBigO_u
    n fp A A_inv L U hnpos hreg
  have hd1 := hd.trans (hu.isBigO_one Real)
  have hc : (fun _ : I => Real.sqrt (kappa2 A A_inv))
      =O[l] (fun _ : I => (1 : Real)) := by
    simpa using
      (Asymptotics.isBigO_refl (fun _ : I => (1 : Real)) l).const_mul_left
        (Real.sqrt (kappa2 A A_inv))
  simpa only [ch14ext_cor146ClosureSqrtKappa, sub_add_cancel] using hd1.add hc

/-- The entire residual spectral replacement is `O(u)` along a genuine
vanishing-roundoff family. -/
theorem ch14ext_cor146ResidualSpectralCorrection_family_isBigO_u
    {I : Type*} {l : Filter I} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U : I -> Fin n -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (nhds 0))
    (hnpos : 1 <= n)
    (hn : Filter.Eventually (fun t => gammaValid (fp t) n) l)
    (hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (fp t) n < 1) l)
    (hreg : Ch14Cor146UniformInverseRegularity l n A A_inv fp L U) :
    (fun t => ch14ext_cor146ResidualSpectralCorrection
      n fp A A_inv L U t) =O[l] (fun t => (fp t).u) := by
  have hfactor := ch14ext_cor146_luFactor_sub_one_family_isBigO_u
    fp n hu hn hsmall
  have hroot := ch14ext_cor146Closure_sqrtKappa_family_isBigO_one
    n fp A A_inv L U hu hnpos hreg
  have hproximity := ch14ext_cor146_sqrtKappa_proximity_family_isBigO_u
    n fp A A_inv L U hnpos hreg
  have hproduct :
      (fun t =>
        ((1 - (n : Real) * gamma (fp t) n)⁻¹ - 1) *
          ch14ext_cor146ClosureSqrtKappa n A L U t)
        =O[l] (fun t => (fp t).u) := by
    simpa only [mul_one] using hfactor.mul hroot
  have hsum := hproduct.add hproximity
  have habs := hsum.norm_left
  apply habs.congr'
  · filter_upwards with t
    simp only [ch14ext_cor146ResidualSpectralCorrection,
      ch14ext_cor146ClosureSqrtKappa, Real.norm_eq_abs]
    congr 1
    ring
  · exact Filter.EventuallyEq.rfl

/-- The correction between the concrete and printed forward coefficients is
`O(u)`; multiplying it by the leading `u` therefore contributes `O(u^2)`. -/
theorem ch14ext_cor146ForwardCoefficientCorrection_family_isBigO_u
    {I : Type*} {l : Filter I} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U : I -> Fin n -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (nhds 0))
    (hnpos : 1 <= n)
    (hn : Filter.Eventually (fun t => gammaValid (fp t) n) l)
    (hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (fp t) n < 1) l)
    (hreg : Ch14Cor146UniformInverseRegularity l n A A_inv fp L U) :
    (fun t => ch14ext_cor146ForwardCoefficientCorrection
      n fp A A_inv L U t) =O[l] (fun t => (fp t).u) := by
  have hfactor := (ch14ext_cor146_luFactor_sub_one_family_isBigO_u
    fp n hu hn hsmall).norm_left
  have hroot := (ch14ext_cor146_sqrtKappa_proximity_family_isBigO_u
    n fp A A_inv L U hnpos hreg).norm_left
  have h1 := hfactor.const_mul_left
    (2 * (n : Real) ^ 2 * Real.sqrt n * kappa2 A A_inv)
  have h2 := hroot.const_mul_left (6 * (n : Real) ^ 2)
  simpa only [ch14ext_cor146ForwardCoefficientCorrection,
    ch14ext_cor146ClosureSqrtKappa, Real.norm_eq_abs, mul_assoc] using h1.add h2

/-- The source-literal residual remainder, including the spectral replacement,
is genuinely `O(u^2)` for uniformly bounded successful-run data. -/
theorem ch14ext_cor146ResidualSourceRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l]
    (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U_inv : I -> Fin n -> Fin n -> Real)
    (V : I -> Nat -> Fin n -> Fin n -> Real)
    (xseq : I -> Nat -> Fin n -> Real) (x_hat : I -> Fin n -> Real)
    (start : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (nhds 0))
    (hnpos : 1 <= n)
    (hn : Filter.Eventually (fun t => gammaValid (fp t) n) l)
    (hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (fp t) n < 1) l)
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hX : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (ch14ext_cor146ClosureX n V start))
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (fun t => V t start))
    (hUinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U_inv)
    (hy : Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t => xseq t start))
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat)
    (hreg : Ch14Cor146UniformInverseRegularity l n A A_inv fp L
      (fun t => V t start)) :
    (fun t => ch14ext_cor146ResidualSourceRemainder n fp A A_inv L U_inv
      V xseq x_hat start t) =O[l] (fun t => (fp t).u ^ 2) := by
  have hrho := ch14ext_cor146ResidualClosureRemainder_norm2_family_isBigO_u_sq
    n fp L (ch14ext_cor146ClosureX n V start) (fun t => V t start) U_inv
      (fun t => xseq t start) x_hat hu hL hX hU hUinv hy hx
  have hspectral := ch14ext_cor146ResidualSpectralCorrection_family_isBigO_u
    n fp A A_inv L (fun t => V t start) hu hnpos hn hsmall hreg
  have hxnorm : (fun t => vecNorm2 (x_hat t))
      =O[l] (fun _ : I => (1 : Real)) :=
    ch14ext_cor146Closure_vecNorm2_family_isBigO hx
  have huO := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hleadRaw := (huO.mul hspectral).mul hxnorm
  have hlead :
      (fun t => 8 * (n : Real) ^ 3 * (fp t).u *
        ch14ext_cor146ResidualSpectralCorrection n fp A A_inv L
          (fun s => V s start) t * opNorm2 A * vecNorm2 (x_hat t))
        =O[l] (fun t => (fp t).u ^ 2) := by
    have h := hleadRaw.const_mul_left (8 * (n : Real) ^ 3 * opNorm2 A)
    simpa only [pow_two, mul_one, mul_assoc, mul_left_comm, mul_comm] using h
  simpa only [ch14ext_cor146ResidualSourceRemainder] using hrho.add hlead

/-- The absolute forward source remainder is genuinely `O(u^2)`: this
combines the literal (14.32) remainder with the `O(u)` coefficient correction
times the leading `u`. -/
theorem ch14ext_cor146ForwardAbsoluteSourceRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l]
    (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U_inv : I -> Fin n -> Fin n -> Real)
    (V : I -> Nat -> Fin n -> Fin n -> Real)
    (xseq : I -> Nat -> Fin n -> Real)
    (z x_hat : I -> Fin n -> Real) (start : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (nhds 0))
    (hnpos : 1 <= n)
    (hn : Filter.Eventually (fun t => gammaValid (fp t) n) l)
    (hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (fp t) n < 1) l)
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (fun t => V t start))
    (hP : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (ch14ext_cor146ClosureP n V start))
    (hUinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U_inv)
    (hz : Ch14Cor146ClosureVectorFamilyIsBigOOne l z)
    (hy : Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t => xseq t start))
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat)
    (hreg : Ch14Cor146UniformInverseRegularity l n A A_inv fp L
      (fun t => V t start)) :
    (fun t => ch14ext_cor146ForwardAbsoluteSourceRemainder n fp A A_inv
      L U_inv V xseq z x_hat start t) =O[l] (fun t => (fp t).u ^ 2) := by
  have hrhoRaw := ch14ext_cor146ForwardLiteralHigherOrder_norm2_family_isBigO_u_sq
    n fp A_inv L (fun t => V t start) (ch14ext_cor146ClosureP n V start)
      U_inv z (fun t => xseq t start) x_hat hu hL hU hP hUinv hz hy hx
  have hrho :
      (fun t => vecNorm2 (ch14ext_cor146ConcreteForwardRemainder n (fp t)
        A_inv (L t) (U_inv t) (V t) (xseq t) (z t) (x_hat t) start))
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [ch14ext_cor146ConcreteForwardRemainder,
      ch14ext_cor146ClosureP] using hrhoRaw
  have hcorr := ch14ext_cor146ForwardCoefficientCorrection_family_isBigO_u
    n fp A A_inv L (fun t => V t start) hu hnpos hn hsmall hreg
  have hxnorm : (fun t => vecNorm2 (x_hat t))
      =O[l] (fun _ : I => (1 : Real)) :=
    ch14ext_cor146Closure_vecNorm2_family_isBigO hx
  have huO := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hextraRaw := (huO.mul hcorr).mul hxnorm
  have hextra :
      (fun t => (fp t).u *
        ch14ext_cor146ForwardCoefficientCorrection n fp A A_inv L
          (fun s => V s start) t * vecNorm2 (x_hat t))
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two, mul_one, mul_assoc] using hextraRaw
  simpa only [ch14ext_cor146ForwardAbsoluteSourceRemainder] using
    hrho.add hextra

/-- The ratio-removal correction is also genuinely `O(u^2)`.  This is a
family statement over a nondegenerate filter, not a fixed-`u` existential
bound. -/
theorem ch14ext_cor146ForwardRelativeSourceRemainder_family_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l]
    (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U_inv : I -> Fin n -> Fin n -> Real)
    (V : I -> Nat -> Fin n -> Fin n -> Real)
    (xseq : I -> Nat -> Fin n -> Real)
    (z x_hat : I -> Fin n -> Real) (x : Fin n -> Real) (start : Nat)
    (hu : Tendsto (fun t => (fp t).u) l (nhds 0))
    (hnpos : 1 <= n)
    (hn : Filter.Eventually (fun t => gammaValid (fp t) n) l)
    (hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (fp t) n < 1) l)
    (hL : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L)
    (hU : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (fun t => V t start))
    (hP : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (ch14ext_cor146ClosureP n V start))
    (hUinv : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U_inv)
    (hz : Ch14Cor146ClosureVectorFamilyIsBigOOne l z)
    (hy : Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t => xseq t start))
    (hx : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat)
    (hreg : Ch14Cor146UniformInverseRegularity l n A A_inv fp L
      (fun t => V t start)) :
    (fun t => ch14ext_cor146ForwardRelativeSourceRemainder n fp A A_inv
      L U_inv V xseq z x_hat x start t) =O[l] (fun t => (fp t).u ^ 2) := by
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  let q : I -> Real := fun t => c * (fp t).u
  have huO := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hq : q =O[l] (fun t => (fp t).u) := by
    simpa only [q] using huO.const_mul_left c
  have hqSq : (fun t => q t ^ 2) =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hq.mul hq
  have hqZero : Tendsto q l (nhds 0) := by
    simpa only [q, mul_zero] using hu.const_mul c
  have hden : Tendsto (fun t => 1 - q t) l (nhds 1) := by
    simpa using hqZero.const_sub 1
  have hinvOne : (fun t => (1 - q t)⁻¹)
      =O[l] (fun _ : I => (1 : Real)) := by
    have hinv : Tendsto (fun t => (1 - q t)⁻¹) l (nhds (1 : Real)) := by
      simpa using hden.inv₀ one_ne_zero
    exact hinv.isBigO_one Real
  have hterm1 : (fun t => q t ^ 2 * (1 - q t)⁻¹)
      =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hqSq.mul hinvOne
  have habs := ch14ext_cor146ForwardAbsoluteSourceRemainder_family_isBigO_u_sq
    n fp A A_inv L U_inv V xseq z x_hat start hu hnpos hn hsmall
      hL hU hP hUinv hz hy hx hreg
  have hxconst : (fun _ : I => (vecNorm2 x)⁻¹)
      =O[l] (fun _ : I => (1 : Real)) := by
    simpa using
      (Asymptotics.isBigO_refl (fun _ : I => (1 : Real)) l).const_mul_left
        (vecNorm2 x)⁻¹
  have hterm2 :
      (fun t => ch14ext_cor146ForwardAbsoluteSourceRemainder n fp A A_inv
        L U_inv V xseq z x_hat start t * (1 - q t)⁻¹ * (vecNorm2 x)⁻¹)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using (habs.mul hinvOne).mul hxconst
  simpa only [ch14ext_cor146ForwardRelativeSourceRemainder, c, q] using
    hterm1.add hterm2

/-! ## Exact source-literal pointwise endpoints -/

/-- **Corollary 14.6 residual with the literal source matrix constant.**

This invokes the concrete (14.31) recurrence and the constructed-Q envelope
closure.  The perturbed condition factor and the exact LU prefactor are moved
into the explicit remainder; no residual endpoint is assumed. -/
theorem ch14ext_cor146_concrete_residual_source_literal
    {I : Type*} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U_inv R_inv : I -> Fin n -> Fin n -> Real)
    (b : Fin n -> Real)
    (V : I -> Nat -> Fin n -> Fin n -> Real)
    (xseq : I -> Nat -> Fin n -> Real) (x_hat : I -> Fin n -> Real)
    (start : Nat) (t : I)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (L t) (V t start) (gamma (fp t) n))
    (hpivPos : forall i : Fin n, 0 < V t start i i)
    (hsym : forall i j : Fin n,
      V t start i j = V t start i i * L t j i)
    (hUInv : IsInverse n (V t start) (U_inv t))
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n (V t start))
      (R_inv t))
    (hn : gammaValid (fp t) n) (hnpos : 1 <= n)
    (h3 : gammaValid (fp t) 3)
    (hsmall : (n : Real) * gamma (fp t) n < 1)
    (hidx : forall s : Nat, s < n - 1 -> start + s < n)
    (hVfinal : V t (start + (n - 1)) = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat t i = xseq t (start + (n - 1)) i)
    (hyStart : xseq t start = fl_forwardSub (fp t) n (L t) b)
    (hVrec : forall s : Nat, (hs : s < n - 1) ->
      V t (start + (s + 1)) =
        ch14ext_gjeStepMatrix (fp t) n (V t (start + s))
          ⟨start + s, hidx s hs⟩)
    (hxrec : forall s : Nat, (hs : s < n - 1) ->
      xseq t (start + (s + 1)) =
        ch14ext_gjeStepVec (fp t) n (V t (start + s))
          ⟨start + s, hidx s hs⟩ (xseq t (start + s)))
    (hpivLoop : forall s : Nat, (hs : s < n - 1) ->
      V t (start + s) ⟨start + s, hidx s hs⟩
        ⟨start + s, hidx s hs⟩ ≠ 0) :
    vecNorm2 (fun i : Fin n => b i - matMulVec n A (x_hat t) i) <=
      8 * (n : Real) ^ 3 * (fp t).u * Real.sqrt (kappa2 A A_inv) *
          opNorm2 A * vecNorm2 (x_hat t) +
        ch14ext_cor146ResidualSourceRemainder n fp A A_inv L U_inv
          V xseq x_hat start t := by
  let factor := (1 - (n : Real) * gamma (fp t) n)⁻¹
  let khat := ch14ext_cor146ClosureSqrtKappa n A L
    (fun s => V s start) t
  let ksrc := Real.sqrt (kappa2 A A_inv)
  let C := 8 * (n : Real) ^ 3 * (fp t).u * opNorm2 A * vecNorm2 (x_hat t)
  let rho := vecNorm2 (fun i =>
    ch14ext_cor146ResidualClosureRemainder n (fp t) (L t)
      (ch14ext_cor146ClosureX n V start t) (V t start) (U_inv t)
      (xseq t start) (x_hat t) i)
  have hbase := ch14ext_cor146_concrete_residual_norm2_with_explicit_remainder
    n (fp t) A (L t) (U_inv t) (R_inv t) b (x_hat t) (V t) (xseq t)
      start hSPD hLU hpivPos hsym hUInv hRInv hn hnpos h3 hsmall hidx
      hVfinal hxfinal hyStart hVrec hxrec hpivLoop
  have hAhat : ch14ext_cor146ClosureAhat n A L (fun s => V s start) t =
      (fun i j => A i j +
        ch14ext_cor146_symmetricGEDelta n A (L t) (V t start) i j) := rfl
  have hspectral : factor * khat <= ksrc + |factor * khat - ksrc| := by
    linarith [le_abs_self (factor * khat - ksrc)]
  have hC0 : 0 <= C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (fp t).u_nonneg)
        (opNorm2_nonneg A))
      (vecNorm2_nonneg (x_hat t))
  have hbase' :
      vecNorm2 (fun i : Fin n => b i - matMulVec n A (x_hat t) i) <=
        C * (factor * khat) + rho := by
    convert hbase using 1 <;>
      simp [C, factor, khat, rho, ch14ext_cor146ClosureSqrtKappa,
        hAhat, ch14ext_cor146ClosureX] <;> ring
  calc
    vecNorm2 (fun i : Fin n => b i - matMulVec n A (x_hat t) i) <=
        C * (factor * khat) + rho := hbase'
    _ <= C * (ksrc + |factor * khat - ksrc|) + rho :=
      add_le_add (mul_le_mul_of_nonneg_left hspectral hC0) (le_refl rho)
    _ = 8 * (n : Real) ^ 3 * (fp t).u * Real.sqrt (kappa2 A A_inv) *
          opNorm2 A * vecNorm2 (x_hat t) +
        ch14ext_cor146ResidualSourceRemainder n fp A A_inv L U_inv
          V xseq x_hat start t := by
      simp only [ch14ext_cor146ResidualSourceRemainder,
        ch14ext_cor146ResidualSpectralCorrection, C, factor, khat, ksrc, rho]
      ring

/-- **Corollary 14.6 absolute forward error with the literal printed
coefficient.**

The concrete (14.32) theorem is used directly.  The LU prefactor and perturbed
square-root condition number are retained in an explicit correction, while
the source first-order coefficient is exactly `8*n^2*sqrt(n)*kappa2(A)`.
No forward-error conclusion is assumed. -/
theorem ch14ext_cor146_concrete_forward_absolute_source_literal
    {I : Type*} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U_inv R_inv : I -> Fin n -> Fin n -> Real)
    (b x : Fin n -> Real)
    (V : I -> Nat -> Fin n -> Fin n -> Real)
    (xseq : I -> Nat -> Fin n -> Real)
    (z x_hat : I -> Fin n -> Real) (start : Nat) (t : I)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (L t) (V t start) (gamma (fp t) n))
    (hpivPos : forall i : Fin n, 0 < V t start i i)
    (hsym : forall i j : Fin n,
      V t start i j = V t start i i * L t j i)
    (hAInv : IsInverse n A A_inv)
    (hUInv : IsInverse n (V t start) (U_inv t))
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n (V t start))
      (R_inv t))
    (hn : gammaValid (fp t) n) (hnpos : 1 <= n)
    (h3 : gammaValid (fp t) 3)
    (hsmall : (n : Real) * gamma (fp t) n < 1)
    (hidx : forall s : Nat, s < n - 1 -> start + s < n)
    (hVfinal : V t (start + (n - 1)) = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat t i = xseq t (start + (n - 1)) i)
    (hyStart : xseq t start = fl_forwardSub (fp t) n (L t) b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n,
      matMulVec n (V t start) (z t) i = xseq t start i)
    (hVrec : forall s : Nat, (hs : s < n - 1) ->
      V t (start + (s + 1)) =
        ch14ext_gjeStepMatrix (fp t) n (V t (start + s))
          ⟨start + s, hidx s hs⟩)
    (hxrec : forall s : Nat, (hs : s < n - 1) ->
      xseq t (start + (s + 1)) =
        ch14ext_gjeStepVec (fp t) n (V t (start + s))
          ⟨start + s, hidx s hs⟩ (xseq t (start + s)))
    (hpivLoop : forall s : Nat, (hs : s < n - 1) ->
      V t (start + s) ⟨start + s, hidx s hs⟩
        ⟨start + s, hidx s hs⟩ ≠ 0) :
    vecNorm2 (fun i : Fin n => x i - x_hat t i) <=
      8 * (n : Real) ^ 2 * Real.sqrt n * (fp t).u * kappa2 A A_inv *
          vecNorm2 (x_hat t) +
        ch14ext_cor146ForwardAbsoluteSourceRemainder n fp A A_inv L U_inv
          V xseq z x_hat start t := by
  let factor := (1 - (n : Real) * gamma (fp t) n)⁻¹
  let khat := ch14ext_cor146ClosureSqrtKappa n A L
    (fun s => V s start) t
  let ksrc := Real.sqrt (kappa2 A A_inv)
  let kap := kappa2 A A_inv
  let a := 2 * (n : Real) ^ 2 * Real.sqrt n * kap
  let d := 6 * (n : Real) ^ 2
  let raw := a * factor + d * khat
  let printed := 8 * (n : Real) ^ 2 * Real.sqrt n * kap
  let corr := ch14ext_cor146ForwardCoefficientCorrection n fp A A_inv L
    (fun s => V s start) t
  let rho := vecNorm2 (ch14ext_cor146ConcreteForwardRemainder n (fp t) A_inv
    (L t) (U_inv t) (V t) (xseq t) (z t) (x_hat t) start)
  have hbase := ch14ext_cor146_concrete_forward_norm2
    n (fp t) A A_inv (L t) (U_inv t) (R_inv t) b x (z t) (x_hat t)
      (V t) (xseq t) start hSPD hLU hpivPos hsym hAInv.1 hUInv hRInv
      hn hnpos h3 hsmall hidx hVfinal hxfinal hyStart hExact hUz hVrec
      hxrec hpivLoop
  have hAhat : ch14ext_cor146ClosureAhat n A L (fun s => V s start) t =
      (fun i j => A i j +
        ch14ext_cor146_symmetricGEDelta n A (L t) (V t start) i j) := rfl
  have hkap1 := ch14ext_cor146_one_le_kappa2_of_isInverse
    n A A_inv hnpos hAInv
  have hkap0 : 0 <= kap := by simpa [kap] using le_trans (by norm_num) hkap1
  have hksrc : ksrc <= kap := by
    simpa [ksrc, kap] using
      ch14ext_cor146_sqrt_kappa2_le_kappa2_of_isInverse n A A_inv hnpos hAInv
  have hnR : (1 : Real) <= (n : Real) := by exact_mod_cast hnpos
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
      vecNorm2 (fun i : Fin n => x i - x_hat t i) <=
        raw * ((fp t).u * vecNorm2 (x_hat t)) + rho := by
    convert hbase using 1 <;>
      simp [raw, a, d, factor, khat, kap, rho,
        ch14ext_cor146ClosureSqrtKappa, hAhat] <;> ring
  have hmult0 : 0 <= (fp t).u * vecNorm2 (x_hat t) :=
    mul_nonneg (fp t).u_nonneg (vecNorm2_nonneg (x_hat t))
  calc
    vecNorm2 (fun i : Fin n => x i - x_hat t i) <=
        raw * ((fp t).u * vecNorm2 (x_hat t)) + rho := hbase'
    _ <= (printed + corr) * ((fp t).u * vecNorm2 (x_hat t)) + rho :=
      add_le_add
        (mul_le_mul_of_nonneg_right hraw hmult0) (le_refl rho)
    _ = 8 * (n : Real) ^ 2 * Real.sqrt n * (fp t).u * kappa2 A A_inv *
          vecNorm2 (x_hat t) +
        ch14ext_cor146ForwardAbsoluteSourceRemainder n fp A A_inv L U_inv
          V xseq z x_hat start t := by
      simp only [ch14ext_cor146ForwardAbsoluteSourceRemainder,
        printed, corr, rho, kap]
      ring

/-- **Full source-literal Corollary 14.6 forward endpoint.**

The factor `||xhat||_2/||x||_2` is eliminated algebraically.  The only extra
successful-run assumption is the transparent first-order bootstrap `q < 1`,
where `q = 8*n^2*sqrt(n)*u*kappa2(A)`; no forward conclusion is assumed. -/
theorem ch14ext_cor146_concrete_forward_relative_source_literal
    {I : Type*} (n : Nat) (fp : I -> FPModel)
    (A A_inv : Fin n -> Fin n -> Real)
    (L U_inv R_inv : I -> Fin n -> Fin n -> Real)
    (b x : Fin n -> Real)
    (V : I -> Nat -> Fin n -> Fin n -> Real)
    (xseq : I -> Nat -> Fin n -> Real)
    (z x_hat : I -> Fin n -> Real) (start : Nat) (t : I)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (L t) (V t start) (gamma (fp t) n))
    (hpivPos : forall i : Fin n, 0 < V t start i i)
    (hsym : forall i j : Fin n,
      V t start i j = V t start i i * L t j i)
    (hAInv : IsInverse n A A_inv)
    (hUInv : IsInverse n (V t start) (U_inv t))
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n (V t start))
      (R_inv t))
    (hn : gammaValid (fp t) n) (hnpos : 1 <= n)
    (h3 : gammaValid (fp t) 3)
    (hsmall : (n : Real) * gamma (fp t) n < 1)
    (hidx : forall s : Nat, s < n - 1 -> start + s < n)
    (hVfinal : V t (start + (n - 1)) = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat t i = xseq t (start + (n - 1)) i)
    (hyStart : xseq t start = fl_forwardSub (fp t) n (L t) b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n,
      matMulVec n (V t start) (z t) i = xseq t start i)
    (hVrec : forall s : Nat, (hs : s < n - 1) ->
      V t (start + (s + 1)) =
        ch14ext_gjeStepMatrix (fp t) n (V t (start + s))
          ⟨start + s, hidx s hs⟩)
    (hxrec : forall s : Nat, (hs : s < n - 1) ->
      xseq t (start + (s + 1)) =
        ch14ext_gjeStepVec (fp t) n (V t (start + s))
          ⟨start + s, hidx s hs⟩ (xseq t (start + s)))
    (hpivLoop : forall s : Nat, (hs : s < n - 1) ->
      V t (start + s) ⟨start + s, hidx s hs⟩
        ⟨start + s, hidx s hs⟩ ≠ 0)
    (hxpos : 0 < vecNorm2 x)
    (hbootstrap :
      8 * (n : Real) ^ 2 * Real.sqrt n * (fp t).u * kappa2 A A_inv < 1) :
    vecNorm2 (fun i : Fin n => x i - x_hat t i) / vecNorm2 x <=
      8 * (n : Real) ^ 2 * Real.sqrt n * (fp t).u * kappa2 A A_inv +
        ch14ext_cor146ForwardRelativeSourceRemainder n fp A A_inv L U_inv
          V xseq z x_hat x start t := by
  let e := vecNorm2 (fun i : Fin n => x i - x_hat t i)
  let xn := vecNorm2 x
  let xhn := vecNorm2 (x_hat t)
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  let q := c * (fp t).u
  let r := ch14ext_cor146ForwardAbsoluteSourceRemainder n fp A A_inv
    L U_inv V xseq z x_hat start t
  have habs := ch14ext_cor146_concrete_forward_absolute_source_literal
    n fp A A_inv L U_inv R_inv b x V xseq z x_hat start t hSPD hLU
      hpivPos hsym hAInv hUInv hRInv hn hnpos h3 hsmall hidx hVfinal
      hxfinal hyStart hExact hUz hVrec hxrec hpivLoop
  have habs' : e <= q * xhn + r := by
    dsimp [e, xhn, r]
    calc
      vecNorm2 (fun i : Fin n => x i - x_hat t i) <=
          8 * (n : Real) ^ 2 * Real.sqrt n * (fp t).u * kappa2 A A_inv *
            vecNorm2 (x_hat t) +
          ch14ext_cor146ForwardAbsoluteSourceRemainder n fp A A_inv L U_inv
            V xseq z x_hat start t := habs
      _ = q * vecNorm2 (x_hat t) +
          ch14ext_cor146ForwardAbsoluteSourceRemainder n fp A A_inv L U_inv
            V xseq z x_hat start t := by
        dsimp [q, c, ch14ext_cor146ForwardPrintedCoefficient]
        ring
  have hxhat : xhn <= xn + e := by
    calc
      xhn = vecNorm2 (fun i : Fin n => x i + (x_hat t i - x i)) := by
        dsimp [xhn]
        apply congrArg vecNorm2
        funext i
        ring
      _ <= vecNorm2 x + vecNorm2 (fun i : Fin n => x_hat t i - x i) :=
        vecNorm2_add_le x (fun i : Fin n => x_hat t i - x i)
      _ = xn + e := by
        dsimp [xn, e]
        rw [vecNorm2_sub_comm]
  have hkap1 := ch14ext_cor146_one_le_kappa2_of_isInverse
    n A A_inv hnpos hAInv
  have hkap0 : 0 <= kappa2 A A_inv := le_trans (by norm_num) hkap1
  have hc0 : 0 <= c := by
    dsimp [c, ch14ext_cor146ForwardPrintedCoefficient]
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg n)) hkap0
  have hq0 : 0 <= q := mul_nonneg hc0 (fp t).u_nonneg
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
  have hrelative :
      e / xn <= ((q * xn + r) / (1 - q)) / xn :=
    div_le_div_of_nonneg_right hsolve hxpos.le
  have hxn : xn ≠ 0 := by
    dsimp [xn]
    exact hxpos.ne'
  calc
    vecNorm2 (fun i : Fin n => x i - x_hat t i) / vecNorm2 x = e / xn := rfl
    _ <= ((q * xn + r) / (1 - q)) / xn := hrelative
    _ = q + (q ^ 2 * (1 - q)⁻¹ + r * (1 - q)⁻¹ * xn⁻¹) := by
      field_simp [hden.ne', hxn]
      ring
    _ = 8 * (n : Real) ^ 2 * Real.sqrt n * (fp t).u * kappa2 A A_inv +
        ch14ext_cor146ForwardRelativeSourceRemainder n fp A A_inv L U_inv
          V xseq z x_hat x start t := by
      simp only [ch14ext_cor146ForwardRelativeSourceRemainder, c, q, r, xn,
        ch14ext_cor146ForwardPrintedCoefficient]
      ring

/-! ## Combined nonvacuous family endpoint -/

/-- Data and certificates for a vanishing-roundoff family of successful
Corollary 14.6 runs.  Every field is an algorithm, model, boundedness, inverse,
or smallness premise.  In particular, this structure has no residual or
forward-error conclusion field. -/
structure Ch14Cor146SuccessfulRunFamily
    {I : Type*} (l : Filter I) (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) (start : Nat) where
  model : I -> FPModel
  L_hat : I -> Fin n -> Fin n -> Real
  U_inv : I -> Fin n -> Fin n -> Real
  R_inv : I -> Fin n -> Fin n -> Real
  V : I -> Nat -> Fin n -> Fin n -> Real
  xseq : I -> Nat -> Fin n -> Real
  z : I -> Fin n -> Real
  x_hat : I -> Fin n -> Real
  spd : IsSymPosDef n A
  dimension_pos : 1 <= n
  exact_solution_nonzero : 0 < vecNorm2 x
  lu_backward : forall t,
    LUBackwardError n A (L_hat t) (V t start) (gamma (model t) n)
  computed_pivots_pos : forall t i, 0 < V t start i i
  symmetric_factor_relation : forall t i j,
    V t start i j = V t start i i * L_hat t j i
  upper_inverse : forall t, IsInverse n (V t start) (U_inv t)
  scaled_upper_inverse : forall t,
    IsInverse n (ch14ext_cor146_scaledUpper n (V t start)) (R_inv t)
  gamma_n_valid : forall t, gammaValid (model t) n
  gamma_three_valid : forall t, gammaValid (model t) 3
  gamma_small : forall t, (n : Real) * gamma (model t) n < 1
  index_valid : forall s : Nat, s < n - 1 -> start + s < n
  final_matrix : forall t, V t (start + (n - 1)) = idMatrix n
  final_vector : forall t i,
    x_hat t i = xseq t (start + (n - 1)) i
  forward_substitution : forall t,
    xseq t start = fl_forwardSub (model t) n (L_hat t) b
  exact_solution : forall i, matMulVec n A x i = b i
  exact_upper_solve : forall t i,
    matMulVec n (V t start) (z t) i = xseq t start i
  matrix_recurrence : forall t s, (hs : s < n - 1) ->
    V t (start + (s + 1)) =
      ch14ext_gjeStepMatrix (model t) n (V t (start + s))
        ⟨start + s, index_valid s hs⟩
  vector_recurrence : forall t s, (hs : s < n - 1) ->
    xseq t (start + (s + 1)) =
      ch14ext_gjeStepVec (model t) n (V t (start + s))
        ⟨start + s, index_valid s hs⟩ (xseq t (start + s))
  loop_pivots_nonzero : forall t s, (hs : s < n - 1) ->
    V t (start + s) ⟨start + s, index_valid s hs⟩
      ⟨start + s, index_valid s hs⟩ ≠ 0
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (nhds 0)
  L_hat_isBigO_one : Ch14Cor146ClosureMatrixFamilyIsBigOOne l L_hat
  X_isBigO_one : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
    (ch14ext_cor146ClosureX n V start)
  U_hat_isBigO_one : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
    (fun t => V t start)
  P_isBigO_one : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
    (ch14ext_cor146ClosureP n V start)
  U_inv_isBigO_one : Ch14Cor146ClosureMatrixFamilyIsBigOOne l U_inv
  z_isBigO_one : Ch14Cor146ClosureVectorFamilyIsBigOOne l z
  y_isBigO_one : Ch14Cor146ClosureVectorFamilyIsBigOOne l
    (fun t => xseq t start)
  x_hat_isBigO_one : Ch14Cor146ClosureVectorFamilyIsBigOOne l x_hat
  uniform_inverse : Ch14Cor146UniformInverseRegularity l n A A_inv model
    L_hat (fun t => V t start)

/-- **Complete source-literal Corollary 14.6 family closure.**

The residual coefficient is exactly
`8*n^3*u*sqrt(kappa2 A A_inv)` (followed by `||A||_2 ||xhat||_2`), and the
relative forward coefficient is exactly
`8*n^2*sqrt(n)*u*kappa2 A A_inv`, i.e. `8*n^(5/2)*u*kappa2(A)`.  Both explicit
remainders are genuine `O(u^2)` statements over a required nonbottom filter.
The forward bootstrap is derived eventually from `u(t) -> 0`; it is not a
family assumption.  No fixed-`u` existential bound and no target endpoint
hypothesis is used. -/
theorem ch14ext_cor146_full_source_literal_family_endpoint
    {I : Type*} {l : Filter I} [NeBot l]
    (n : Nat) (A A_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) (start : Nat)
    (F : Ch14Cor146SuccessfulRunFamily l n A A_inv b x start) :
    (forall t,
      vecNorm2 (fun i : Fin n => b i - matMulVec n A (F.x_hat t) i) <=
        8 * (n : Real) ^ 3 * (F.model t).u * Real.sqrt (kappa2 A A_inv) *
            opNorm2 A * vecNorm2 (F.x_hat t) +
          ch14ext_cor146ResidualSourceRemainder n F.model A A_inv
            F.L_hat F.U_inv F.V F.xseq F.x_hat start t) ∧
    ((fun t => ch14ext_cor146ResidualSourceRemainder n F.model A A_inv
      F.L_hat F.U_inv F.V F.xseq F.x_hat start t)
        =O[l] (fun t => (F.model t).u ^ 2)) ∧
    (Filter.Eventually (fun t =>
      vecNorm2 (fun i : Fin n => x i - F.x_hat t i) / vecNorm2 x <=
        8 * (n : Real) ^ 2 * Real.sqrt n * (F.model t).u * kappa2 A A_inv +
          ch14ext_cor146ForwardRelativeSourceRemainder n F.model A A_inv
            F.L_hat F.U_inv F.V F.xseq F.z F.x_hat x start t) l) ∧
    ((fun t => ch14ext_cor146ForwardRelativeSourceRemainder n F.model
      A A_inv F.L_hat F.U_inv F.V F.xseq F.z F.x_hat x start t)
        =O[l] (fun t => (F.model t).u ^ 2)) := by
  have hn : Filter.Eventually (fun t => gammaValid (F.model t) n) l :=
    Filter.Eventually.of_forall F.gamma_n_valid
  have hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (F.model t) n < 1) l :=
    Filter.Eventually.of_forall F.gamma_small
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  have hqZero : Tendsto (fun t => c * (F.model t).u) l (nhds 0) := by
    simpa only [mul_zero] using F.unit_tendsto_zero.const_mul c
  have hqSmall : Filter.Eventually (fun t => c * (F.model t).u < 1) l :=
    (tendsto_order.1 hqZero).2 1 zero_lt_one
  have hbootstrap : Filter.Eventually (fun t =>
      8 * (n : Real) ^ 2 * Real.sqrt n * (F.model t).u *
        kappa2 A A_inv < 1) l := by
    filter_upwards [hqSmall] with t ht
    dsimp [c, ch14ext_cor146ForwardPrintedCoefficient] at ht
    convert ht using 1 <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    exact ch14ext_cor146_concrete_residual_source_literal
      n F.model A A_inv F.L_hat F.U_inv F.R_inv b F.V F.xseq F.x_hat
        start t F.spd (F.lu_backward t) (F.computed_pivots_pos t)
        (F.symmetric_factor_relation t) (F.upper_inverse t)
        (F.scaled_upper_inverse t) (F.gamma_n_valid t) F.dimension_pos
        (F.gamma_three_valid t) (F.gamma_small t) F.index_valid
        (F.final_matrix t) (F.final_vector t) (F.forward_substitution t)
        (F.matrix_recurrence t) (F.vector_recurrence t)
        (F.loop_pivots_nonzero t)
  · exact ch14ext_cor146ResidualSourceRemainder_family_isBigO_u_sq
      n F.model A A_inv F.L_hat F.U_inv F.V F.xseq F.x_hat start
        F.unit_tendsto_zero F.dimension_pos hn hsmall F.L_hat_isBigO_one
        F.X_isBigO_one F.U_hat_isBigO_one F.U_inv_isBigO_one
        F.y_isBigO_one F.x_hat_isBigO_one F.uniform_inverse
  · filter_upwards [hbootstrap] with t ht
    exact ch14ext_cor146_concrete_forward_relative_source_literal
      n F.model A A_inv F.L_hat F.U_inv F.R_inv b x F.V F.xseq F.z
        F.x_hat start t F.spd (F.lu_backward t) (F.computed_pivots_pos t)
        (F.symmetric_factor_relation t) F.uniform_inverse.source_inverse
        (F.upper_inverse t) (F.scaled_upper_inverse t) (F.gamma_n_valid t)
        F.dimension_pos (F.gamma_three_valid t) (F.gamma_small t)
        F.index_valid (F.final_matrix t) (F.final_vector t)
        (F.forward_substitution t) F.exact_solution (F.exact_upper_solve t)
        (F.matrix_recurrence t) (F.vector_recurrence t)
        (F.loop_pivots_nonzero t) F.exact_solution_nonzero
        ht
  · exact ch14ext_cor146ForwardRelativeSourceRemainder_family_isBigO_u_sq
      n F.model A A_inv F.L_hat F.U_inv F.V F.xseq F.z F.x_hat x start
        F.unit_tendsto_zero F.dimension_pos hn hsmall F.L_hat_isBigO_one
        F.U_hat_isBigO_one F.P_isBigO_one F.U_inv_isBigO_one
        F.z_isBigO_one F.y_isBigO_one F.x_hat_isBigO_one F.uniform_inverse

end NumStability.Ch14Ext
