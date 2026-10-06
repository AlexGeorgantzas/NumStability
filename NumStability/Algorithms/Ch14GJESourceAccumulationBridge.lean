-- Algorithms/Ch14GJESourceAccumulationBridge.lean
--
-- Source-active accumulation bridge for Higham (14.29).  The recursively
-- executed Algorithm 14.4 trace supplies (14.25b) and (14.26); the generic
-- accumulation machinery then yields the printed stage-2 forward error.

import NumStability.Algorithms.Ch14GaussJordanSourceClosure

namespace NumStability.Ch14Ext

open Finset BigOperators
open NumStability

/-- The algebraic last step of Higham (14.29).  Componentwise matrix and RHS
    recurrence bounds are accumulated separately and then combined using the
    exact initial relation `U x = y` and the final normalization `D = I`.

    This lemma deliberately knows nothing about how a stage is executed.  The
    source-facing theorem below derives both recurrence-bound premises from
    `ch14ext_gjeSourceTrace`; they are not assumptions of that endpoint. -/
theorem ch14ext_gje_stage2_forward_error_of_accumulation_14_29
    (fp : FPModel) (n : Nat)
    (N_hat : Fin n -> Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin n -> Real) (xseq : Nat -> Fin n -> Real)
    (x : Fin n -> Real) (start : Nat)
    (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hidx : forall t : Nat, t < n - 1 -> start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hUx : forall i : Fin n, matMulVec n (V start) x i = xseq start i)
    (hrecM : forall t : Nat, (ht : t < n - 1) -> forall i j : Fin n,
      |V (start + (t + 1)) i j -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * V (start + t) l j| <=
        gamma fp 3 *
          ∑ l : Fin n,
            |N_hat ⟨start + t, hidx t ht⟩ i l| * |V (start + t) l j|)
    (hrecX : forall t : Nat, (ht : t < n - 1) -> forall i : Fin n,
      |xseq (start + (t + 1)) i -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * xseq (start + t) l| <=
        gamma fp 3 *
          ∑ l : Fin n,
            |N_hat ⟨start + t, hidx t ht⟩ i l| * |xseq (start + t) l|) :
    forall i : Fin n,
      |x i - xseq (start + (n - 1)) i| <=
        gje_c₃ fp n *
          ch14ext_gjeForwardEnvelope n N_hat (V start) x (xseq start)
            start (n - 1) i := by
  intro i
  let P := gje_cumulative_product n N_hat start (start + (n - 1))
  let B := ch14ext_boundObj n N_hat (V start) start (n - 1)
  let bv := ch14ext_boundVec n N_hat (xseq start) start (n - 1)
  let R₁ := ∑ j : Fin n,
    (idMatrix n i j - matMul n P (V start) i j) * x j
  let R₂ := matMulVec n P (xseq start) i - xseq (start + (n - 1)) i
  have hM := ch14ext_matrixAccumulation_c3 n fp N_hat V start hnpos h3 hidx hrecM
  have hR := ch14ext_rhsAccumulation_c3 n fp N_hat xseq start hnpos h3 hidx hrecX
  have hM' : forall a b : Fin n,
      |idMatrix n a b - matMul n P (V start) a b| <= gje_c₃ fp n * B a b := by
    intro a b
    have h := hM a b
    rw [hVfinal] at h
    simpa [P, B] using h
  have hR' : |R₂| <= gje_c₃ fp n * bv i := by
    have h := hR i
    have hsym :
        |matMulVec n P (xseq start) i - xseq (start + (n - 1)) i| =
          |xseq (start + (n - 1)) i - matMulVec n P (xseq start) i| :=
      abs_sub_comm _ _
    rw [hsym]
    simpa [P, bv, R₂] using h
  have hUxFn : matMulVec n (V start) x = xseq start := by
    funext a
    exact hUx a
  have hPUx : matMulVec n (matMul n P (V start)) x i =
      matMulVec n P (xseq start) i := by
    rw [matMulVec_matMul, hUxFn]
  have hId : matMulVec n (idMatrix n) x i = x i := by
    rw [matMulVec_id]
  have hR₁eq : R₁ = x i - matMulVec n P (xseq start) i := by
    unfold R₁
    calc
      (∑ j : Fin n,
          (idMatrix n i j - matMul n P (V start) i j) * x j) =
          (∑ j : Fin n, idMatrix n i j * x j) -
            ∑ j : Fin n, matMul n P (V start) i j * x j := by
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = matMulVec n (idMatrix n) x i -
            matMulVec n (matMul n P (V start)) x i := rfl
      _ = x i - matMulVec n P (xseq start) i := by rw [hId, hPUx]
  have hdecomp : x i - xseq (start + (n - 1)) i = R₁ + R₂ := by
    rw [hR₁eq]
    unfold R₂
    ring
  have hBaction :
      (∑ j : Fin n, B i j * |x j|) =
        matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
          (matMulVec n (absMatrix n (V start)) (absVec n x)) i := by
    change matMulVec n B (absVec n x) i = _
    unfold B ch14ext_boundObj
    rw [matMulVec_matMul]
  have hR₁ : |R₁| <= gje_c₃ fp n *
      matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
        (matMulVec n (absMatrix n (V start)) (absVec n x)) i := by
    unfold R₁
    calc
      |∑ j : Fin n,
          (idMatrix n i j - matMul n P (V start) i j) * x j| <=
          ∑ j : Fin n,
            |(idMatrix n i j - matMul n P (V start) i j) * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n,
            |idMatrix n i j - matMul n P (V start) i j| * |x j| :=
        Finset.sum_congr rfl (fun j _ => abs_mul _ _)
      _ <= ∑ j : Fin n, (gje_c₃ fp n * B i j) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hM' i j) (abs_nonneg _)
      _ = gje_c₃ fp n * ∑ j : Fin n, B i j * |x j| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = gje_c₃ fp n *
          matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
            (matMulVec n (absMatrix n (V start)) (absVec n x)) i := by
        rw [hBaction]
  have hR₂ : |R₂| <= gje_c₃ fp n *
      matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
        (absVec n (xseq start)) i := by
    simpa [bv, ch14ext_boundVec] using hR'
  rw [hdecomp]
  refine le_trans (abs_add_le R₁ R₂) ?_
  unfold ch14ext_gjeForwardEnvelope
  calc
    |R₁| + |R₂| <=
        gje_c₃ fp n *
            matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
              (matMulVec n (absMatrix n (V start)) (absVec n x)) i +
          gje_c₃ fp n *
            matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
              (absVec n (xseq start)) i := add_le_add hR₁ hR₂
    _ = gje_c₃ fp n *
        (matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
            (matMulVec n (absMatrix n (V start)) (absVec n x)) i +
          matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
            (absVec n (xseq start)) i) := by ring

/-- **Reusable source-trace recurrence bridge for (14.25b) and (14.26).**

    The two conjuncts have exactly the `hrecM` and `hrecX` shapes consumed by
    the Chapter 14 accumulation and Q-construction theorems.  They are derived
    from the recursively executed source-active trace, upper triangularity,
    successful pivots, and the FP model.  No unrestricted GJE-step recurrence
    is assumed. -/
theorem ch14ext_gjeSourceTrace_recurrence_bounds_14_25b_14_26 {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n)
    (hidx : forall t : Nat, t < n - 1 -> 1 + t < n)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, hidx t ht⟩ ⟨1 + t, hidx t ht⟩ ≠ 0)
    (h3 : gammaValid fp 3) :
    (forall t : Nat, (ht : t < n - 1) -> forall i j : Fin n,
      |ch14ext_gjeSourceTraceMatrix fp 1 s (1 + (t + 1)) i j -
          ∑ l : Fin n,
            ch14ext_gjeSeqStages n (ch14ext_gjeSourceTraceMatrix fp 1 s)
              ⟨1 + t, hidx t ht⟩ i l *
              ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t) l j| <=
        gamma fp 3 *
          ∑ l : Fin n,
            |ch14ext_gjeSeqStages n (ch14ext_gjeSourceTraceMatrix fp 1 s)
              ⟨1 + t, hidx t ht⟩ i l| *
              |ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t) l j|) ∧
    (forall t : Nat, (ht : t < n - 1) -> forall i : Fin n,
      |ch14ext_gjeSourceTraceRhs fp 1 s (1 + (t + 1)) i -
          ∑ l : Fin n,
            ch14ext_gjeSeqStages n (ch14ext_gjeSourceTraceMatrix fp 1 s)
              ⟨1 + t, hidx t ht⟩ i l *
              ch14ext_gjeSourceTraceRhs fp 1 s (1 + t) l| <=
        gamma fp 3 *
          ∑ l : Fin n,
            |ch14ext_gjeSeqStages n (ch14ext_gjeSourceTraceMatrix fp 1 s)
              ⟨1 + t, hidx t ht⟩ i l| *
              |ch14ext_gjeSourceTraceRhs fp 1 s (1 + t) l|) := by
  let V := ch14ext_gjeSourceTraceMatrix fp 1 s
  let xseq := ch14ext_gjeSourceTraceRhs fp 1 s
  let N_hat := ch14ext_gjeSeqStages n V
  change
    (forall t : Nat, (ht : t < n - 1) -> forall i j : Fin n,
      |V (1 + (t + 1)) i j -
          ∑ l : Fin n, N_hat ⟨1 + t, hidx t ht⟩ i l * V (1 + t) l j| <=
        gamma fp 3 *
          ∑ l : Fin n,
            |N_hat ⟨1 + t, hidx t ht⟩ i l| * |V (1 + t) l j|) ∧
    (forall t : Nat, (ht : t < n - 1) -> forall i : Fin n,
      |xseq (1 + (t + 1)) i -
          ∑ l : Fin n, N_hat ⟨1 + t, hidx t ht⟩ i l * xseq (1 + t) l| <=
        gamma fp 3 *
          ∑ l : Fin n,
            |N_hat ⟨1 + t, hidx t ht⟩ i l| * |xseq (1 + t) l|)
  have hV0 : forall i j : Fin n, j.val < i.val -> V 1 i j = 0 := by
    intro i j hji
    simpa [V, ch14ext_gjeSourceTraceMatrix, ch14ext_gjeSourceTrace] using
      hUpper i j hji
  have hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (1 + (t + 1)) =
        ch14ext_gjeSourceStepMatrix fp n (V (1 + t)) ⟨1 + t, hidx t ht⟩ := by
    intro t ht
    simpa [V] using ch14ext_gjeSourceTraceMatrix_rec fp 1 s t (hidx t ht)
  have hxrec : forall t : Nat, (ht : t < n - 1) ->
      xseq (1 + (t + 1)) =
        ch14ext_gjeSourceStepVec fp n (V (1 + t)) ⟨1 + t, hidx t ht⟩
          (xseq (1 + t)) := by
    intro t ht
    simpa [V, xseq] using ch14ext_gjeSourceTraceRhs_rec fp 1 s t (hidx t ht)
  have hpiv' : forall t : Nat, (ht : t < n - 1) ->
      V (1 + t) ⟨1 + t, hidx t ht⟩ ⟨1 + t, hidx t ht⟩ ≠ 0 := by
    intro t ht
    simpa [V] using hpiv t ht
  have hlocal := ch14ext_gjeSource_sequence_local_14_25b_14_26
    fp V xseq 1 (n - 1) hidx hV0 hVrec hxrec hpiv' h3
  constructor
  · intro t ht i j
    have heq := (hlocal t ht).1 i j
    have hb := (hlocal t ht).2.1 i j
    calc
      |V (1 + (t + 1)) i j -
          ∑ l : Fin n, N_hat ⟨1 + t, hidx t ht⟩ i l * V (1 + t) l j| =
          |ch14ext_gjeSourceDeltaSeq fp n V 1 t i j| := by
            rw [heq]
            simp [N_hat, matMul]
      _ <= gamma fp 3 *
          ∑ l : Fin n,
            |N_hat ⟨1 + t, hidx t ht⟩ i l| * |V (1 + t) l j| := by
        simpa [N_hat, matMul, absMatrix] using hb
  · intro t ht i
    have heq := (hlocal t ht).2.2.2.2.1 i
    have hb := (hlocal t ht).2.2.2.2.2.1 i
    calc
      |xseq (1 + (t + 1)) i -
          ∑ l : Fin n, N_hat ⟨1 + t, hidx t ht⟩ i l * xseq (1 + t) l| =
          |ch14ext_gjeSourceFSeq fp n V xseq 1 t i| := by
            rw [heq]
            simp [N_hat, matMulVec]
      _ <= gamma fp 3 *
          ∑ l : Fin n,
            |N_hat ⟨1 + t, hidx t ht⟩ i l| * |xseq (1 + t) l| := by
        simpa [N_hat, matMulVec, absMatrix, absVec] using hb

/-- **Higham (14.29), recursively executed source-active Algorithm 14.4 trace.**

    Starting with the upper-triangular stage-1 state `s`, execute exactly the
    masked source steps `ch14ext_gjeSourceStepState` at indices `1,...,n-1`.
    Successful pivots and the source's `D = I` normalization are the only
    operational certificates.  The (14.25b)/(14.26) local bounds are derived
    from those concrete steps, fed into the generic accumulation, and combined
    to obtain

      `|x - xhat| <= c3 |X| (|U| |x| + |y|)`.

    In particular, this endpoint assumes neither unrestricted
    `ch14ext_gjeStepMatrix`/`ch14ext_gjeStepVec` recurrences nor its conclusion. -/
theorem ch14ext_gjeSourceTrace_stage2_forward_error_14_29 {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) (x : Fin n -> Real)
    (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hUx : forall i : Fin n, matMulVec n s.matrix x i = s.rhs i)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + t)
          ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |x i - ch14ext_gjeSourceTraceRhs fp 1 s n i| <=
        gje_c₃ fp n *
          ch14ext_gjeForwardEnvelope n
            (ch14ext_gjeSeqStages n (ch14ext_gjeSourceTraceMatrix fp 1 s))
            s.matrix x s.rhs 1 (n - 1) i := by
  let V := ch14ext_gjeSourceTraceMatrix fp 1 s
  let xseq := ch14ext_gjeSourceTraceRhs fp 1 s
  let N_hat := ch14ext_gjeSeqStages n V
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hpiv' : forall t : Nat, (ht : t < n - 1) ->
      V (1 + t) ⟨1 + t, hidx t ht⟩ ⟨1 + t, hidx t ht⟩ ≠ 0 := by
    intro t ht
    simpa [V] using hpiv t ht
  have hrec := ch14ext_gjeSourceTrace_recurrence_bounds_14_25b_14_26
    fp s hidx hUpper hpiv' h3
  have hrecM := hrec.1
  have hrecX := hrec.2
  have hsum : 1 + (n - 1) = n := by omega
  have hVfinal : V (1 + (n - 1)) = idMatrix n := by
    rw [hsum]
    simpa [V] using hfinal
  have hUx' : forall i : Fin n, matMulVec n (V 1) x i = xseq 1 i := by
    intro i
    simpa [V, xseq, ch14ext_gjeSourceTraceMatrix,
      ch14ext_gjeSourceTraceRhs, ch14ext_gjeSourceTrace] using hUx i
  have hforward := ch14ext_gje_stage2_forward_error_of_accumulation_14_29
    fp n N_hat V xseq x 1 hnpos h3 hidx hVfinal hUx' hrecM hrecX
  simpa [V, xseq, N_hat, hsum, ch14ext_gjeSourceTraceMatrix,
    ch14ext_gjeSourceTraceRhs, ch14ext_gjeSourceTrace] using hforward

end NumStability.Ch14Ext
