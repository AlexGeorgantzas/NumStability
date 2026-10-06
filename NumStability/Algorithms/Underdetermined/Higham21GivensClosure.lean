-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Actual rounded stored-Givens closure for the Givens branch of Theorem 21.4.

import NumStability.Algorithms.Underdetermined.Higham21GivensRounded

namespace NumStability

/-!
The earlier Givens endpoint deliberately exposed a stored-replay bridge because
the staged QR routine returns only its reduced panel.  This file reconstructs
the active rotation trace from the same concrete task schedule.  Each trace
entry retains the two panel entries from which its rounded coefficients were
computed.  Consequently the rounded transpose replay can be compared with the
same exact Givens product that explains the QR reduction, without assuming an
application certificate.
-/

/-- One active staged-QR rotation together with the source pair used by the
concrete rounded coefficient kernels. -/
structure Higham21ConcreteGivensReplayStep (n : Nat) where
  p : Fin n
  q : Fin n
  distinct : p ≠ q
  xi : Real
  xj : Real
  source_ne : xi ^ 2 + xj ^ 2 ≠ 0

namespace Higham21ConcreteGivensReplayStep

/-- Stored rounded coefficients emitted by one active QR task. -/
noncomputable def stored {n : Nat} (fp : FPModel)
    (g : Higham21ConcreteGivensReplayStep n) :
    Higham21StoredGivensRotation n :=
  { p := g.p
    q := g.q
    distinct := g.distinct
    c_hat := fl_givensC fp g.xi g.xj
    s_hat := fl_givensS fp g.xi g.xj }

/-- Exact transpose rotation paired with `stored`. -/
noncomputable def exactTranspose {n : Nat}
    (g : Higham21ConcreteGivensReplayStep n) :
    Fin n → Fin n → Real :=
  givensRotation n g.p g.q (givensC g.xi g.xj) (-givensS g.xi g.xj)

theorem exactTranspose_orthogonal {n : Nat}
    (g : Higham21ConcreteGivensReplayStep n) :
    IsOrthogonal n g.exactTranspose := by
  exact givensRotation_orthogonal n g.p g.q
    (givensC g.xi g.xj) (-givensS g.xi g.xj) g.distinct (by
      have h := givensCoeff_norm_sq g.xi g.xj g.source_ne
      nlinarith)

end Higham21ConcreteGivensReplayStep

/-- Exact transposed product represented by a concrete replay list. -/
noncomputable def higham21ConcreteGivensExactQ {n : Nat} :
    List (Higham21ConcreteGivensReplayStep n) → Fin n → Fin n → Real
  | [] => idMatrix n
  | g :: gs => matMul n g.exactTranspose (higham21ConcreteGivensExactQ gs)

/-- Existing stored-rotation trace obtained from the concrete source-bearing
trace. -/
noncomputable def higham21ConcreteGivensStoredTrace {n : Nat} (fp : FPModel)
    (steps : List (Higham21ConcreteGivensReplayStep n)) :
    List (Higham21StoredGivensRotation n) :=
  steps.map (Higham21ConcreteGivensReplayStep.stored fp)

@[simp] theorem higham21ConcreteGivensExactQ_nil (n : Nat) :
    higham21ConcreteGivensExactQ
      ([] : List (Higham21ConcreteGivensReplayStep n)) = idMatrix n := rfl

@[simp] theorem higham21ConcreteGivensExactQ_cons {n : Nat}
    (g : Higham21ConcreteGivensReplayStep n)
    (gs : List (Higham21ConcreteGivensReplayStep n)) :
    higham21ConcreteGivensExactQ (g :: gs) =
      matMul n g.exactTranspose (higham21ConcreteGivensExactQ gs) := rfl

theorem higham21ConcreteGivensExactQ_orthogonal {n : Nat}
    (steps : List (Higham21ConcreteGivensReplayStep n)) :
    IsOrthogonal n (higham21ConcreteGivensExactQ steps) := by
  induction steps with
  | nil => exact idMatrix_orthogonal n
  | cons g gs ih =>
      exact g.exactTranspose_orthogonal.mul ih

theorem higham21ConcreteGivensExactQ_append {n : Nat}
    (xs ys : List (Higham21ConcreteGivensReplayStep n)) :
    higham21ConcreteGivensExactQ (xs ++ ys) =
      matMul n (higham21ConcreteGivensExactQ xs)
        (higham21ConcreteGivensExactQ ys) := by
  induction xs with
  | nil => exact (matMul_id_left n (higham21ConcreteGivensExactQ ys)).symm
  | cons g gs ih =>
      simp only [List.cons_append, higham21ConcreteGivensExactQ_cons]
      rw [ih, matMul_assoc]

@[simp] theorem higham21ConcreteGivensStoredTrace_nil
    (fp : FPModel) (n : Nat) :
    higham21ConcreteGivensStoredTrace fp
      ([] : List (Higham21ConcreteGivensReplayStep n)) = [] := rfl

@[simp] theorem higham21ConcreteGivensStoredTrace_cons {n : Nat}
    (fp : FPModel) (g : Higham21ConcreteGivensReplayStep n)
    (gs : List (Higham21ConcreteGivensReplayStep n)) :
    higham21ConcreteGivensStoredTrace fp (g :: gs) =
      g.stored fp :: higham21ConcreteGivensStoredTrace fp gs := rfl

theorem higham21ConcreteGivensStoredTrace_append {n : Nat}
    (fp : FPModel)
    (xs ys : List (Higham21ConcreteGivensReplayStep n)) :
    higham21ConcreteGivensStoredTrace fp (xs ++ ys) =
      higham21ConcreteGivensStoredTrace fp xs ++
        higham21ConcreteGivensStoredTrace fp ys := by
  simp [higham21ConcreteGivensStoredTrace]

/-- Transposition changes only the sign of the sine coefficient in the local
Givens convention. -/
theorem matTranspose_givensRotation {n : Nat} (p q : Fin n)
    (c s : Real) (hpq : p ≠ q) :
    matTranspose (givensRotation n p q c s) =
      givensRotation n p q c (-s) := by
  ext i j
  simp only [matTranspose, givensRotation]
  by_cases hip : i = p <;> by_cases hiq : i = q <;>
    by_cases hjp : j = p <;> by_cases hjq : j = q <;>
    simp_all [eq_comm]

/-- The actual rounded transpose application of one retained active rotation
satisfies the concrete coefficient-plus-application contract. -/
theorem higham21_concrete_givens_transpose_app_error
    {n : Nat} (fp : FPModel) (g : Higham21ConcreteGivensReplayStep n)
    (x : Fin n → Real) (hvalid : gammaValid fp 8) :
    GivensAppError n g.exactTranspose x
      (Higham21StoredGivensRotation.applyTranspose fp (g.stored fp) x)
      (gamma fp 8 * Real.sqrt (n : Real)) := by
  have hvalid6 : gammaValid fp 6 := gammaValid_mono fp (by omega) hvalid
  have hcoeff0 :=
    fl_givensCoeffError_conservative fp g.xi g.xj g.source_ne hvalid6
  have hcoeff :
      GivensCoeffError (givensC g.xi g.xj) (-givensS g.xi g.xj)
        (fl_givensC fp g.xi g.xj) (-fl_givensS fp g.xi g.xj)
        (gamma fp 6) := by
    constructor
    · exact hcoeff0.c_rel
    · obtain ⟨theta, htheta, hs⟩ := hcoeff0.s_rel
      refine ⟨theta, htheta, ?_⟩
      rw [hs]
      ring
  have hcs :
      givensC g.xi g.xj ^ 2 + (-givensS g.xi g.xj) ^ 2 = 1 := by
    have h := givensCoeff_norm_sq g.xi g.xj g.source_ne
    nlinarith
  have happ :=
    fl_givensApply_coeffError_app_error fp n g.p g.q
      (givensC g.xi g.xj) (-givensS g.xi g.xj)
      (fl_givensC fp g.xi g.xj) (-fl_givensS fp g.xi g.xj)
      (gamma fp 6) x g.distinct hcs le_rfl hcoeff hvalid
  have hnorm : frobNorm g.exactTranspose = Real.sqrt (n : Real) :=
    g.exactTranspose_orthogonal.frobNorm_eq_sqrt_card
  rw [show frobNorm
      (givensRotation n g.p g.q (givensC g.xi g.xj) (-givensS g.xi g.xj)) =
        Real.sqrt (n : Real) by
      simpa [Higham21ConcreteGivensReplayStep.exactTranspose] using hnorm] at happ
  simpa [Higham21ConcreteGivensReplayStep.exactTranspose,
    Higham21ConcreteGivensReplayStep.stored,
    Higham21StoredGivensRotation.applyTranspose] using happ

/-- General square-matrix one-step rule for a rounded accumulated action with
a fixed exact reference.  It is the non-embedded analogue of the corresponding
Householder panel lemma. -/
theorem higham21_fixed_accumulation_prepend_closed
    {n : Nat}
    {Qtail Qtail_hat : Fin n → Fin n → Real} {etaTail : Real}
    (hTail : HouseholderQRPanelQhatFixedAccumError
      n Qtail Qtail_hat etaTail)
    (P Q_ref Q_hat : Fin n → Fin n → Real) (c : Real)
    (hP : IsOrthogonal n P) (hc : 0 ≤ c)
    (hQref : Q_ref = matMul n P Qtail)
    (hStep : ∃ E : Fin n → Fin n → Real,
      (∀ i j, Q_hat i j = matMul n P Qtail_hat i j + E i j) ∧
      frobNorm E ≤ c * frobNorm Qtail_hat) :
    HouseholderQRPanelQhatFixedAccumError n Q_ref Q_hat
      (etaTail + c * (Real.sqrt (n : Real) + etaTail)) := by
  obtain ⟨DeltaTail, hTailRep, hDeltaTail⟩ := hTail.result
  obtain ⟨E, hQhat, hE⟩ := hStep
  let DeltaQ : Fin n → Fin n → Real :=
    fun i j => matMul n P DeltaTail i j + E i j
  refine ⟨?_, ⟨DeltaQ, ?_, ?_⟩⟩
  · rw [hQref]
    exact hP.mul hTail.orth
  · intro i j
    have htail : Qtail_hat = fun a b => Qtail a b + DeltaTail a b := by
      ext a b
      exact hTailRep a b
    calc
      Q_hat i j = matMul n P Qtail_hat i j + E i j := hQhat i j
      _ = matMul n P (fun a b => Qtail a b + DeltaTail a b) i j + E i j := by
        rw [htail]
      _ = matMul n P Qtail i j + matMul n P DeltaTail i j + E i j := by
        rw [matMul_add_right]
      _ = Q_ref i j + DeltaQ i j := by
        rw [hQref]
        dsimp only [DeltaQ]
        ring
  · have htailNorm : frobNorm Qtail_hat ≤
        Real.sqrt (n : Real) + etaTail := by
      have hsum : frobNorm Qtail_hat ≤
          frobNorm Qtail + frobNorm DeltaTail := by
        rw [show Qtail_hat = fun i j => Qtail i j + DeltaTail i j from by
          ext i j
          exact hTailRep i j]
        exact frobNorm_add_le Qtail DeltaTail
      calc
        frobNorm Qtail_hat ≤ frobNorm Qtail + frobNorm DeltaTail := hsum
        _ = Real.sqrt (n : Real) + frobNorm DeltaTail := by
          rw [hTail.orth.frobNorm_eq_sqrt_card]
        _ ≤ Real.sqrt (n : Real) + etaTail := add_le_add_right hDeltaTail _
    have hDeltaQ : frobNorm DeltaQ ≤
        frobNorm (matMul n P DeltaTail) + frobNorm E := by
      exact frobNorm_add_le (matMul n P DeltaTail) E
    calc
      frobNorm DeltaQ ≤
          frobNorm (matMul n P DeltaTail) + frobNorm E := hDeltaQ
      _ = frobNorm DeltaTail + frobNorm E := by
        rw [frobNorm_orthogonal_left P DeltaTail hP]
      _ ≤ etaTail + c * frobNorm Qtail_hat := add_le_add hDeltaTail hE
      _ ≤ etaTail + c * (Real.sqrt (n : Real) + etaTail) :=
        add_le_add_right (mul_le_mul_of_nonneg_left htailNorm hc) _

theorem Higham21GivensStoredReplayBridge.mono
    {n : Nat} {fp : FPModel} {Q : Fin n → Fin n → Real}
    {trace : List (Higham21StoredGivensRotation n)} {eta eta' : Real}
    (h : Higham21GivensStoredReplayBridge fp n Q trace eta)
    (heta : eta ≤ eta') :
    Higham21GivensStoredReplayBridge fp n Q trace eta' := by
  intro z
  obtain ⟨Q_hat, hfixed, hreplay⟩ := h z
  exact ⟨Q_hat, hfixed.mono heta, hreplay⟩

/-- Closed fixed-reference accumulation bound for successive rounded Givens
applications.  Unlike a vector-only bound, the fixed-matrix witness carries the
Frobenius norm `sqrt n` of the exact accumulated factor. -/
noncomputable def higham21GivensReplayAccumBound (n : Nat) (c : Real) :
    Nat → Real
  | 0 => 0
  | r + 1 =>
      higham21GivensReplayAccumBound n c r +
        c * (Real.sqrt (n : Real) + higham21GivensReplayAccumBound n c r)

theorem higham21GivensReplayAccumBound_nonneg (n : Nat) {c : Real}
    (hc : 0 ≤ c) : ∀ r, 0 ≤ higham21GivensReplayAccumBound n c r := by
  intro r
  induction r with
  | zero => simp [higham21GivensReplayAccumBound]
  | succ r ih =>
      simp only [higham21GivensReplayAccumBound]
      exact add_nonneg ih (mul_nonneg hc (add_nonneg (Real.sqrt_nonneg _) ih))

theorem higham21GivensReplayAccumBound_le_succ (n : Nat) {c : Real}
    (hc : 0 ≤ c) (r : Nat) :
    higham21GivensReplayAccumBound n c r ≤
      higham21GivensReplayAccumBound n c (r + 1) := by
  simp only [higham21GivensReplayAccumBound]
  exact le_add_of_nonneg_right
    (mul_nonneg hc (add_nonneg (Real.sqrt_nonneg _)
      (higham21GivensReplayAccumBound_nonneg n hc r)))

theorem higham21GivensReplayAccumBound_mono_nat (n : Nat) {c : Real}
    (hc : 0 ≤ c) {r s : Nat} (hrs : r ≤ s) :
    higham21GivensReplayAccumBound n c r ≤
      higham21GivensReplayAccumBound n c s := by
  induction hrs with
  | refl => exact le_rfl
  | @step s _ ih =>
      exact ih.trans (higham21GivensReplayAccumBound_le_succ n hc s)

/-- The reconstructed concrete trace has an unconditional fixed-reference
rounded replay certificate. -/
theorem higham21_concrete_givens_stored_replay_bridge
    {n : Nat} (fp : FPModel)
    (steps : List (Higham21ConcreteGivensReplayStep n))
    (hvalid : gammaValid fp 8) :
    Higham21GivensStoredReplayBridge fp n
      (higham21ConcreteGivensExactQ steps)
      (higham21ConcreteGivensStoredTrace fp steps)
      (higham21GivensReplayAccumBound n
        (gamma fp 8 * Real.sqrt (n : Real)) steps.length) := by
  induction steps with
  | nil =>
      intro z
      refine ⟨idMatrix n, ?_, ?_⟩
      · refine ⟨idMatrix_orthogonal n, ?_⟩
        let Z : Fin n → Fin n → Real := fun _ _ => 0
        refine ⟨Z, ?_, ?_⟩
        · intro i j
          simp [Z]
        · rw [show frobNorm Z = 0 by
            rw [frobNorm_eq_zero_iff]
            intro i j
            rfl]
          simp [higham21GivensReplayAccumBound]
      · simp [higham21ConcreteGivensStoredTrace,
          higham21ApplyStoredGivensRotationsTranspose, matMulVec_id]
  | cons g gs ih =>
      intro z
      obtain ⟨Qtail_hat, hTail, hTailReplay⟩ := ih z
      let tailOut : Fin n → Real :=
        higham21ApplyStoredGivensRotationsTranspose fp n
          (higham21ConcreteGivensStoredTrace fp gs) z
      have happ := higham21_concrete_givens_transpose_app_error
        fp g tailOut hvalid
      obtain ⟨DeltaP, hDeltaP, hApply⟩ := happ.pert
      let P : Fin n → Fin n → Real := g.exactTranspose
      let Q_hat : Fin n → Fin n → Real :=
        matMul n (fun i j => P i j + DeltaP i j) Qtail_hat
      let E : Fin n → Fin n → Real := matMul n DeltaP Qtail_hat
      have hc : 0 ≤ gamma fp 8 * Real.sqrt (n : Real) :=
        mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
      have hStep : ∃ E : Fin n → Fin n → Real,
          (∀ i j, Q_hat i j = matMul n P Qtail_hat i j + E i j) ∧
          frobNorm E ≤
            (gamma fp 8 * Real.sqrt (n : Real)) * frobNorm Qtail_hat := by
        refine ⟨E, ?_, ?_⟩
        · intro i j
          simp only [Q_hat, E]
          rw [matMul_add_left]
        · calc
            frobNorm E ≤ frobNorm DeltaP * frobNorm Qtail_hat :=
              frobNorm_matMul_le DeltaP Qtail_hat
            _ ≤ (gamma fp 8 * Real.sqrt (n : Real)) *
                  frobNorm Qtail_hat :=
              mul_le_mul_of_nonneg_right hDeltaP (frobNorm_nonneg _)
      have hFixed : HouseholderQRPanelQhatFixedAccumError n
          (higham21ConcreteGivensExactQ (g :: gs)) Q_hat
          (higham21GivensReplayAccumBound n
              (gamma fp 8 * Real.sqrt (n : Real)) gs.length +
            (gamma fp 8 * Real.sqrt (n : Real)) *
              (Real.sqrt (n : Real) +
                higham21GivensReplayAccumBound n
                  (gamma fp 8 * Real.sqrt (n : Real)) gs.length)) := by
        exact higham21_fixed_accumulation_prepend_closed hTail P
          (higham21ConcreteGivensExactQ (g :: gs)) Q_hat
          (gamma fp 8 * Real.sqrt (n : Real)) g.exactTranspose_orthogonal hc
          rfl hStep
      refine ⟨Q_hat, ?_, ?_⟩
      · simpa [higham21GivensReplayAccumBound] using hFixed
      · ext i
        change Higham21StoredGivensRotation.applyTranspose fp (g.stored fp)
            tailOut i =
          matMulVec n Q_hat z i
        calc
          (g.stored fp).applyTranspose fp tailOut i =
              matMulVec n (fun a b => P a b + DeltaP a b) tailOut i :=
            hApply i
          _ = matMulVec n (fun a b => P a b + DeltaP a b)
                (matMulVec n Qtail_hat z) i := by
            rw [show tailOut = matMulVec n Qtail_hat z from by
              simpa [tailOut] using hTailReplay]
          _ = matMulVec n Q_hat z i := by
            symm
            exact matMulVec_matMul n
              (fun a b => P a b + DeltaP a b) Qtail_hat z i

/-! ## The same explicit product explains the staged QR reduction -/

/-- Prepend one orthogonal residual step to an explicit tail QR certificate.
The perturbation is transported back through the exact first rotation. -/
theorem higham21_prepend_columnwise_qr_certificate
    {m p : Nat}
    (B B1 Bfinal : Fin m → Fin p → Real)
    (P Qtail : Fin m → Fin m → Real)
    (E dTail : Fin m → Fin p → Real)
    (hP : IsOrthogonal m P) (hQtail : IsOrthogonal m Qtail)
    (hB1 : B1 = fun i j => matMulRect m m p P B i j + E i j)
    (hTail : Bfinal =
      matMulRect m m p (matTranspose Qtail)
        (fun i j => B1 i j + dTail i j)) :
    let Q := matMul m (matTranspose P) Qtail
    let dA := matMulRect m m p (matTranspose P)
      (fun i j => E i j + dTail i j)
    IsOrthogonal m Q ∧
      Bfinal = matMulRect m m p (matTranspose Q)
        (fun i j => B i j + dA i j) ∧
      ∀ j, columnFrob dA j ≤ columnFrob E j + columnFrob dTail j := by
  dsimp only
  let Q : Fin m → Fin m → Real := matMul m (matTranspose P) Qtail
  let S : Fin m → Fin p → Real := fun i j => E i j + dTail i j
  let dA : Fin m → Fin p → Real :=
    matMulRect m m p (matTranspose P) S
  have hQ : IsOrthogonal m Q := hP.transpose.mul hQtail
  have hQT : matTranspose Q = matMul m (matTranspose Qtail) P := by
    simp [Q, matTranspose_matMul, matTranspose_involutive]
  have hPPt : matMul m P (matTranspose P) = idMatrix m := by
    ext i j
    exact hP.right_inv i j
  have hPd : matMulRect m m p P dA = S := by
    simp only [dA]
    rw [← matMulRect_assoc_square_left, hPPt, matMulRect_id_left]
  have hPBd : matMulRect m m p P (fun i j => B i j + dA i j) =
      fun i j => B1 i j + dTail i j := by
    rw [matMulRect_add_right, hPd, hB1]
    ext i j
    simp only [S]
    ring
  have hrepr : Bfinal = matMulRect m m p (matTranspose Q)
      (fun i j => B i j + dA i j) := by
    rw [hTail, hQT, matMulRect_assoc_square_left, hPBd]
  refine ⟨hQ, hrepr, ?_⟩
  intro j
  have hdcol : columnFrob dA j = columnFrob S j := by
    exact columnFrob_orthogonal_left (matTranspose P) S hP.transpose j
  rw [hdcol]
  simpa [S] using columnFrob_add_le E dTail j

set_option maxHeartbeats 800000 in
/-- A finite same-stage task list supplies an explicit exact product and the
matching list of active rounded replay steps.  Inactive zero-target tasks are
skipped by both products. -/
theorem higham21_givens_task_list_explicit_certificate
    (fp : FPModel) (m cols s : Nat)
    (tasks : List (GivensQRTask m cols))
    (B : Fin m → Fin cols → Real)
    (hstage : ∀ t ∈ tasks, t.stage = s)
    (hzero : ZeroedThrough s B)
    (hvalid : gammaValid fp 8) :
    ∃ (steps : List (Higham21ConcreteGivensReplayStep m))
        (dA : Fin m → Fin cols → Real),
      IsOrthogonal m (higham21ConcreteGivensExactQ steps) ∧
      fl_givensQRTaskList fp m cols tasks B =
        matMulRect m m cols
          (matTranspose (higham21ConcreteGivensExactQ steps))
          (fun i j => B i j + dA i j) ∧
      (∀ j, columnFrob dA j ≤
        residualAccumBound (gamma fp 8 * Real.sqrt (m : Real)) tasks.length *
          columnFrob B j) ∧
      steps.length ≤ tasks.length := by
  induction tasks generalizing B with
  | nil =>
      let Z : Fin m → Fin cols → Real := fun _ _ => 0
      refine ⟨[], Z, idMatrix_orthogonal m, ?_, ?_, ?_⟩
      · simp [fl_givensQRTaskList, Z, higham21ConcreteGivensExactQ,
          matTranspose_id, matMulRect_id_left]
      · intro j
        have hZ : columnFrob Z j = 0 := by
          rw [columnFrob, frobNorm_eq_zero_iff]
          intro i u
          rfl
        simp [Z, hZ, residualAccumBound]
      · simp
  | cons t ts ih =>
      have htstage : t.stage = s := hstage t (by simp)
      have htailStage : ∀ u ∈ ts, u.stage = s := by
        intro u hu
        exact hstage u (by simp [hu])
      let B1 : Fin m → Fin cols → Real :=
        fl_givensQRTaskStepOfTask fp m cols t B
      have hzero_t : ZeroedThrough t.stage B := by simpa [htstage] using hzero
      have hzero1 : ZeroedThrough s B1 := by
        simpa [B1, htstage] using
          fl_givensQRTaskStepOfTask_preserves_zeroedThrough_stage
            fp m cols t B hzero_t
      obtain ⟨tailSteps, dTail, hQtail, hTailRep, hTailBound,
          hTailLen⟩ := ih B1 htailStage hzero1
      let P : Fin m → Fin m → Real := givensQRTaskRotation m cols t B
      have hP : IsOrthogonal m P := givensQRTaskRotation_orthogonal m cols t B
      obtain ⟨E, hStepRep, hEBound, _hrows⟩ :=
        fl_givensQRTaskStepOfTask_columnFrob_uniform_of_zeroedThrough
          fp m cols t B hzero_t hvalid
      have hB1 : B1 = fun i j => matMulRect m m cols P B i j + E i j := by
        ext i j
        exact hStepRep i j
      have hTailRep' : fl_givensQRTaskList fp m cols ts B1 =
          matMulRect m m cols
            (matTranspose (higham21ConcreteGivensExactQ tailSteps))
            (fun i j => B1 i j + dTail i j) := hTailRep
      have hpre := higham21_prepend_columnwise_qr_certificate
        B B1 (fl_givensQRTaskList fp m cols ts B1) P
        (higham21ConcreteGivensExactQ tailSteps) E dTail hP hQtail hB1
        hTailRep'
      dsimp only at hpre
      obtain ⟨hQpre, hRepPre, hColPre⟩ := hpre
      let dPre : Fin m → Fin cols → Real :=
        matMulRect m m cols (matTranspose P)
          (fun i j => E i j + dTail i j)
      have hc : 0 ≤ gamma fp 8 * Real.sqrt (m : Real) :=
        mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
      let alpha : Real :=
        residualAccumBound (gamma fp 8 * Real.sqrt (m : Real)) ts.length
      have halpha : 0 ≤ alpha := residualAccumBound_nonneg _ hc _
      have hB1col : ∀ j, columnFrob B1 j ≤
          (1 + gamma fp 8 * Real.sqrt (m : Real)) * columnFrob B j := by
        intro j
        have hPB : columnFrob (matMulRect m m cols P B) j = columnFrob B j :=
          columnFrob_orthogonal_left P B hP j
        calc
          columnFrob B1 j =
              columnFrob (fun i q => matMulRect m m cols P B i q + E i q) j := by
                rw [hB1]
          _ ≤ columnFrob (matMulRect m m cols P B) j + columnFrob E j :=
            columnFrob_add_le (matMulRect m m cols P B) E j
          _ = columnFrob B j + columnFrob E j := by rw [hPB]
          _ ≤ columnFrob B j +
                (gamma fp 8 * Real.sqrt (m : Real)) * columnFrob B j :=
            add_le_add_right (hEBound j) (columnFrob B j)
          _ = (1 + gamma fp 8 * Real.sqrt (m : Real)) * columnFrob B j := by
            ring
      have hPreBound : ∀ j, columnFrob dPre j ≤
          residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
              (t :: ts).length * columnFrob B j := by
        intro j
        have hdt : columnFrob dTail j ≤
            alpha * ((1 + gamma fp 8 * Real.sqrt (m : Real)) *
              columnFrob B j) := by
          exact (hTailBound j).trans
            (mul_le_mul_of_nonneg_left (hB1col j) halpha)
        calc
          columnFrob dPre j ≤ columnFrob E j + columnFrob dTail j :=
            hColPre j
          _ ≤ (gamma fp 8 * Real.sqrt (m : Real)) * columnFrob B j +
                alpha * ((1 + gamma fp 8 * Real.sqrt (m : Real)) *
                  columnFrob B j) := add_le_add (hEBound j) hdt
          _ = residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
                (t :: ts).length * columnFrob B j := by
            simp only [List.length_cons, residualAccumBound, alpha]
            ring
      by_cases hactive : B t.row t.col = 0
      · have hPId : P = idMatrix m := by
          simp [P, givensQRTaskRotation, hactive]
        have hQeq : matMul m (matTranspose P)
              (higham21ConcreteGivensExactQ tailSteps) =
            higham21ConcreteGivensExactQ tailSteps := by
          rw [hPId, matTranspose_id, matMul_id_left]
        refine ⟨tailSteps, dPre, hQtail, ?_, hPreBound, ?_⟩
        · simpa [fl_givensQRTaskList, B1, dPre, hQeq] using hRepPre
        · exact hTailLen.trans (Nat.le_succ ts.length)
      · have hsource : B t.pivot t.col ^ 2 + B t.row t.col ^ 2 ≠ 0 := by
          intro hsum
          have hrowSq : B t.row t.col ^ 2 = 0 := by
            nlinarith [sq_nonneg (B t.pivot t.col), sq_nonneg (B t.row t.col)]
          exact hactive (sq_eq_zero_iff.mp hrowSq)
        let g : Higham21ConcreteGivensReplayStep m :=
          { p := t.pivot
            q := t.row
            distinct := t.pivot_ne_row
            xi := B t.pivot t.col
            xj := B t.row t.col
            source_ne := hsource }
        have hPt : matTranspose P = g.exactTranspose := by
          simp only [P, givensQRTaskRotation, hactive, if_false]
          exact matTranspose_givensRotation t.pivot t.row
            (givensC (B t.pivot t.col) (B t.row t.col))
            (givensS (B t.pivot t.col) (B t.row t.col)) t.pivot_ne_row
        have hQeq : matMul m (matTranspose P)
              (higham21ConcreteGivensExactQ tailSteps) =
            higham21ConcreteGivensExactQ (g :: tailSteps) := by
          rw [hPt]
          rfl
        refine ⟨g :: tailSteps, dPre, ?_, ?_, hPreBound, ?_⟩
        · simpa [← hQeq] using hQpre
        · simpa [fl_givensQRTaskList, B1, dPre, ← hQeq] using hRepPre
        · simpa using Nat.succ_le_succ hTailLen

/-- Compose two explicit columnwise QR certificates in execution order.  The
second perturbation is transported through the first exact factor, so its
column norm is unchanged. -/
theorem higham21_append_columnwise_qr_certificate
    {m p : Nat}
    (B Bmid Bfinal : Fin m → Fin p → Real)
    (Qprev Qlocal : Fin m → Fin m → Real)
    (dPrev dLocal : Fin m → Fin p → Real)
    (hQprev : IsOrthogonal m Qprev)
    (hQlocal : IsOrthogonal m Qlocal)
    (hPrev : Bmid = matMulRect m m p (matTranspose Qprev)
      (fun i j => B i j + dPrev i j))
    (hLocal : Bfinal = matMulRect m m p (matTranspose Qlocal)
      (fun i j => Bmid i j + dLocal i j)) :
    let Q := matMul m Qprev Qlocal
    let dA := fun i j => dPrev i j +
      matMulRect m m p Qprev dLocal i j
    IsOrthogonal m Q ∧
      Bfinal = matMulRect m m p (matTranspose Q)
        (fun i j => B i j + dA i j) ∧
      ∀ j, columnFrob dA j ≤
        columnFrob dPrev j + columnFrob dLocal j := by
  dsimp only
  let dLift : Fin m → Fin p → Real :=
    matMulRect m m p Qprev dLocal
  let dA : Fin m → Fin p → Real := fun i j => dPrev i j + dLift i j
  have hQ : IsOrthogonal m (matMul m Qprev Qlocal) :=
    hQprev.mul hQlocal
  have hQtQ : matMul m (matTranspose Qprev) Qprev = idMatrix m := by
    ext i j
    exact hQprev.left_inv i j
  have hCancel :
      matMulRect m m p (matTranspose Qprev) dLift = dLocal := by
    simp only [dLift]
    rw [← matMulRect_assoc_square_left, hQtQ, matMulRect_id_left]
  have hInside :
      matMulRect m m p (matTranspose Qprev)
          (fun i j => B i j + dA i j) =
        fun i j => Bmid i j + dLocal i j := by
    ext i j
    calc
      matMulRect m m p (matTranspose Qprev)
          (fun a b => B a b + dA a b) i j =
          matMulRect m m p (matTranspose Qprev)
            (fun a b => (B a b + dPrev a b) + dLift a b) i j := by
              congr 2
              ext a b
              simp only [dA]
              ring
      _ = matMulRect m m p (matTranspose Qprev)
            (fun a b => B a b + dPrev a b) i j +
          matMulRect m m p (matTranspose Qprev) dLift i j := by
            rw [matMulRect_add_right]
      _ = Bmid i j + dLocal i j := by
            rw [← hPrev, hCancel]
  have hQT : matTranspose (matMul m Qprev Qlocal) =
      matMul m (matTranspose Qlocal) (matTranspose Qprev) := by
    exact matTranspose_matMul Qprev Qlocal
  refine ⟨hQ, ?_, ?_⟩
  · rw [hLocal, hQT, matMulRect_assoc_square_left, hInside]
  · intro j
    have hLiftCol : columnFrob dLift j = columnFrob dLocal j := by
      exact columnFrob_orthogonal_left Qprev dLocal hQprev j
    calc
      columnFrob dA j ≤ columnFrob dPrev j + columnFrob dLift j := by
        simpa [dA] using columnFrob_add_le dPrev dLift j
      _ = columnFrob dPrev j + columnFrob dLocal j := by rw [hLiftCol]

set_option maxHeartbeats 1600000 in
/-- The full staged QR fold carries an explicit source-bearing active trace.
Its exact product is the orthogonal witness in the same conservative
columnwise backward-error bound used by Theorem 19.10. -/
theorem higham21_givens_stage_fold_explicit_certificate
    (fp : FPModel) (m cols : Nat)
    (B : Fin m → Fin cols → Real) (k : Nat)
    (hvalid : gammaValid fp 8) :
    ∃ (steps : List (Higham21ConcreteGivensReplayStep m))
        (dA : Fin m → Fin cols → Real),
      IsOrthogonal m (higham21ConcreteGivensExactQ steps) ∧
      fl_givensQRStageFold fp m cols k B =
        matMulRect m m cols
          (matTranspose (higham21ConcreteGivensExactQ steps))
          (fun i j => B i j + dA i j) ∧
      (∀ j, columnFrob dA j ≤
        residualAccumBound
          (residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
            (givensQRStageTaskList m cols k).length) k *
          columnFrob B j) ∧
      steps.length ≤ (givensQRStageTaskList m cols k).length := by
  induction k with
  | zero =>
      let Z : Fin m → Fin cols → Real := fun _ _ => 0
      refine ⟨[], Z, idMatrix_orthogonal m, ?_, ?_, ?_⟩
      · simp [fl_givensQRStageFold, higham21ConcreteGivensExactQ,
          matTranspose_id, matMulRect_id_left, Z]
      · intro j
        have hZ : columnFrob Z j = 0 := by
          rw [columnFrob, frobNorm_eq_zero_iff]
          intro i u
          rfl
        simp [Z, hZ, residualAccumBound]
      · simp [givensQRStageTaskList]
  | succ s ih =>
      obtain ⟨prevSteps, dPrev, hQprev, hPrev, hPrevBound,
          hPrevLen⟩ := ih
      let Bmid : Fin m → Fin cols → Real :=
        fl_givensQRStageFold fp m cols s B
      have hzero : ZeroedThrough s Bmid := by
        simpa [Bmid] using
          fl_givensQRStageFold_zeroedThrough fp m cols B s
      have hstage : ∀ t ∈ givensQRStageTasks m cols s, t.stage = s := by
        intro t ht
        exact givensQRStageTasks_stage t ht
      obtain ⟨localSteps, dLocal, hQlocal, hLocal, hLocalBound,
          hLocalLen⟩ :=
        higham21_givens_task_list_explicit_certificate fp m cols s
          (givensQRStageTasks m cols s) Bmid hstage hzero hvalid
      let Qprev : Fin m → Fin m → Real :=
        higham21ConcreteGivensExactQ prevSteps
      let Qlocal : Fin m → Fin m → Real :=
        higham21ConcreteGivensExactQ localSteps
      let dA : Fin m → Fin cols → Real := fun i j =>
        dPrev i j + matMulRect m m cols Qprev dLocal i j
      have hPrev' : Bmid = matMulRect m m cols (matTranspose Qprev)
          (fun i j => B i j + dPrev i j) := by
        simpa [Bmid, Qprev] using hPrev
      have hLocal' : fl_givensQRStageFold fp m cols (s + 1) B =
          matMulRect m m cols (matTranspose Qlocal)
            (fun i j => Bmid i j + dLocal i j) := by
        simpa [fl_givensQRStageFold, Bmid, Qlocal] using hLocal
      have hComp := higham21_append_columnwise_qr_certificate
        B Bmid (fl_givensQRStageFold fp m cols (s + 1) B)
        Qprev Qlocal dPrev dLocal hQprev hQlocal hPrev' hLocal'
      dsimp only at hComp
      have hQappend : higham21ConcreteGivensExactQ
            (prevSteps ++ localSteps) = matMul m Qprev Qlocal := by
        simpa [Qprev, Qlocal] using
          higham21ConcreteGivensExactQ_append prevSteps localSteps
      have hbase : 0 ≤ gamma fp 8 * Real.sqrt (m : Real) :=
        mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
      let oldBudget : Real :=
        residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
          (givensQRStageTaskList m cols s).length
      let newBudget : Real :=
        residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
          (givensQRStageTaskList m cols (s + 1)).length
      let alpha : Real := residualAccumBound newBudget s
      have holdBudget : 0 ≤ oldBudget :=
        residualAccumBound_nonneg _ hbase _
      have hnewBudget : 0 ≤ newBudget :=
        residualAccumBound_nonneg _ hbase _
      have hFlatLen : (givensQRStageTaskList m cols s).length ≤
          (givensQRStageTaskList m cols (s + 1)).length := by
        simp only [givensQRStageTaskList, List.length_append]
        omega
      have hBudgetMono : oldBudget ≤ newBudget := by
        exact residualAccumBound_le_of_le_nat _ hbase hFlatLen
      have hOldAlpha : residualAccumBound oldBudget s ≤ alpha := by
        exact residualAccumBound_mono holdBudget hBudgetMono s
      have halpha : 0 ≤ alpha :=
        residualAccumBound_nonneg newBudget hnewBudget s
      have hPrevBound' : ∀ j, columnFrob dPrev j ≤
          alpha * columnFrob B j := by
        intro j
        exact (hPrevBound j).trans
          (mul_le_mul_of_nonneg_right hOldAlpha (columnFrob_nonneg B j))
      have hBmidCol : ∀ j, columnFrob Bmid j ≤
          (1 + alpha) * columnFrob B j := by
        intro j
        calc
          columnFrob Bmid j = columnFrob
              (matMulRect m m cols (matTranspose Qprev)
                (fun i q => B i q + dPrev i q)) j := by rw [hPrev']
          _ = columnFrob (fun i q => B i q + dPrev i q) j :=
            columnFrob_orthogonal_left (matTranspose Qprev)
              (fun i q => B i q + dPrev i q) hQprev.transpose j
          _ ≤ columnFrob B j + columnFrob dPrev j :=
            columnFrob_add_le B dPrev j
          _ ≤ columnFrob B j + alpha * columnFrob B j :=
            add_le_add_right (hPrevBound' j) (columnFrob B j)
          _ = (1 + alpha) * columnFrob B j := by ring
      have hStageLen : (givensQRStageTasks m cols s).length ≤
          (givensQRStageTaskList m cols (s + 1)).length := by
        simp only [givensQRStageTaskList, List.length_append]
        omega
      have hLocalBudget :
          residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
              (givensQRStageTasks m cols s).length ≤ newBudget := by
        exact residualAccumBound_le_of_le_nat _ hbase hStageLen
      have hLocalBound' : ∀ j, columnFrob dLocal j ≤
          newBudget * ((1 + alpha) * columnFrob B j) := by
        intro j
        exact (hLocalBound j).trans
          ((mul_le_mul_of_nonneg_right hLocalBudget
              (columnFrob_nonneg Bmid j)).trans
            (mul_le_mul_of_nonneg_left (hBmidCol j) hnewBudget))
      refine ⟨prevSteps ++ localSteps, dA, ?_, ?_, ?_, ?_⟩
      · rw [hQappend]
        exact hComp.1
      · simpa [dA, hQappend] using hComp.2.1
      · intro j
        calc
          columnFrob dA j ≤
              columnFrob dPrev j + columnFrob dLocal j := by
                simpa [dA, Qprev] using hComp.2.2 j
          _ ≤ alpha * columnFrob B j +
                newBudget * ((1 + alpha) * columnFrob B j) :=
            add_le_add (hPrevBound' j) (hLocalBound' j)
          _ = residualAccumBound newBudget (s + 1) *
                columnFrob B j := by
            simp only [residualAccumBound, alpha]
            ring
          _ = residualAccumBound
                (residualAccumBound
                  (gamma fp 8 * Real.sqrt (m : Real))
                  (givensQRStageTaskList m cols (s + 1)).length)
                (s + 1) * columnFrob B j := by rfl
      · simp only [List.length_append, givensQRStageTaskList,
          List.length_append]
        omega

/-! ## A shared concrete QR/replay factor for the Chapter 21 endpoint -/

/-- Active source-bearing trace selected from the constructive staged-fold
certificate for `Aᵀ`. -/
noncomputable def higham21GivensActualConcreteSteps
    (fp : FPModel) (m k : Nat)
    (A : Fin m → Fin (m + k) → Real)
    (hvalid : gammaValid fp 8) :
    List (Higham21ConcreteGivensReplayStep (m + k)) :=
  Classical.choose
    (higham21_givens_stage_fold_explicit_certificate
      fp (m + k) m (finiteTranspose A)
      (givensQRStageCount (m + k) m) hvalid)

/-- Perturbation paired with `higham21GivensActualConcreteSteps`. -/
noncomputable def higham21GivensActualDeltaAT
    (fp : FPModel) (m k : Nat)
    (A : Fin m → Fin (m + k) → Real)
    (hvalid : gammaValid fp 8) :
    Fin (m + k) → Fin m → Real :=
  Classical.choose (Classical.choose_spec
    (higham21_givens_stage_fold_explicit_certificate
      fp (m + k) m (finiteTranspose A)
      (givensQRStageCount (m + k) m) hvalid))

/-- All facts retained by the selected concrete trace and perturbation. -/
theorem higham21GivensActualConcreteSteps_spec
    (fp : FPModel) (m k : Nat)
    (A : Fin m → Fin (m + k) → Real)
    (hvalid : gammaValid fp 8) :
    IsOrthogonal (m + k)
        (higham21ConcreteGivensExactQ
          (higham21GivensActualConcreteSteps fp m k A hvalid)) ∧
      higham21GivensQMethodRTall fp m k A =
        matMulRect (m + k) (m + k) m
          (matTranspose (higham21ConcreteGivensExactQ
            (higham21GivensActualConcreteSteps fp m k A hvalid)))
          (fun i j => finiteTranspose A i j +
            higham21GivensActualDeltaAT fp m k A hvalid i j) ∧
      (∀ j, columnFrob
          (higham21GivensActualDeltaAT fp m k A hvalid) j ≤
        H19.Theorem19_10.gamma_tilde fp (m + k) m *
          columnFrob (finiteTranspose A) j) ∧
      (higham21GivensActualConcreteSteps fp m k A hvalid).length ≤
        (givensQRStageTaskList (m + k) m
          (givensQRStageCount (m + k) m)).length := by
  simpa [higham21GivensActualConcreteSteps,
      higham21GivensActualDeltaAT, higham21GivensQMethodRTall,
      H19.Theorem19_10.gamma_tilde] using
    (Classical.choose_spec (Classical.choose_spec
      (higham21_givens_stage_fold_explicit_certificate
        fp (m + k) m (finiteTranspose A)
        (givensQRStageCount (m + k) m) hvalid)))

/-- The exact product encoded by the actual retained trace is a valid
Chapter-19-style QR factor for the concrete staged result. -/
theorem higham21_givens_actual_qr_transpose_certificate
    (fp : FPModel) (m k : Nat)
    (A : Fin m → Fin (m + k) → Real)
    (hvalid : gammaValid fp 8) :
    H19.Theorem19_4.HouseholderQRBackwardError (m + k) m
      (finiteTranspose A)
      (higham21ConcreteGivensExactQ
        (higham21GivensActualConcreteSteps fp m k A hvalid))
      (higham21GivensQMethodRTall fp m k A)
      (H19.Theorem19_10.gamma_tilde fp (m + k) m) := by
  let steps := higham21GivensActualConcreteSteps fp m k A hvalid
  let Q := higham21ConcreteGivensExactQ steps
  let dA := higham21GivensActualDeltaAT fp m k A hvalid
  have hspec := higham21GivensActualConcreteSteps_spec fp m k A hvalid
  have hQ : IsOrthogonal (m + k) Q := by simpa [Q, steps] using hspec.1
  have hrepr : higham21GivensQMethodRTall fp m k A =
      matMulRect (m + k) (m + k) m (matTranspose Q)
        (fun i j => finiteTranspose A i j + dA i j) := by
    simpa [Q, steps, dA] using hspec.2.1
  have hbound : ∀ j, columnFrob dA j ≤
      H19.Theorem19_10.gamma_tilde fp (m + k) m *
        columnFrob (finiteTranspose A) j := by
    simpa [dA] using hspec.2.2.1
  refine
    { upper := fl_givensQRStageFold_upper_trapezoidal
        fp (m + k) m (finiteTranspose A)
      orth := hQ
      result := ?_ }
  refine ⟨dA, ?_, hbound⟩
  have hQQT : matMul (m + k) Q (matTranspose Q) = idMatrix (m + k) := by
    ext i j
    exact hQ.right_inv i j
  intro i j
  calc
    finiteTranspose A i j + dA i j =
        matMulRect (m + k) (m + k) m (idMatrix (m + k))
          (fun a b => finiteTranspose A a b + dA a b) i j := by
            rw [matMulRect_id_left]
    _ = matMulRect (m + k) (m + k) m
          (matMul (m + k) Q (matTranspose Q))
          (fun a b => finiteTranspose A a b + dA a b) i j := by
            rw [hQQT]
    _ = matMulRect (m + k) (m + k) m Q
          (matMulRect (m + k) (m + k) m (matTranspose Q)
            (fun a b => finiteTranspose A a b + dA a b)) i j := by
            rw [matMulRect_assoc_square_left]
    _ = matMulRect (m + k) (m + k) m Q
          (higham21GivensQMethodRTall fp m k A) i j := by
            rw [← hrepr]

/-- Stored coefficient trace emitted by the same selected active task trace. -/
noncomputable def higham21GivensActualStoredTrace
    (fp : FPModel) (m k : Nat)
    (A : Fin m → Fin (m + k) → Real)
    (hvalid : gammaValid fp 8) :
    List (Higham21StoredGivensRotation (m + k)) :=
  higham21ConcreteGivensStoredTrace fp
    (higham21GivensActualConcreteSteps fp m k A hvalid)

/-- Schedule-level fixed-accumulation radius for actual rounded transpose
replay.  The active trace may be shorter because zero-target tasks are
skipped. -/
noncomputable def Higham21GivensActualReplayEtaQ
    (fp : FPModel) (m k : Nat) : Real :=
  higham21GivensReplayAccumBound (m + k)
    (gamma fp 8 * Real.sqrt ((m + k : Nat) : Real))
    (givensQRStageTaskList (m + k) m
      (givensQRStageCount (m + k) m)).length

/-- Actual rounded operations close the replay bridge for the exact factor
that also explains the staged QR panel. -/
theorem higham21_givens_actual_stored_replay_bridge
    (fp : FPModel) (m k : Nat)
    (A : Fin m → Fin (m + k) → Real)
    (hvalid : gammaValid fp 8) :
    Higham21GivensStoredReplayBridge fp (m + k)
      (higham21ConcreteGivensExactQ
        (higham21GivensActualConcreteSteps fp m k A hvalid))
      (higham21GivensActualStoredTrace fp m k A hvalid)
      (Higham21GivensActualReplayEtaQ fp m k) := by
  have hraw := higham21_concrete_givens_stored_replay_bridge fp
    (higham21GivensActualConcreteSteps fp m k A hvalid) hvalid
  apply hraw.mono
  have hc : 0 ≤ gamma fp 8 * Real.sqrt ((m + k : Nat) : Real) :=
    mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  exact higham21GivensReplayAccumBound_mono_nat (m + k) hc
    (higham21GivensActualConcreteSteps_spec fp m k A hvalid).2.2.2

/-- Per-input certificate produced from the proved global bridge, rather than
supplied as a hypothesis. -/
noncomputable def higham21GivensActualApplicationCertificate
    (fp : FPModel) (m k : Nat)
    (A : Fin m → Fin (m + k) → Real) (b : Fin m → Real)
    (hvalid : gammaValid fp 8) :
    Higham21GivensFixedAccumulationCertificate fp (m + k)
      (higham21ConcreteGivensExactQ
        (higham21GivensActualConcreteSteps fp m k A hvalid))
      (higham21GivensActualStoredTrace fp m k A hvalid)
      (Fin.append (higham21GivensRoundedY1 fp m k A b)
        (0 : Fin k → Real))
      (Higham21GivensActualReplayEtaQ fp m k) := by
  let hex := higham21_givens_actual_stored_replay_bridge fp m k A hvalid
    (Fin.append (higham21GivensRoundedY1 fp m k A b)
      (0 : Fin k → Real))
  let Q_hat := Classical.choose hex
  have hspec := Classical.choose_spec hex
  exact { Q_hat := Q_hat, fixed := hspec.1, replay_eq := hspec.2 }

/-- Fully specified rounded Q-method output: the triangular solve is followed
by replay of the coefficients retained from the actual staged Givens sweep. -/
noncomputable def higham21GivensActualRoundedOutput
    (fp : FPModel) (m k : Nat)
    (A : Fin m → Fin (m + k) → Real) (b : Fin m → Real)
    (hvalid : gammaValid fp 8) : Fin (m + k) → Real :=
  higham21GivensStoredRoundedOutput fp m k A b
    (higham21GivensActualStoredTrace fp m k A hvalid)

/-- Rowwise coefficient for the closed actual-rounded Givens branch. -/
noncomputable def Higham21GivensActualRoundedRowwiseCoefficient
    (fp : FPModel) (m k : Nat) : Real :=
  Higham21FixedAccumulationRoundedRowwiseCoefficient fp m
    (H19.Theorem19_10.gamma_tilde fp (m + k) m)
    (Higham21GivensActualReplayEtaQ fp m k)

/-- Equation (21.10) action bound for the actual retained trace. -/
theorem higham21_givens_actual_rounded_action_error
    (fp : FPModel) (m k : Nat)
    (A : Fin m → Fin (m + k) → Real) (b : Fin m → Real)
    (hvalid : gammaValid fp 8) :
    vecNorm2 (fun i : Fin (m + k) =>
      higham21GivensActualRoundedOutput fp m k A b hvalid i -
        matMulVec (m + k)
          (higham21ConcreteGivensExactQ
            (higham21GivensActualConcreteSteps fp m k A hvalid))
          (Fin.append (higham21GivensRoundedY1 fp m k A b)
            (0 : Fin k → Real)) i) ≤
      Higham21GivensActualReplayEtaQ fp m k *
        vecNorm2 (higham21GivensRoundedY1 fp m k A b) := by
  let happ := higham21GivensActualApplicationCertificate
    fp m k A b hvalid
  have hx : higham21GivensActualRoundedOutput fp m k A b hvalid =
      matMulVec (m + k) happ.Q_hat
        (Fin.append (higham21GivensRoundedY1 fp m k A b)
          (0 : Fin k → Real)) := by
    simpa [higham21GivensActualRoundedOutput,
      higham21GivensStoredRoundedOutput] using happ.replay_eq
  simpa [hx] using
    (higham21_eq21_10_q_action_vec_error_bound_of_fixed_q_accum_error
      (higham21ConcreteGivensExactQ
        (higham21GivensActualConcreteSteps fp m k A hvalid))
      happ.Q_hat (higham21GivensRoundedY1 fp m k A b)
      (higham21GivensActualRoundedOutput fp m k A b hvalid)
      (Higham21GivensActualReplayEtaQ fp m k) happ.fixed hx)

/-- Higham, Chapter 21, Theorem 21.4 for the closed actual-rounded Givens
branch.  No replay/application certificate and no target-equivalence bridge
is assumed: both the QR factor and the final action come from the same
source-bearing concrete task trace. -/
theorem higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable
    {m k : Nat} (fp : FPModel)
    (A : Fin m → Fin (m + k) → Real) (b : Fin m → Real)
    (_hm : 0 < m)
    (hvalid : gammaValid fp 8)
    (hdiag : ∀ i : Fin m,
      ¬ higham21GivensRoundedRTop fp m k A i i = 0)
    (hvalidTri : gammaValid fp m)
    (hgram : ¬ Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0)
    (hQsmall : Higham21GivensActualReplayEtaQ fp m k < 1)
    (hCondSmall :
      3 *
        (Higham21GivensActualRoundedRowwiseCoefficient fp m k *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (higham21GivensActualRoundedOutput fp m k A b hvalid)
      (Real.sqrt 2 *
        Higham21GivensActualRoundedRowwiseCoefficient fp m k) := by
  let happ := higham21GivensActualApplicationCertificate
    fp m k A b hvalid
  have hqr := higham21_givens_actual_qr_transpose_certificate
    fp m k A hvalid
  have hdiag' : ∀ i : Fin m,
      ¬ higham21GivensQMethodRTall fp m k A (Fin.castAdd k i) i = 0 := by
    simpa [higham21GivensRoundedRTop] using hdiag
  have hx : higham21GivensActualRoundedOutput fp m k A b hvalid =
      matMulVec (m + k) happ.Q_hat
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose (fun i j =>
              higham21GivensQMethodRTall fp m k A
                (Fin.castAdd k i) j)) b)
          (0 : Fin k → Real)) := by
    simpa [higham21GivensActualRoundedOutput,
      higham21GivensStoredRoundedOutput, higham21GivensRoundedY1,
      higham21GivensRoundedRTop] using happ.replay_eq
  simpa [Higham21GivensActualRoundedRowwiseCoefficient] using
    (higham21_q_method_fixed_accumulation_rowwise_backward_stable
      fp A
      (higham21ConcreteGivensExactQ
        (higham21GivensActualConcreteSteps fp m k A hvalid))
      happ.Q_hat (higham21GivensQMethodRTall fp m k A) b
      (higham21GivensActualRoundedOutput fp m k A b hvalid)
      (higham21_givens_qr_gamma_tilde_nonneg fp (m + k) m hvalid)
      hqr hdiag' hvalidTri happ.fixed hQsmall hgram hx
      (by
        simpa [Higham21GivensActualRoundedRowwiseCoefficient] using
          hCondSmall))

/-- Printed `ωᴿ` consequence for the closed actual-rounded Givens output. -/
theorem higham21_theorem21_4_givens_actual_rounded_omegaR_le
    {m k : Nat} (fp : FPModel)
    (A : Fin m → Fin (m + k) → Real) (b : Fin m → Real)
    (hm : 0 < m)
    (hvalid : gammaValid fp 8)
    (hdiag : ∀ i : Fin m,
      ¬ higham21GivensRoundedRTop fp m k A i i = 0)
    (hvalidTri : gammaValid fp m)
    (hgram : ¬ Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0)
    (hQsmall : Higham21GivensActualReplayEtaQ fp m k < 1)
    (hCondSmall :
      3 *
        (Higham21GivensActualRoundedRowwiseCoefficient fp m k *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    higham21RowwiseBackwardErrorOmegaR A b
        (higham21GivensActualRoundedOutput fp m k A b hvalid) ≤
      Real.sqrt 2 *
        Higham21GivensActualRoundedRowwiseCoefficient fp m k := by
  exact higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
    (higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable
      fp A b hm hvalid hdiag hvalidTri hgram hQsmall hCondSmall)

end NumStability
