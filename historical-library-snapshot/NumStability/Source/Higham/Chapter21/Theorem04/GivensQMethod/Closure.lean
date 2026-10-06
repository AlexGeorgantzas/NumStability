import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.BackwardError.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.StoredReplay.EndToEnd.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.StoredReplay.RoundedReplay
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter21.Theorem04.RowwiseBackwardError

/-!
# Source.Higham.Chapter21.Theorem04.GivensQMethod.Closure

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Actual rounded stored-Givens closure for the Givens branch of Theorem 21.4.



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











namespace Higham21ConcreteGivensReplayStep

























end Higham21ConcreteGivensReplayStep






















































































































































































































































































































/-! ## The same explicit product explains the staged QR reduction -/



































































































































































































































































































































































































































/-! ## A shared concrete QR/replay factor for the Chapter 21 endpoint -/
























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










/-- Rowwise coefficient for the closed actual-rounded Givens branch. -/
noncomputable def Higham21GivensActualRoundedRowwiseCoefficient
    (fp : FPModel) (m k : Nat) : Real :=
  Higham21FixedAccumulationRoundedRowwiseCoefficient fp m
    (H19.Theorem19_10.gamma_tilde fp (m + k) m)
    (Higham21GivensActualReplayEtaQ fp m k)















































































































end NumStability
