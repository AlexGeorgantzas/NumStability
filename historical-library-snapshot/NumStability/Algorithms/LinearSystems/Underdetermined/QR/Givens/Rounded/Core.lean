import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.StoredReplay.RoundedReplay
import NumStability.Source.Higham.Chapter21.Equation10.RoundedReplay
import NumStability.Source.Higham.Chapter21.Theorem04.GivensQMethod.RoundedReplay

/-!
# Algorithms.Underdetermined.Higham21GivensRounded

Historical W04 compatibility facade retaining the exact private reverse closure.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Rounded stored-Givens application endpoint for Theorem 21.4.



namespace NumStability

/-! ## Stored rotations and their rounded transpose replay -/


































/-! ## Fixed-accumulation application interface -/













































/-! ## Method-independent rounded-Q handoff -/





































































































































































































/-- Lemma 21.2 turns the two fixed-accumulation systems into rowwise backward
stability for the actual supplied output. -/
theorem higham21_q_method_fixed_accumulation_rowwise_backward_stable
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real)
    (Q Q_hat : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (b : Fin m -> Real) (x_hat : Fin (m + k) -> Real)
    {etaQR etaQ : Real}
    (hetaQR : 0 <= etaQR)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError
      (m + k) m (finiteTranspose A) Q R_tall etaQR)
    (hdiag : forall i : Fin m,
      Not (R_tall (Fin.castAdd k i) i = 0))
    (hvalidTri : gammaValid fp m)
    (hQerr : HouseholderQRPanelQhatFixedAccumError
      (m + k) Q Q_hat etaQ)
    (hQsmall : etaQ < 1)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hx :
      x_hat = matMulVec (m + k) Q_hat
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun i j => R_tall (Fin.castAdd k i) j)) b)
          (0 : Fin k -> Real)))
    (hCondSmall :
      3 *
        (Higham21FixedAccumulationRoundedRowwiseCoefficient
            fp m etaQR etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
      (Real.sqrt 2 *
        Higham21FixedAccumulationRoundedRowwiseCoefficient
          fp m etaQR etaQ) := by
  let R_hat : Fin m -> Fin m -> Real := fun i j =>
    R_tall (Fin.castAdd k i) j
  let y1 : Fin m -> Real :=
    fl_forwardSub fp m (matTranspose R_hat) b
  let eta : Real :=
    Higham21FixedAccumulationRoundedRowwiseCoefficient fp m etaQR etaQ
  let Aplus : Fin (m + k) -> Fin m -> Real :=
    undetAplusOfGramNonsingInv A
  let rho : Real :=
    eta * Real.sqrt (((m + k : Nat) : Real)) *
      higham21Cond2With A Aplus
  have hetaQ : 0 <= etaQ :=
    higham21_fixed_accumulation_radius_nonneg hQerr
  have heta : 0 <= eta := by
    exact Higham21FixedAccumulationRoundedRowwiseCoefficient_nonneg
      fp m etaQR etaQ hetaQR hetaQ
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hgram
  obtain ⟨Q_inv, DeltaR, y, _hleft, _hDeltaR,
      hfirst, hsecond, hrow1, hrow2⟩ :=
    higham21_q_method_fixed_accumulation_two_perturbed_systems
      fp A Q Q_hat R_tall b x_hat hqr hdiag hvalidTri hQerr hQsmall hx
  let DeltaA1 : Fin m -> Fin (m + k) -> Real :=
    Higham21QMethodDeltaA1 A Q_inv
      (fun i j => R_hat i j + DeltaR i j)
  let DeltaA2 : Fin m -> Fin (m + k) -> Real :=
    Higham21QMethodDeltaA2 A Q_hat R_hat
  have hrow1' : forall i : Fin m,
      rectRowNorm2 DeltaA1 i <= eta * rectRowNorm2 A i := by
    simpa [DeltaA1, R_hat, eta] using hrow1
  have hrow2' : forall i : Fin m,
      rectRowNorm2 DeltaA2 i <= eta * rectRowNorm2 A i := by
    simpa [DeltaA2, R_hat, eta] using hrow2
  have hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho := by
    simpa [rho] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA1 Aplus eta heta hrow1'
  have hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho := by
    simpa [rho] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA2 Aplus eta heta hrow2'
  have hsmall : 3 * max rho rho < 1 := by
    simpa [rho, eta, Aplus] using hCondSmall
  exact
    higham21_lemma21_2_rowwise_backward_error_bound_of_pseudoinverse_products
      A Aplus DeltaA1 DeltaA2 b x_hat y rho rho eta hRight
      (by simpa [DeltaA1, R_hat] using hfirst)
      (by simpa [DeltaA2, R_hat] using hsecond)
      hProd1 hProd2 hsmall heta hrow1' hrow2'

/-! ## Staged-Givens specialization -/





























































































































































/-- Rowwise backward stability of the actual rounded stored-Givens output,
conditional only on the explicit per-input application certificate. -/
theorem higham21_theorem21_4_givens_stored_replay_rowwise_backward_stable
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensRoundedRTop fp m k A i i = 0))
    (hvalidTri : gammaValid fp m)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (happ : Higham21GivensQMethodApplicationCertificate
      fp m k A b hvalidGivens trace etaQ)
    (hQsmall : etaQ < 1)
    (hCondSmall :
      3 *
        (Higham21GivensRoundedRowwiseCoefficient fp m k etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (higham21GivensStoredRoundedOutput fp m k A b trace)
      (Real.sqrt 2 *
        Higham21GivensRoundedRowwiseCoefficient fp m k etaQ) := by
  have hqr : H19.Theorem19_4.HouseholderQRBackwardError
      (m + k) m (finiteTranspose A)
      (higham21GivensQMethodQ fp m k A hvalidGivens)
      (higham21GivensQMethodRTall fp m k A)
      (H19.Theorem19_10.gamma_tilde fp (m + k) m) :=
    higham21_givens_qr_backward_error_to_generic_certificate
      (higham21_givens_qr_transpose_certificate
        fp A hm hvalidGivens)
  have hdiag' : forall i : Fin m,
      Not (higham21GivensQMethodRTall fp m k A
        (Fin.castAdd k i) i = 0) := by
    simpa [higham21GivensRoundedRTop] using hdiag
  have hx :
      higham21GivensStoredRoundedOutput fp m k A b trace =
        matMulVec (m + k) happ.Q_hat
          (Fin.append
            (fl_forwardSub fp m
              (matTranspose
                (fun i j => higham21GivensQMethodRTall fp m k A
                  (Fin.castAdd k i) j)) b)
            (0 : Fin k -> Real)) := by
    simpa [higham21GivensStoredRoundedOutput,
      higham21GivensRoundedY1, higham21GivensRoundedRTop] using
      happ.replay_eq
  simpa [Higham21GivensRoundedRowwiseCoefficient] using
    (higham21_q_method_fixed_accumulation_rowwise_backward_stable
      fp A
      (higham21GivensQMethodQ fp m k A hvalidGivens)
      happ.Q_hat
      (higham21GivensQMethodRTall fp m k A)
      b (higham21GivensStoredRoundedOutput fp m k A b trace)
      (higham21_givens_qr_gamma_tilde_nonneg
        fp (m + k) m hvalidGivens)
      hqr hdiag' hvalidTri happ.fixed hQsmall hgram hx
      (by simpa [Higham21GivensRoundedRowwiseCoefficient] using hCondSmall))

/-- Printed `omega^R` consequence for the actual rounded stored-Givens
output. -/
theorem higham21_theorem21_4_givens_stored_replay_omegaR_le
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensRoundedRTop fp m k A i i = 0))
    (hvalidTri : gammaValid fp m)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (happ : Higham21GivensQMethodApplicationCertificate
      fp m k A b hvalidGivens trace etaQ)
    (hQsmall : etaQ < 1)
    (hCondSmall :
      3 *
        (Higham21GivensRoundedRowwiseCoefficient fp m k etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    higham21RowwiseBackwardErrorOmegaR A b
        (higham21GivensStoredRoundedOutput fp m k A b trace) <=
      Real.sqrt 2 *
        Higham21GivensRoundedRowwiseCoefficient fp m k etaQ := by
  exact
    higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
      (higham21_theorem21_4_givens_stored_replay_rowwise_backward_stable
        fp A b hm hvalidGivens hdiag hvalidTri hgram trace happ
        hQsmall hCondSmall)











/-- Strongest executable endpoint available from the current API: once the
single stored-replay bridge is supplied, the concrete trace replay is rowwise
backward stable. -/
theorem higham21_theorem21_4_givens_stored_replay_rowwise_of_bridge
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensRoundedRTop fp m k A i i = 0))
    (hvalidTri : gammaValid fp m)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (hbridge : Higham21GivensQMethodStoredReplayBridge
      fp m k A hvalidGivens trace etaQ)
    (hQsmall : etaQ < 1)
    (hCondSmall :
      3 *
        (Higham21GivensRoundedRowwiseCoefficient fp m k etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (higham21GivensStoredRoundedOutput fp m k A b trace)
      (Real.sqrt 2 *
        Higham21GivensRoundedRowwiseCoefficient fp m k etaQ) := by
  let z : Fin (m + k) -> Real :=
    Fin.append (higham21GivensRoundedY1 fp m k A b)
      (0 : Fin k -> Real)
  obtain ⟨Q_hat, hfixed, hreplay⟩ := hbridge z
  let happ : Higham21GivensQMethodApplicationCertificate
      fp m k A b hvalidGivens trace etaQ :=
    { Q_hat := Q_hat
      fixed := hfixed
      replay_eq := by simpa [z] using hreplay }
  exact
    higham21_theorem21_4_givens_stored_replay_rowwise_backward_stable
      fp A b hm hvalidGivens hdiag hvalidTri hgram trace happ
      hQsmall hCondSmall

/-- Printed `omega^R` endpoint under the sole global replay bridge. -/
theorem higham21_theorem21_4_givens_stored_replay_omegaR_le_of_bridge
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensRoundedRTop fp m k A i i = 0))
    (hvalidTri : gammaValid fp m)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (hbridge : Higham21GivensQMethodStoredReplayBridge
      fp m k A hvalidGivens trace etaQ)
    (hQsmall : etaQ < 1)
    (hCondSmall :
      3 *
        (Higham21GivensRoundedRowwiseCoefficient fp m k etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    higham21RowwiseBackwardErrorOmegaR A b
        (higham21GivensStoredRoundedOutput fp m k A b trace) <=
      Real.sqrt 2 *
        Higham21GivensRoundedRowwiseCoefficient fp m k etaQ := by
  exact
    higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
      (higham21_theorem21_4_givens_stored_replay_rowwise_of_bridge
        fp A b hm hvalidGivens hdiag hvalidTri hgram trace hbridge
        hQsmall hCondSmall)

end NumStability
