-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Strict source closure for Theorem 21.4 and the Q-method output in (21.11).

import NumStability.Algorithms.Underdetermined.Higham21GivensClosure
import NumStability.Algorithms.Underdetermined.Higham21QRFoundations
import NumStability.Algorithms.Underdetermined.Higham21RankStability

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
The printed Theorem 21.4 assumes full row rank and a condition of the form
`cond₂(A) m n γₙ < 1`; it does not assume that a computed triangular factor
has nonzero diagonal.  The older concrete endpoints exposed that operational
fact as an additional domain field.  This file derives it from the already
proved QR row perturbation and the printed small-condition hypothesis.

For the retained-trace Givens route, the same source closure also absorbs the
separate `Q_hat` replay-radius premise into one explicit schedule gamma index.
-/

/-- If a perturbed transpose factors through a tall upper-trapezoidal `R` and
its transpose action is injective, then the square top block of `R` is
nonsingular.  Orthogonality is not needed for this direction. -/
theorem higham21_topBlock_det_ne_zero_of_perturbed_transpose_injective
    {m k : Nat}
    (B : Fin m -> Fin (m + k) -> Real)
    (Q : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (hupper : IsUpperTrapezoidal (m + k) m R_tall)
    (hrep : forall i j,
      B i j = matMulRect (m + k) (m + k) m Q R_tall j i)
    (hinj : Function.Injective (rectMatMulVec (finiteTranspose B))) :
    Matrix.det
      ((fun i j => R_tall (Fin.castAdd k i) j) :
        Matrix (Fin m) (Fin m) Real) ≠ 0 := by
  let R_top : Fin m -> Fin m -> Real :=
    fun i j => R_tall (Fin.castAdd k i) j
  have hRblock : R_tall = lsQRTallBlock (k := k) R_top :=
    lsQRTallBlock_of_upper_trapezoidal R_tall hupper
  have hB : finiteTranspose B =
      matMulRectLeft Q (lsQRTallBlock (k := k) R_top) := by
    ext i j
    have hij := hrep j i
    rw [hRblock] at hij
    simpa [finiteTranspose, matMulRectLeft, matMulRect] using hij
  have hRinj : Function.Injective (rectMatMulVec R_top) := by
    intro x y hxy
    apply hinj
    calc
      rectMatMulVec (finiteTranspose B) x =
          rectMatMulVec
            (matMulRectLeft Q (lsQRTallBlock (k := k) R_top)) x := by
        rw [hB]
      _ = matMulVec (m + k) Q
          (rectMatMulVec (lsQRTallBlock (k := k) R_top) x) :=
        rectMatMulVec_matMulRectLeft Q (lsQRTallBlock (k := k) R_top) x
      _ = matMulVec (m + k) Q
          (Fin.append (rectMatMulVec R_top x) (0 : Fin k -> Real)) := by
        rw [lsQRTallBlock_mulVec]
      _ = matMulVec (m + k) Q
          (Fin.append (rectMatMulVec R_top y) (0 : Fin k -> Real)) := by
        rw [hxy]
      _ = matMulVec (m + k) Q
          (rectMatMulVec (lsQRTallBlock (k := k) R_top) y) := by
        rw [lsQRTallBlock_mulVec]
      _ = rectMatMulVec
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_top)) y :=
        (rectMatMulVec_matMulRectLeft Q
          (lsQRTallBlock (k := k) R_top) y).symm
      _ = rectMatMulVec (finiteTranspose B) y := by rw [hB]
  simpa [R_top] using det_ne_zero_of_square_rectMatMulVec_injective hRinj

/-- Row-relative QR error smaller than the inverse-scaled rank radius forces
the computed top block to be nonsingular. -/
theorem higham21_topBlock_det_ne_zero_of_qr_rowwise_smallness
    {m k : Nat}
    (A DeltaA : Fin m -> Fin (m + k) -> Real)
    (Aplus : Fin (m + k) -> Fin m -> Real)
    (Q : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    {eta : Real}
    (heta : 0 <= eta)
    (hrow : forall i : Fin m,
      rectRowNorm2 DeltaA i <= eta * rectRowNorm2 A i)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hsmall :
      eta * Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A Aplus < 1)
    (hupper : IsUpperTrapezoidal (m + k) m R_tall)
    (hrep : forall i j,
      A i j + DeltaA i j =
        matMulRect (m + k) (m + k) m Q R_tall j i) :
    Matrix.det
      ((fun i j => R_tall (Fin.castAdd k i) j) :
        Matrix (Fin m) (Fin m) Real) ≠ 0 := by
  let c := eta * Real.sqrt (((m + k : Nat) : Real)) *
    higham21Cond2With A Aplus
  have hc : 0 <= c := by
    exact mul_nonneg
      (mul_nonneg heta (Real.sqrt_nonneg _))
      (higham21Cond2With_nonneg A Aplus)
  have hproduct : rectOpNorm2Le (rectMatMul Aplus DeltaA) c := by
    simpa [c] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA Aplus eta heta hrow
  have hinj : Function.Injective
      (rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA i j))) :=
    higham21_theorem21_1_perturbed_transpose_injective_of_right_inverse
      A Aplus DeltaA hRight hproduct hc (by simpa [c] using hsmall)
  exact higham21_topBlock_det_ne_zero_of_perturbed_transpose_injective
    (fun i j => A i j + DeltaA i j) Q R_tall hupper hrep hinj

/-- The Householder QR row perturbation radius is absorbed by the single
source-facing gamma used in the existing Theorem-21.4 endpoint. -/
theorem higham21_householder_qr_scaled_radius_le_rounded_gamma
    (fp : FPModel) (m k : Nat) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    H19.Theorem19_4.gamma_tilde fp (m + k) m *
        Real.sqrt (((m + k : Nat) : Real)) <=
      gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
  let N := m + k
  let H := Higham21QMethodRoundedGammaBaseIndex m k
  let etaQR := H19.Theorem19_4.gamma_tilde fp (m + k) m
  have hN : 1 <= N := by simp [N]; omega
  have hComputed :=
    Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have hRowValid :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k hComputed
  have hQRValid :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k hRowValid
  have hetaQR : 0 <= etaQR := by
    simpa [etaQR] using H19.Theorem19_4.gamma_tilde_nonneg fp hQRValid
  have hetaQ : 0 <= Higham21QMethodQhatRadius fp m k :=
    Higham21QMethodQhatRadius_nonneg fp m k hComputed
  have hetaQR_le_coeff :
      etaQR <= Higham21QMethodRoundedRowwiseCoefficient fp m k := by
    have hterm : 0 <=
        Higham21QMethodQhatRadius fp m k * (1 + etaQR) :=
      mul_nonneg hetaQ (by linarith)
    unfold Higham21QMethodRoundedRowwiseCoefficient
    unfold Higham21QMethodRoundedRowwiseCoefficientOfInverseBound
    exact (le_add_of_nonneg_right hterm).trans (le_max_right _ _)
  have hetaQR_le_gammaH : etaQR <= gamma fp H := by
    exact hetaQR_le_coeff.trans (by
      simpa [H] using
        Higham21QMethodRoundedRowwiseCoefficient_le_gamma_base
          fp m k hm hvalid)
  have hNH_le : N * H <= Higham21QMethodRoundedGammaIndex m k := by
    have hN3 : N <= 3 * N := Nat.le_mul_of_pos_left N (by norm_num)
    simpa [Higham21QMethodRoundedGammaIndex, N, H,
      Nat.mul_assoc] using Nat.mul_le_mul_right H hN3
  have hNHvalid : gammaValid fp (N * H) :=
    gammaValid_mono fp hNH_le hvalid
  have hgammaH0 : 0 <= gamma fp H :=
    gamma_nonneg fp (gammaValid_mono fp (Nat.le_mul_of_pos_left H (by
      simpa [N] using Nat.add_pos_left hm k)) hNHvalid)
  calc
    etaQR * Real.sqrt (((m + k : Nat) : Real)) =
        etaQR * Real.sqrt (N : Real) := by simp [N]
    _ <= gamma fp H * Real.sqrt (N : Real) :=
      mul_le_mul_of_nonneg_right hetaQR_le_gammaH (Real.sqrt_nonneg _)
    _ <= gamma fp H * (N : Real) :=
      mul_le_mul_of_nonneg_left (higham21_sqrt_nat_le_nat N) hgammaH0
    _ = (N : Real) * gamma fp H := by ring
    _ <= gamma fp (N * H) := gamma_nsmul_le fp N H hN hNHvalid
    _ <= gamma fp (Higham21QMethodRoundedGammaIndex m k) :=
      gamma_mono fp hNH_le hvalid

/-- The printed full-row-rank and small-condition hypotheses construct the
entire concrete Householder domain, including computed triangular
nonbreakdown. -/
theorem Higham21QMethodFullRowRankComputedQRDomain.of_source_smallness
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    Higham21QMethodFullRowRankComputedQRDomain m k fp A := by
  let N := m + k
  let etaQR := H19.Theorem19_4.gamma_tilde fp N m
  let Q := fl_householderQRPanel_Q fp N m (finiteTranspose A)
  let R := fl_householderQRPanel_R fp N m (finiteTranspose A)
  have hComputed :=
    Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have hRowValid :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k hComputed
  have hQRValid :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k hRowValid
  have hqr : H19.Theorem19_4.HouseholderQRBackwardError N m
      (finiteTranspose A) Q R etaQR := by
    simpa [N, Q, R, etaQR] using
      H19.Theorem19_4.householder_qr_backward_error
        fp N m (finiteTranspose A) hm (by simp [N]) hQRValid
  obtain ⟨DeltaA, hrep, hrow⟩ :=
    higham21_theorem21_4_qr_transpose_row_perturbation_bound
      A Q R etaQR hqr
  have hdetA : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0 :=
    higham21_rectGram_det_ne_zero_of_transpose_full_col_rank A hfull
  have hRight :
      rectMatMul A (undetAplusOfGramNonsingInv A) = idMatrix m :=
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      A hdetA
  have hetaQR : 0 <= etaQR := by
    simpa [etaQR] using H19.Theorem19_4.gamma_tilde_nonneg fp hQRValid
  have hscaled :
      etaQR * Real.sqrt (N : Real) <=
        gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
    simpa [N, etaQR] using
      higham21_householder_qr_scaled_radius_le_rounded_gamma
        fp m k hm hvalid
  have hcond0 : 0 <=
      higham21Cond2With A (undetAplusOfGramNonsingInv A) :=
    higham21Cond2With_nonneg A (undetAplusOfGramNonsingInv A)
  have hsmallQR :
      etaQR * Real.sqrt (N : Real) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1 :=
    (mul_le_mul_of_nonneg_right hscaled hcond0).trans_lt hCondSmall
  have hdetR := higham21_topBlock_det_ne_zero_of_qr_rowwise_smallness
    A DeltaA (undetAplusOfGramNonsingInv A) Q R hetaQR hrow hRight
      (by simpa [N] using hsmallQR) hqr.upper hrep
  have hnonbreak : Higham21QMethodTopBlockNonbreakdown m k fp A := by
    exact Higham21QMethodTopBlockNonbreakdown.of_topBlock_det_ne_zero
      fp A (by simpa [R, N] using hdetR)
  exact ⟨hfull, by
    simpa [Higham21QMethodTopBlockNonbreakdown] using hnonbreak⟩

/-- Theorem 21.4 on the actual rounded Householder output, now with exactly
the printed rank/small-condition source surface (plus model gamma validity). -/
theorem higham21_theorem21_4_computed_qhat_rowwise_backward_stable_source
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m -> Fin m -> Real := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k -> Real))
    UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
      (gamma fp (Higham21QMethodRoundedGammaIndex m k)) := by
  exact higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma
    fp A b hm
      (Higham21QMethodFullRowRankComputedQRDomain.of_source_smallness
        fp A hm hfull hvalid hCondSmall)
      hvalid hCondSmall

/-! ## Retained-trace Givens replay smallness -/

/-- The fixed-reference Givens replay recurrence is a scaled copy of the
standard multiplicative residual recurrence. -/
theorem higham21GivensReplayAccumBound_eq_sqrt_mul_residualAccumBound
    (n : Nat) (c : Real) : forall r : Nat,
    higham21GivensReplayAccumBound n c r =
      Real.sqrt (n : Real) * residualAccumBound c r := by
  intro r
  induction r with
  | zero => simp [higham21GivensReplayAccumBound, residualAccumBound]
  | succ r ih =>
      simp only [higham21GivensReplayAccumBound, residualAccumBound]
      rw [ih]
      ring

/-- Operation-count index sufficient for all local Givens kernels, the
triangular solve, and the complete retained-trace replay. -/
noncomputable def Higham21GivensOperationalGammaIndex (m k : Nat) : Nat :=
  let N := m + k
  let r := (givensQRStageTaskList N m (givensQRStageCount N m)).length
  2 * (N * ((r + 1) * (8 * N)))

theorem Higham21GivensOperationalGammaIndex.valid8
    (fp : FPModel) (m k : Nat) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21GivensOperationalGammaIndex m k)) :
    gammaValid fp 8 := by
  apply gammaValid_mono fp
  · let N := m + k
    let r := (givensQRStageTaskList N m (givensQRStageCount N m)).length
    change 8 <= 2 * (N * ((r + 1) * (8 * N)))
    have hN : 1 <= N := by simp [N]; omega
    have h8N : 8 <= 8 * N := by
      simpa using Nat.mul_le_mul_left 8 hN
    exact h8N.trans
      ((Nat.le_mul_of_pos_left (8 * N) (Nat.succ_pos r)).trans
        ((Nat.le_mul_of_pos_left ((r + 1) * (8 * N)) (by omega : 0 < N)).trans
          (Nat.le_mul_of_pos_left _ (by norm_num))))
  · exact hvalid

theorem Higham21GivensOperationalGammaIndex.validM
    (fp : FPModel) (m k : Nat) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21GivensOperationalGammaIndex m k)) :
    gammaValid fp m := by
  apply gammaValid_mono fp
  · let N := m + k
    let r := (givensQRStageTaskList N m (givensQRStageCount N m)).length
    change m <= 2 * (N * ((r + 1) * (8 * N)))
    have hmN : m <= N := by simp [N]
    have hN8N : N <= 8 * N := Nat.le_mul_of_pos_left N (by norm_num)
    exact hmN.trans (hN8N.trans
      ((Nat.le_mul_of_pos_left (8 * N) (Nat.succ_pos r)).trans
        ((Nat.le_mul_of_pos_left ((r + 1) * (8 * N)) (by
            simp [N]; omega : 0 < N)).trans
          (Nat.le_mul_of_pos_left _ (by norm_num)))))
  · exact hvalid

/-- Validity at the operational schedule index forces the actual accumulated
Givens replay radius below one; no independent `hQsmall` premise is needed. -/
theorem Higham21GivensActualReplayEtaQ_lt_one_of_operational_gammaValid
    (fp : FPModel) (m k : Nat) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21GivensOperationalGammaIndex m k)) :
    Higham21GivensActualReplayEtaQ fp m k < 1 := by
  let N := m + k
  let r := (givensQRStageTaskList N m (givensQRStageCount N m)).length
  let K := 8 * N
  let M := N * ((r + 1) * K)
  have hN : 1 <= N := by simp [N]; omega
  have hK_le_rK : K <= (r + 1) * K :=
    Nat.le_mul_of_pos_left K (Nat.succ_pos r)
  have hrK_le_M : (r + 1) * K <= M :=
    Nat.le_mul_of_pos_left ((r + 1) * K) (by omega : 0 < N)
  have hM_le_index : M <= Higham21GivensOperationalGammaIndex m k := by
    simp [Higham21GivensOperationalGammaIndex, M, K, N, r]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  have hK_le_index : K <= Higham21GivensOperationalGammaIndex m k :=
    (hK_le_rK.trans hrK_le_M).trans hM_le_index
  have h8_le_K : 8 <= K := by
    simpa [K] using Nat.mul_le_mul_left 8 hN
  have h8valid : gammaValid fp 8 :=
    gammaValid_mono fp (h8_le_K.trans hK_le_index) hvalid
  have hKvalid : gammaValid fp K :=
    gammaValid_mono fp hK_le_index hvalid
  have hc0 : 0 <= gamma fp 8 * Real.sqrt (N : Real) :=
    mul_nonneg (gamma_nonneg fp h8valid) (Real.sqrt_nonneg _)
  have hc_le : gamma fp 8 * Real.sqrt (N : Real) <= gamma fp K := by
    calc
      gamma fp 8 * Real.sqrt (N : Real) <= gamma fp 8 * (N : Real) :=
        mul_le_mul_of_nonneg_left (higham21_sqrt_nat_le_nat N)
          (gamma_nonneg fp h8valid)
      _ = (N : Real) * gamma fp 8 := by ring
      _ <= gamma fp (N * 8) := gamma_nsmul_le fp N 8 hN (by
        simpa [K, Nat.mul_comm] using hKvalid)
      _ = gamma fp K := by simp [K, Nat.mul_comm]
  have hrK_le : r * K <= (r + 1) * K :=
    Nat.mul_le_mul_right K (Nat.le_succ r)
  have hrKvalid : gammaValid fp (r * K) :=
    gammaValid_mono fp
      ((hrK_le.trans hrK_le_M).trans hM_le_index) hvalid
  have hNrK_le_M : N * (r * K) <= M := by
    exact Nat.mul_le_mul_left N hrK_le
  have hNrKvalid : gammaValid fp (N * (r * K)) :=
    gammaValid_mono fp (hNrK_le_M.trans hM_le_index) hvalid
  have hMvalid : gammaValid fp M :=
    gammaValid_mono fp hM_le_index hvalid
  have h2Mvalid : gammaValid fp (2 * M) := by
    simpa [Higham21GivensOperationalGammaIndex, M, K, N, r] using hvalid
  have hresMono :
      residualAccumBound (gamma fp 8 * Real.sqrt (N : Real)) r <=
        residualAccumBound (gamma fp K) r :=
    residualAccumBound_mono hc0 hc_le r
  have hresGamma : residualAccumBound (gamma fp K) r <= gamma fp (r * K) :=
    residualAccumBound_gamma_le_gamma_mul fp K r hrKvalid
  have hgamma_rK0 : 0 <= gamma fp (r * K) := gamma_nonneg fp hrKvalid
  calc
    Higham21GivensActualReplayEtaQ fp m k =
        Real.sqrt (N : Real) *
          residualAccumBound (gamma fp 8 * Real.sqrt (N : Real)) r := by
      simp [Higham21GivensActualReplayEtaQ, N, r,
        higham21GivensReplayAccumBound_eq_sqrt_mul_residualAccumBound]
    _ <= Real.sqrt (N : Real) * residualAccumBound (gamma fp K) r :=
      mul_le_mul_of_nonneg_left hresMono (Real.sqrt_nonneg _)
    _ <= Real.sqrt (N : Real) * gamma fp (r * K) :=
      mul_le_mul_of_nonneg_left hresGamma (Real.sqrt_nonneg _)
    _ <= (N : Real) * gamma fp (r * K) :=
      mul_le_mul_of_nonneg_right (higham21_sqrt_nat_le_nat N) hgamma_rK0
    _ <= gamma fp (N * (r * K)) :=
      gamma_nsmul_le fp N (r * K) hN hNrKvalid
    _ <= gamma fp M := gamma_mono fp hNrK_le_M hMvalid
    _ < 1 := gamma_lt_one fp M h2Mvalid

/-- Full source rank and the printed Lemma-21.2 smallness condition force the
actual retained-trace Givens top block to be nonsingular. -/
theorem higham21_givens_actual_topBlock_nonbreakdown_of_source_smallness
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hvalid : gammaValid fp (Higham21GivensOperationalGammaIndex m k))
    (hCondSmall :
      3 * (Higham21GivensActualRoundedRowwiseCoefficient fp m k *
        Real.sqrt (((m + k : Nat) : Real)) *
        higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    forall i : Fin m, higham21GivensRoundedRTop fp m k A i i ≠ 0 := by
  let N := m + k
  let etaQR := H19.Theorem19_10.gamma_tilde fp N m
  let etaQ := Higham21GivensActualReplayEtaQ fp m k
  let eta := Higham21GivensActualRoundedRowwiseCoefficient fp m k
  have hvalid8 :=
    Higham21GivensOperationalGammaIndex.valid8 fp m k hm hvalid
  let Q := higham21ConcreteGivensExactQ
    (higham21GivensActualConcreteSteps fp m k A hvalid8)
  let R := higham21GivensQMethodRTall fp m k A
  have hqr := higham21_givens_actual_qr_transpose_certificate
    fp m k A hvalid8
  obtain ⟨DeltaA, hrep, hrow⟩ :=
    higham21_theorem21_4_qr_transpose_row_perturbation_bound
      A Q R etaQR (by simpa [Q, R, etaQR] using hqr)
  have hdetA : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0 :=
    higham21_rectGram_det_ne_zero_of_transpose_full_col_rank A hfull
  have hRight :
      rectMatMul A (undetAplusOfGramNonsingInv A) = idMatrix m :=
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      A hdetA
  have hetaQR0 : 0 <= etaQR := by
    simpa [etaQR] using
      higham21_givens_qr_gamma_tilde_nonneg fp N m hvalid8
  have hetaQ0 : 0 <= etaQ := by
    unfold etaQ Higham21GivensActualReplayEtaQ
    exact higham21GivensReplayAccumBound_nonneg _
      (mul_nonneg (gamma_nonneg fp hvalid8) (Real.sqrt_nonneg _)) _
  have hetaQR_le_eta : etaQR <= eta := by
    have hterm : 0 <= etaQ * (1 + etaQR) :=
      mul_nonneg hetaQ0 (by linarith)
    unfold eta Higham21GivensActualRoundedRowwiseCoefficient
    unfold Higham21FixedAccumulationRoundedRowwiseCoefficient
    exact (le_add_of_nonneg_right hterm).trans (le_max_right _ _)
  have hsqrt0 : 0 <= Real.sqrt (N : Real) := Real.sqrt_nonneg _
  have hcond0 : 0 <=
      higham21Cond2With A (undetAplusOfGramNonsingInv A) :=
    higham21Cond2With_nonneg A (undetAplusOfGramNonsingInv A)
  have hsmallQR :
      etaQR * Real.sqrt (N : Real) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1 := by
    have hle1 : etaQR * Real.sqrt (N : Real) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) <=
        eta * Real.sqrt (N : Real) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hetaQR_le_eta hsqrt0) hcond0
    have hbase0 : 0 <= eta * Real.sqrt (N : Real) *
        higham21Cond2With A (undetAplusOfGramNonsingInv A) := by
      exact mul_nonneg
        (mul_nonneg (hetaQR0.trans hetaQR_le_eta) hsqrt0) hcond0
    have hthree : 3 *
        (eta * Real.sqrt (N : Real) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1 := by
      simpa [eta, N] using hCondSmall
    have hbase_lt : eta * Real.sqrt (N : Real) *
        higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1 := by
      nlinarith
    exact hle1.trans_lt hbase_lt
  have hdetR := higham21_topBlock_det_ne_zero_of_qr_rowwise_smallness
    A DeltaA (undetAplusOfGramNonsingInv A) Q R hetaQR0 hrow hRight
      (by simpa [N] using hsmallQR) hqr.upper hrep
  have hupperTop : IsUpperTrapezoidal m m
      (fun i j => R (Fin.castAdd k i) j) :=
    lsQRTallBlock_top_upper_of_upper_trapezoidal R hqr.upper
  have hdiag := diag_ne_zero_of_upper_triangular_det_ne_zero m
    (fun i j => R (Fin.castAdd k i) j) hupperTop hdetR
  simpa [R, higham21GivensRoundedRTop] using hdiag

/-- The Givens alternative of Theorem 21.4 with all operational guards
derived from source rank, one schedule gamma-validity hypothesis, and the
printed small-condition inequality. -/
theorem higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable_source
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hvalid : gammaValid fp (Higham21GivensOperationalGammaIndex m k))
    (hCondSmall :
      3 * (Higham21GivensActualRoundedRowwiseCoefficient fp m k *
        Real.sqrt (((m + k : Nat) : Real)) *
        higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (higham21GivensActualRoundedOutput fp m k A b (by
        exact Higham21GivensOperationalGammaIndex.valid8
          fp m k hm hvalid))
      (Real.sqrt 2 *
        Higham21GivensActualRoundedRowwiseCoefficient fp m k) := by
  have hvalid8 : gammaValid fp 8 :=
    Higham21GivensOperationalGammaIndex.valid8 fp m k hm hvalid
  have hvalidM : gammaValid fp m :=
    Higham21GivensOperationalGammaIndex.validM fp m k hm hvalid
  have hdiag :=
    higham21_givens_actual_topBlock_nonbreakdown_of_source_smallness
      fp A hm hfull hvalid hCondSmall
  have hgram : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0 :=
    higham21_rectGram_det_ne_zero_of_transpose_full_col_rank A hfull
  have hQsmall :=
    Higham21GivensActualReplayEtaQ_lt_one_of_operational_gammaValid
      fp m k hm hvalid
  simpa using
    higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable
      fp A b hm hvalid8 hdiag hvalidM hgram hQsmall hCondSmall

end NumStability
