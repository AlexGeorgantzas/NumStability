import HighamBench.P28Definitions

namespace HighamBench

open scoped Matrix.Norms.Frobenius

/-- P28-T3: the square-matrix error-transport core of Lemma 4.1. -/
theorem p28_t3_lemma4_1_core {n : ℕ} (data : P28Lemma41CoreData n) :
    ‖data.X - data.U * p28HermitianEstimate data.U data.X‖ ≤
        2 * p28CoreCoefficient data.eps data.d * data.xScale ∧
    ‖p28HermitianEstimate data.U data.X - data.H‖ ≤
        (p28CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
  -- PROOF_START P28-T3-H001
  have h_fXbar_Z : data.fXbar * data.Z = data.Xbar := by
    rw [data.fxbar_svd, data.z_svd, data.xbar_svd]
    calc
      (data.P * data.fSigma * star data.Q) *
            (data.Q * data.recoveryDiagonal * star data.Q) =
          data.P * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q := by noncomm_ring
      _ =
          data.P * (data.fSigma * data.recoveryDiagonal) * star data.Q := by
            rw [data.q_unitary_left]
            simp [Matrix.mul_assoc]
      _ = data.P * data.Sigma * star data.Q := by
            rw [data.singular_recovery]
  have h_UfHbar_Z : (data.U * data.fHbar) * data.Z = data.U * data.Hbar := by
    rw [data.fhbar_svd, data.z_svd, data.hbar_svd]
    calc
      (data.U * (data.Q * data.fSigma * star data.Q)) *
            (data.Q * data.recoveryDiagonal * star data.Q) =
          data.U * (data.Q * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q) := by noncomm_ring
      _ =
          data.U * (data.Q * (data.fSigma * data.recoveryDiagonal) * star data.Q) := by
            rw [data.q_unitary_left]
            simp [Matrix.mul_assoc]
      _ = data.U * (data.Q * data.Sigma * star data.Q) := by
            rw [data.singular_recovery]
  have h_forward_difference :
      data.fXbar - data.U * data.fHbar = data.U * data.EH - data.EY := by
    calc
      data.fXbar - data.U * data.fHbar =
          (data.Yhat - data.EY) - data.U * data.fHbar := by
            rw [data.y_forward]
            abel
      _ = (data.U * data.HY - data.EY) - data.U * data.fHbar := by
            rw [← data.y_polar]
      _ = data.U * data.EH - data.EY := by
            rw [data.hy_perturbed]
            noncomm_ring
  have h_xbar_difference :
      data.Xbar - data.U * data.Hbar =
        (data.U * data.EH - data.EY) * data.Z := by
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - (data.U * data.fHbar) * data.Z := by
            rw [h_fXbar_Z, h_UfHbar_Z]
      _ = (data.fXbar - data.U * data.fHbar) * data.Z := by
            rw [Matrix.sub_mul]
      _ = (data.U * data.EH - data.EY) * data.Z := by
            rw [h_forward_difference]
  have h_xbar_bound :
      ‖data.Xbar - data.U * data.Hbar‖ ≤
        2 * data.d * data.eps * data.xScale := by
    calc
      ‖data.Xbar - data.U * data.Hbar‖ =
          ‖(data.U * data.EH - data.EY) * data.Z‖ := by
            rw [h_xbar_difference]
      _ ≤ ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ :=
            norm_mul_le _ _
      _ ≤ (‖data.U * data.EH‖ + ‖data.EY‖) * ‖data.Z‖ := by
            exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ = (‖data.EH‖ + ‖data.EY‖) * ‖data.Z‖ := by
            rw [data.U_left_isometry]
      _ ≤ (data.eps * data.fScale + data.eps * data.fScale) * ‖data.Z‖ := by
            exact mul_le_mul_of_nonneg_right
              (add_le_add data.eh_bound data.ey_bound) (norm_nonneg _)
      _ = (2 * data.eps) * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ (2 * data.eps) * (data.d * data.xScale) := by
            exact mul_le_mul_of_nonneg_left data.z_scaled_bound
              (mul_nonneg (by norm_num) data.eps_nonneg)
      _ = 2 * data.d * data.eps * data.xScale := by ring
  have h_X_difference :
      data.X - data.U * data.Hbar =
        (data.Xbar - data.U * data.Hbar) - data.EX := by
    rw [data.xbar_eq]
    abel
  have h_core_bound :
      ‖data.X - data.U * data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    calc
      ‖data.X - data.U * data.Hbar‖ =
          ‖(data.Xbar - data.U * data.Hbar) - data.EX‖ := by
            rw [h_X_difference]
      _ ≤ ‖data.Xbar - data.U * data.Hbar‖ + ‖data.EX‖ :=
            norm_sub_le _ _
      _ ≤ 2 * data.d * data.eps * data.xScale + data.eps * data.xScale :=
            add_le_add h_xbar_bound data.ex_bound
      _ = p28CoreCoefficient data.eps data.d * data.xScale := by
            simp only [p28CoreCoefficient]
            ring
  have h_pullback_difference :
      star data.U * data.X - data.Hbar =
        star data.U * (data.X - data.U * data.Hbar) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, data.unitary_left]
    simp
  have h_pullback_bound :
      ‖star data.U * data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [h_pullback_difference, data.Ustar_left_isometry]
    exact h_core_bound
  have h_sym_difference :
      p28HermitianEstimate data.U data.X - data.Hbar =
        (2 : ℂ)⁻¹ •
          ((star data.U * data.X - data.Hbar) +
            star (star data.U * data.X - data.Hbar)) := by
    rw [p28HermitianEstimate, p28Sym, star_sub, data.hbar_selfadjoint]
    module
  have h_sym_bound :
      ‖p28HermitianEstimate data.U data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    calc
      ‖p28HermitianEstimate data.U data.X - data.Hbar‖ =
          ‖(2 : ℂ)⁻¹ •
            ((star data.U * data.X - data.Hbar) +
              star (star data.U * data.X - data.Hbar))‖ := by
                rw [h_sym_difference]
      _ = ‖(2 : ℂ)⁻¹‖ *
          ‖(star data.U * data.X - data.Hbar) +
            star (star data.U * data.X - data.Hbar)‖ := by
              rw [norm_smul]
      _ ≤ ‖(2 : ℂ)⁻¹‖ *
          (‖star data.U * data.X - data.Hbar‖ +
            ‖star (star data.U * data.X - data.Hbar)‖) := by
              exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = ‖star data.U * data.X - data.Hbar‖ := by
            rw [norm_star]
            rw [show ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) by norm_num]
            ring
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale :=
            h_pullback_bound
  have h_residual_decomposition :
      data.X - data.U * p28HermitianEstimate data.U data.X =
        (data.X - data.U * data.Hbar) +
          data.U * (data.Hbar - p28HermitianEstimate data.U data.X) := by
    noncomm_ring
  constructor
  · calc
      ‖data.X - data.U * p28HermitianEstimate data.U data.X‖ =
          ‖(data.X - data.U * data.Hbar) +
            data.U * (data.Hbar - p28HermitianEstimate data.U data.X)‖ := by
              rw [h_residual_decomposition]
      _ ≤ ‖data.X - data.U * data.Hbar‖ +
          ‖data.U * (data.Hbar - p28HermitianEstimate data.U data.X)‖ :=
            norm_add_le _ _
      _ = ‖data.X - data.U * data.Hbar‖ +
          ‖data.Hbar - p28HermitianEstimate data.U data.X‖ := by
            rw [data.U_left_isometry]
      _ = ‖data.X - data.U * data.Hbar‖ +
          ‖p28HermitianEstimate data.U data.X - data.Hbar‖ := by
            rw [← norm_neg (data.Hbar - p28HermitianEstimate data.U data.X)]
            congr 2
            abel
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale +
          p28CoreCoefficient data.eps data.d * data.xScale :=
            add_le_add h_core_bound h_sym_bound
      _ = 2 * p28CoreCoefficient data.eps data.d * data.xScale := by ring
  · calc
      ‖p28HermitianEstimate data.U data.X - data.H‖ ≤
          ‖p28HermitianEstimate data.U data.X - data.Hbar‖ +
            ‖data.Hbar - data.H‖ := by
              rw [show p28HermitianEstimate data.U data.X - data.H =
                (p28HermitianEstimate data.U data.X - data.Hbar) +
                  (data.Hbar - data.H) by abel]
              exact norm_add_le _ _
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale +
          data.eps * data.xScale :=
            add_le_add h_sym_bound data.hermitian_polar_bound
      _ = (p28CoreCoefficient data.eps data.d + data.eps) *
          data.xScale := by ring

end HighamBench
