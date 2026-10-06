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
  have hfxz : data.fXbar * data.Z = data.Xbar := by
    rw [data.fxbar_svd, data.z_svd]
    calc
      (data.P * data.fSigma * star data.Q) *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          data.P * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q := by noncomm_ring
      _ = data.P * data.fSigma * 1 * data.recoveryDiagonal * star data.Q := by
        rw [data.q_unitary_left]
      _ = data.P * (data.fSigma * data.recoveryDiagonal) * star data.Q := by
        noncomm_ring
      _ = data.P * data.Sigma * star data.Q := by rw [data.singular_recovery]
      _ = data.Xbar := data.xbar_svd.symm
  have hfhz : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd]
    calc
      (data.Q * data.fSigma * star data.Q) *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          data.Q * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q := by noncomm_ring
      _ = data.Q * data.fSigma * 1 * data.recoveryDiagonal * star data.Q := by
        rw [data.q_unitary_left]
      _ = data.Q * (data.fSigma * data.recoveryDiagonal) * star data.Q := by
        noncomm_ring
      _ = data.Q * data.Sigma * star data.Q := by rw [data.singular_recovery]
      _ = data.Hbar := data.hbar_svd.symm
  have htransport : data.fXbar + data.EY =
      data.U * (data.fHbar + data.EH) := by
    calc
      data.fXbar + data.EY = data.Yhat := data.y_forward.symm
      _ = data.U * data.HY := data.y_polar
      _ = data.U * (data.fHbar + data.EH) := by rw [data.hy_perturbed]
  have hfXbar_eq : data.fXbar =
      data.U * data.fHbar + data.U * data.EH - data.EY := by
    calc
      data.fXbar = (data.fXbar + data.EY) - data.EY := by abel
      _ = data.U * (data.fHbar + data.EH) - data.EY := by rw [htransport]
      _ = data.U * data.fHbar + data.U * data.EH - data.EY := by
        rw [Matrix.mul_add]
  have hxbar_error : data.Xbar - data.U * data.Hbar =
      data.U * data.EH * data.Z - data.EY * data.Z := by
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - data.U * (data.fHbar * data.Z) := by
            rw [hfxz, hfhz]
      _ = (data.U * data.fHbar + data.U * data.EH - data.EY) * data.Z -
          data.U * (data.fHbar * data.Z) := by rw [hfXbar_eq]
      _ = data.U * data.EH * data.Z - data.EY * data.Z := by
        noncomm_ring
  have hEHZ : ‖data.U * data.EH * data.Z‖ ≤
      data.eps * data.d * data.xScale := by
    calc
      ‖data.U * data.EH * data.Z‖ ≤ ‖data.U * data.EH‖ * ‖data.Z‖ :=
        norm_mul_le _ _
      _ = ‖data.EH‖ * ‖data.Z‖ := by rw [data.U_left_isometry]
      _ ≤ (data.eps * data.fScale) * ‖data.Z‖ :=
        mul_le_mul_of_nonneg_right data.eh_bound (norm_nonneg _)
      _ = data.eps * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ data.eps * (data.d * data.xScale) :=
        mul_le_mul_of_nonneg_left data.z_scaled_bound data.eps_nonneg
      _ = data.eps * data.d * data.xScale := by ring
  have hEYZ : ‖data.EY * data.Z‖ ≤
      data.eps * data.d * data.xScale := by
    calc
      ‖data.EY * data.Z‖ ≤ ‖data.EY‖ * ‖data.Z‖ := norm_mul_le _ _
      _ ≤ (data.eps * data.fScale) * ‖data.Z‖ :=
        mul_le_mul_of_nonneg_right data.ey_bound (norm_nonneg _)
      _ = data.eps * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ data.eps * (data.d * data.xScale) :=
        mul_le_mul_of_nonneg_left data.z_scaled_bound data.eps_nonneg
      _ = data.eps * data.d * data.xScale := by ring
  have hxbar_bound : ‖data.Xbar - data.U * data.Hbar‖ ≤
      2 * data.d * data.eps * data.xScale := by
    calc
      ‖data.Xbar - data.U * data.Hbar‖ =
          ‖data.U * data.EH * data.Z - data.EY * data.Z‖ := by rw [hxbar_error]
      _ ≤ ‖data.U * data.EH * data.Z‖ + ‖data.EY * data.Z‖ := norm_sub_le _ _
      _ ≤ data.eps * data.d * data.xScale +
          data.eps * data.d * data.xScale := add_le_add hEHZ hEYZ
      _ = 2 * data.d * data.eps * data.xScale := by ring
  have hx_error_eq : data.X - data.U * data.Hbar =
      (data.Xbar - data.U * data.Hbar) - data.EX := by
    rw [data.xbar_eq]
    abel
  have hx_bound : ‖data.X - data.U * data.Hbar‖ ≤
      p28CoreCoefficient data.eps data.d * data.xScale := by
    calc
      ‖data.X - data.U * data.Hbar‖ =
          ‖(data.Xbar - data.U * data.Hbar) - data.EX‖ := by rw [hx_error_eq]
      _ ≤ ‖data.Xbar - data.U * data.Hbar‖ + ‖data.EX‖ := norm_sub_le _ _
      _ ≤ 2 * data.d * data.eps * data.xScale +
          data.eps * data.xScale := add_le_add hxbar_bound data.ex_bound
      _ = p28CoreCoefficient data.eps data.d * data.xScale := by
        simp [p28CoreCoefficient]
        ring
  have hstar_bound : ‖star data.U * data.X - data.Hbar‖ ≤
      p28CoreCoefficient data.eps data.d * data.xScale := by
    calc
      ‖star data.U * data.X - data.Hbar‖ =
          ‖star data.U * (data.X - data.U * data.Hbar)‖ := by
            rw [Matrix.mul_sub, ← Matrix.mul_assoc, data.unitary_left,
              Matrix.one_mul]
      _ = ‖data.X - data.U * data.Hbar‖ := data.Ustar_left_isometry _
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale := hx_bound
  have hestimate_eq : p28HermitianEstimate data.U data.X - data.Hbar =
      (2 : ℂ)⁻¹ • ((star data.U * data.X - data.Hbar) +
        star (star data.U * data.X - data.Hbar)) := by
    simp only [p28HermitianEstimate, p28Sym]
    rw [star_sub, data.hbar_selfadjoint]
    module
  have hestimate_bound :
      ‖p28HermitianEstimate data.U data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [hestimate_eq, norm_smul]
    calc
      ‖(2 : ℂ)⁻¹‖ *
          ‖(star data.U * data.X - data.Hbar) +
            star (star data.U * data.X - data.Hbar)‖ ≤
          ‖(2 : ℂ)⁻¹‖ *
            (‖star data.U * data.X - data.Hbar‖ +
              ‖star (star data.U * data.X - data.Hbar)‖) := by
                gcongr
                exact norm_add_le _ _
      _ = ‖star data.U * data.X - data.Hbar‖ := by
        rw [norm_star]
        norm_num
        ring
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale := hstar_bound
  constructor
  · calc
      ‖data.X - data.U * p28HermitianEstimate data.U data.X‖ =
          ‖(data.X - data.U * data.Hbar) +
            data.U * (data.Hbar - p28HermitianEstimate data.U data.X)‖ := by
              congr 1
              noncomm_ring
      _ ≤ ‖data.X - data.U * data.Hbar‖ +
          ‖data.U * (data.Hbar - p28HermitianEstimate data.U data.X)‖ :=
            norm_add_le _ _
      _ = ‖data.X - data.U * data.Hbar‖ +
          ‖data.Hbar - p28HermitianEstimate data.U data.X‖ := by
            rw [data.U_left_isometry]
      _ = ‖data.X - data.U * data.Hbar‖ +
          ‖p28HermitianEstimate data.U data.X - data.Hbar‖ := by
            congr 1
            exact norm_sub_rev _ _
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale +
          p28CoreCoefficient data.eps data.d * data.xScale :=
            add_le_add hx_bound hestimate_bound
      _ = 2 * p28CoreCoefficient data.eps data.d * data.xScale := by ring
  · calc
      ‖p28HermitianEstimate data.U data.X - data.H‖ ≤
          ‖p28HermitianEstimate data.U data.X - data.Hbar‖ +
            ‖data.Hbar - data.H‖ := by
              simpa only [sub_add_sub_cancel] using
                norm_add_le
                  (p28HermitianEstimate data.U data.X - data.Hbar)
                  (data.Hbar - data.H)
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale +
          data.eps * data.xScale :=
            add_le_add hestimate_bound data.hermitian_polar_bound
      _ = (p28CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
        ring

end HighamBench
