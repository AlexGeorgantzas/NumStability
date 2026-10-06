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
  have hfxZ : data.fXbar * data.Z = data.Xbar := by
    rw [data.fxbar_svd, data.z_svd, data.xbar_svd]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star data.Q) data.Q,
      data.q_unitary_left, Matrix.one_mul,
      ← Matrix.mul_assoc data.fSigma data.recoveryDiagonal,
      data.singular_recovery]
  have hfhZ : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd, data.hbar_svd]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star data.Q) data.Q,
      data.q_unitary_left, Matrix.one_mul,
      ← Matrix.mul_assoc data.fSigma data.recoveryDiagonal,
      data.singular_recovery]
  have hy_identity :
      data.fXbar + data.EY = data.U * (data.fHbar + data.EH) := by
    calc
      data.fXbar + data.EY = data.Yhat := data.y_forward.symm
      _ = data.U * data.HY := data.y_polar
      _ = data.U * (data.fHbar + data.EH) := by rw [data.hy_perturbed]
  have hf_identity :
      data.fXbar - data.U * data.fHbar = data.U * data.EH - data.EY := by
    calc
      data.fXbar - data.U * data.fHbar =
          (data.fXbar + data.EY) - data.U * data.fHbar - data.EY := by
            abel
      _ = data.U * (data.fHbar + data.EH) -
          data.U * data.fHbar - data.EY := by rw [hy_identity]
      _ = data.U * data.EH - data.EY := by
        simp only [Matrix.mul_add]
        abel
  have hxbar_transport :
      data.Xbar - data.U * data.Hbar =
        (data.U * data.EH - data.EY) * data.Z := by
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - data.U * (data.fHbar * data.Z) := by
            rw [hfxZ, hfhZ]
      _ = (data.fXbar - data.U * data.fHbar) * data.Z := by
        noncomm_ring
      _ = (data.U * data.EH - data.EY) * data.Z := by rw [hf_identity]
  have hxbar_transport_bound :
      ‖data.Xbar - data.U * data.Hbar‖ ≤
        2 * data.d * data.eps * data.xScale := by
    rw [hxbar_transport]
    calc
      ‖(data.U * data.EH - data.EY) * data.Z‖ ≤
          ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ := norm_mul_le _ _
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
  have ha_identity :
      star data.U * data.X - data.Hbar =
        star data.U * ((data.Xbar - data.U * data.Hbar) - data.EX) := by
    calc
      star data.U * data.X - data.Hbar =
          star data.U * data.X - (star data.U * data.U) * data.Hbar := by
            rw [data.unitary_left, Matrix.one_mul]
      _ = star data.U * (data.X - data.U * data.Hbar) := by
        noncomm_ring
      _ = star data.U * ((data.Xbar - data.U * data.Hbar) - data.EX) := by
        rw [data.xbar_eq]
        noncomm_ring
  have ha_bound :
      ‖star data.U * data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [ha_identity, data.Ustar_left_isometry]
    calc
      ‖(data.Xbar - data.U * data.Hbar) - data.EX‖ ≤
          ‖data.Xbar - data.U * data.Hbar‖ + ‖data.EX‖ := norm_sub_le _ _
      _ ≤ 2 * data.d * data.eps * data.xScale +
          data.eps * data.xScale :=
        add_le_add hxbar_transport_bound data.ex_bound
      _ = p28CoreCoefficient data.eps data.d * data.xScale := by
        simp only [p28CoreCoefficient]
        ring
  have hsym_sub :
      p28HermitianEstimate data.U data.X - data.Hbar =
        (2 : ℂ)⁻¹ •
          ((star data.U * data.X - data.Hbar) +
            star (star data.U * data.X - data.Hbar)) := by
    rw [p28HermitianEstimate, p28Sym]
    rw [star_sub, data.hbar_selfadjoint]
    ext i j
    simp
    ring
  have hestimate_hbar :
      ‖p28HermitianEstimate data.U data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [hsym_sub, norm_smul]
    calc
      ‖(2 : ℂ)⁻¹‖ *
          ‖(star data.U * data.X - data.Hbar) +
            star (star data.U * data.X - data.Hbar)‖ ≤
          ‖(2 : ℂ)⁻¹‖ *
            (‖star data.U * data.X - data.Hbar‖ +
              ‖star (star data.U * data.X - data.Hbar)‖) := by
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = ‖star data.U * data.X - data.Hbar‖ := by
        rw [norm_star]
        have hnonneg : 0 ≤ ‖star data.U * data.X - data.Hbar‖ := norm_nonneg _
        norm_num
        linarith
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale := ha_bound
  have hu_right : data.U * star data.U = 1 :=
    mul_eq_one_comm.mp data.unitary_left
  have hx_as_u : data.X = data.U * (star data.U * data.X) := by
    rw [← Matrix.mul_assoc, hu_right, Matrix.one_mul]
  have hx_uhbar :
      ‖data.X - data.U * data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [hx_as_u, ← Matrix.mul_sub, data.U_left_isometry]
    exact ha_bound
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
        rw [← norm_neg (data.Hbar - p28HermitianEstimate data.U data.X)]
        congr 2
        abel
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale +
          p28CoreCoefficient data.eps data.d * data.xScale :=
        add_le_add hx_uhbar hestimate_hbar
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
        add_le_add hestimate_hbar data.hermitian_polar_bound
      _ = (p28CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
        ring

end HighamBench
