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
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star data.Q) data.Q,
      data.q_unitary_left, Matrix.one_mul,
      ← Matrix.mul_assoc data.fSigma data.recoveryDiagonal,
      data.singular_recovery]
  have h_fHbar_Z : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd, data.hbar_svd]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star data.Q) data.Q,
      data.q_unitary_left, Matrix.one_mul,
      ← Matrix.mul_assoc data.fSigma data.recoveryDiagonal,
      data.singular_recovery]
  have h_forward_polar :
      data.fXbar + data.EY = data.U * (data.fHbar + data.EH) := by
    calc
      data.fXbar + data.EY = data.Yhat := data.y_forward.symm
      _ = data.U * data.HY := data.y_polar
      _ = data.U * (data.fHbar + data.EH) := by rw [data.hy_perturbed]
  have h_transported :
      data.fXbar - data.U * data.fHbar = data.U * data.EH - data.EY := by
    calc
      data.fXbar - data.U * data.fHbar =
          (data.fXbar + data.EY) - data.U * data.fHbar - data.EY := by
            module
      _ = data.U * (data.fHbar + data.EH) -
          data.U * data.fHbar - data.EY := by rw [h_forward_polar]
      _ = data.U * data.EH - data.EY := by
        rw [Matrix.mul_add]
        module
  have h_xbar_identity :
      data.Xbar - data.U * data.Hbar =
        (data.U * data.EH - data.EY) * data.Z := by
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - data.U * (data.fHbar * data.Z) := by
            rw [h_fXbar_Z, h_fHbar_Z]
      _ = (data.fXbar - data.U * data.fHbar) * data.Z := by
            noncomm_ring
      _ = (data.U * data.EH - data.EY) * data.Z := by
            rw [h_transported]
  have h_error_sum : ‖data.U * data.EH - data.EY‖ ≤
      2 * data.eps * data.fScale := by
    calc
      ‖data.U * data.EH - data.EY‖ ≤
          ‖data.U * data.EH‖ + ‖data.EY‖ := norm_sub_le _ _
      _ = ‖data.EH‖ + ‖data.EY‖ := by rw [data.U_left_isometry]
      _ ≤ data.eps * data.fScale + data.eps * data.fScale :=
        add_le_add data.eh_bound data.ey_bound
      _ = 2 * data.eps * data.fScale := by ring
  have h_xbar_bound :
      ‖data.Xbar - data.U * data.Hbar‖ ≤
        2 * data.d * data.eps * data.xScale := by
    calc
      ‖data.Xbar - data.U * data.Hbar‖ =
          ‖(data.U * data.EH - data.EY) * data.Z‖ := by
            rw [h_xbar_identity]
      _ ≤ ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ := norm_mul_le _ _
      _ ≤ (2 * data.eps * data.fScale) * ‖data.Z‖ :=
        mul_le_mul_of_nonneg_right h_error_sum (norm_nonneg _)
      _ ≤ 2 * data.d * data.eps * data.xScale := by
        have htwoeps : 0 ≤ 2 * data.eps := mul_nonneg (by norm_num) data.eps_nonneg
        have hz := mul_le_mul_of_nonneg_left data.z_scaled_bound htwoeps
        nlinarith
  have h_x_identity :
      data.X - data.U * data.Hbar =
        (data.Xbar - data.U * data.Hbar) - data.EX := by
    rw [data.xbar_eq]
    noncomm_ring
  have h_core :
      ‖data.X - data.U * data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    calc
      ‖data.X - data.U * data.Hbar‖ =
          ‖(data.Xbar - data.U * data.Hbar) - data.EX‖ := by
            rw [h_x_identity]
      _ ≤ ‖data.Xbar - data.U * data.Hbar‖ + ‖data.EX‖ := norm_sub_le _ _
      _ ≤ 2 * data.d * data.eps * data.xScale + data.eps * data.xScale :=
        add_le_add h_xbar_bound data.ex_bound
      _ = p28CoreCoefficient data.eps data.d * data.xScale := by
        simp only [p28CoreCoefficient]
        ring
  have h_star_identity :
      star data.U * (data.X - data.U * data.Hbar) =
        star data.U * data.X - data.Hbar := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, data.unitary_left, Matrix.one_mul]
  have h_star_core :
      ‖star data.U * data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [← h_star_identity, data.Ustar_left_isometry]
    exact h_core
  have h_sym_identity :
      p28HermitianEstimate data.U data.X - data.Hbar =
        p28Sym (star data.U * data.X - data.Hbar) := by
    unfold p28HermitianEstimate p28Sym
    rw [star_sub, data.hbar_selfadjoint]
    module
  have h_sym_contract (A : P28ComplexMatrix n) : ‖p28Sym A‖ ≤ ‖A‖ := by
    unfold p28Sym
    rw [norm_smul]
    have hhalf : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
    calc
      ‖(2 : ℂ)⁻¹‖ * ‖A + star A‖ ≤
          ‖(2 : ℂ)⁻¹‖ * (‖A‖ + ‖star A‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = ‖A‖ := by rw [hhalf, norm_star]; ring
  have h_estimate_hbar :
      ‖p28HermitianEstimate data.U data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    calc
      ‖p28HermitianEstimate data.U data.X - data.Hbar‖ =
          ‖p28Sym (star data.U * data.X - data.Hbar)‖ := by
            rw [h_sym_identity]
      _ ≤ ‖star data.U * data.X - data.Hbar‖ := h_sym_contract _
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale := h_star_core
  constructor
  · have h_residual_identity :
        data.X - data.U * p28HermitianEstimate data.U data.X =
          (data.X - data.U * data.Hbar) +
            data.U * (data.Hbar - p28HermitianEstimate data.U data.X) := by
      noncomm_ring
    calc
      ‖data.X - data.U * p28HermitianEstimate data.U data.X‖ =
          ‖(data.X - data.U * data.Hbar) +
            data.U * (data.Hbar - p28HermitianEstimate data.U data.X)‖ := by
              rw [h_residual_identity]
      _ ≤ ‖data.X - data.U * data.Hbar‖ +
          ‖data.U * (data.Hbar - p28HermitianEstimate data.U data.X)‖ :=
        norm_add_le _ _
      _ = ‖data.X - data.U * data.Hbar‖ +
          ‖data.Hbar - p28HermitianEstimate data.U data.X‖ := by
        rw [data.U_left_isometry]
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale +
          p28CoreCoefficient data.eps data.d * data.xScale := by
        exact add_le_add h_core (by simpa [norm_sub_rev] using h_estimate_hbar)
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
        add_le_add h_estimate_hbar data.hermitian_polar_bound
      _ = (p28CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
        ring

end HighamBench
