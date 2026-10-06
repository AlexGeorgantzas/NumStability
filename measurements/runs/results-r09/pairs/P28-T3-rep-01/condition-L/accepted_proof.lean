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
  have norm_sym_le (A : P28ComplexMatrix n) : ‖p28Sym A‖ ≤ ‖A‖ := by
    rw [p28Sym, norm_smul]
    calc
      ‖(2 : ℂ)⁻¹‖ * ‖A + star A‖ ≤
          ‖(2 : ℂ)⁻¹‖ * (‖A‖ + ‖star A‖) := by
            gcongr
            exact norm_add_le _ _
      _ = ‖A‖ := by
        rw [norm_star]
        norm_num
        ring
  have sym_sub_selfadjoint (A K : P28ComplexMatrix n) (hK : star K = K) :
      p28Sym A - K = p28Sym (A - K) := by
    rw [p28Sym, p28Sym, star_sub, hK]
    module
  have hfz : data.fXbar * data.Z = data.Xbar := by
    rw [data.fxbar_svd, data.z_svd, data.xbar_svd]
    calc
      (data.P * data.fSigma * star data.Q) *
            (data.Q * data.recoveryDiagonal * star data.Q) =
          data.P * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q := by
              simp only [Matrix.mul_assoc]
      _ = data.P * data.fSigma * data.recoveryDiagonal * star data.Q := by
            rw [data.q_unitary_left]
            simp
      _ = data.P * data.Sigma * star data.Q := by
            rw [Matrix.mul_assoc data.P, data.singular_recovery]
  have hhz : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd, data.hbar_svd]
    calc
      (data.Q * data.fSigma * star data.Q) *
            (data.Q * data.recoveryDiagonal * star data.Q) =
          data.Q * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q := by
              simp only [Matrix.mul_assoc]
      _ = data.Q * data.fSigma * data.recoveryDiagonal * star data.Q := by
            rw [data.q_unitary_left]
            simp
      _ = data.Q * data.Sigma * star data.Q := by
            rw [Matrix.mul_assoc data.Q, data.singular_recovery]
  have hyrel :
      data.fXbar - data.U * data.fHbar = data.U * data.EH - data.EY := by
    calc
      data.fXbar - data.U * data.fHbar =
          data.Yhat - data.EY - data.U * data.fHbar := by
            rw [data.y_forward]
            abel
      _ = data.U * data.HY - data.EY - data.U * data.fHbar := by
            rw [data.y_polar]
      _ = data.U * (data.fHbar + data.EH) - data.EY -
          data.U * data.fHbar := by
            rw [data.hy_perturbed]
      _ = data.U * data.EH - data.EY := by noncomm_ring
  have htransport :
      data.Xbar - data.U * data.Hbar =
        (data.U * data.EH - data.EY) * data.Z := by
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - data.U * (data.fHbar * data.Z) := by
            rw [hfz, hhz]
      _ = (data.fXbar - data.U * data.fHbar) * data.Z := by
            noncomm_ring
      _ = (data.U * data.EH - data.EY) * data.Z := by rw [hyrel]
  have htransport_bound :
      ‖data.Xbar - data.U * data.Hbar‖ ≤
        2 * data.d * data.eps * data.xScale := by
    rw [htransport]
    calc
      ‖(data.U * data.EH - data.EY) * data.Z‖ ≤
          ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ := norm_mul_le _ _
      _ ≤ (‖data.U * data.EH‖ + ‖data.EY‖) * ‖data.Z‖ := by
            gcongr
            exact norm_sub_le _ _
      _ = (‖data.EH‖ + ‖data.EY‖) * ‖data.Z‖ := by
            rw [data.U_left_isometry]
      _ ≤ (data.eps * data.fScale + data.eps * data.fScale) *
          ‖data.Z‖ := by
            gcongr
            exact data.eh_bound
            exact data.ey_bound
      _ = 2 * data.eps * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ 2 * data.eps * (data.d * data.xScale) :=
            mul_le_mul_of_nonneg_left data.z_scaled_bound
              (mul_nonneg (by norm_num) data.eps_nonneg)
      _ = 2 * data.d * data.eps * data.xScale := by ring
  have hx_hbar_eq :
      data.X - data.U * data.Hbar =
        (data.Xbar - data.U * data.Hbar) - data.EX := by
    rw [data.xbar_eq]
    abel
  have hx_hbar_bound :
      ‖data.X - data.U * data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [hx_hbar_eq]
    calc
      ‖(data.Xbar - data.U * data.Hbar) - data.EX‖ ≤
          ‖data.Xbar - data.U * data.Hbar‖ + ‖data.EX‖ := norm_sub_le _ _
      _ ≤ 2 * data.d * data.eps * data.xScale +
          data.eps * data.xScale := add_le_add htransport_bound data.ex_bound
      _ = p28CoreCoefficient data.eps data.d * data.xScale := by
            rw [p28CoreCoefficient]
            ring
  have hstar_error_eq :
      star data.U * data.X - data.Hbar =
        star data.U * (data.X - data.U * data.Hbar) := by
    calc
      star data.U * data.X - data.Hbar =
          star data.U * data.X - (star data.U * data.U) * data.Hbar := by
            rw [data.unitary_left]
            simp
      _ = star data.U * (data.X - data.U * data.Hbar) := by
            noncomm_ring
  have hstar_error_bound :
      ‖star data.U * data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [hstar_error_eq, data.Ustar_left_isometry]
    exact hx_hbar_bound
  have hestimate_hbar_eq :
      p28HermitianEstimate data.U data.X - data.Hbar =
        p28Sym (star data.U * data.X - data.Hbar) := by
    rw [p28HermitianEstimate]
    exact sym_sub_selfadjoint _ _ data.hbar_selfadjoint
  have hestimate_hbar_bound :
      ‖p28HermitianEstimate data.U data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [hestimate_hbar_eq]
    exact le_trans (norm_sym_le _) hstar_error_bound
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
            rw [norm_sub_rev data.Hbar]
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale +
          p28CoreCoefficient data.eps data.d * data.xScale :=
            add_le_add hx_hbar_bound hestimate_hbar_bound
      _ = 2 * p28CoreCoefficient data.eps data.d * data.xScale := by ring
  · calc
      ‖p28HermitianEstimate data.U data.X - data.H‖ =
          ‖(p28HermitianEstimate data.U data.X - data.Hbar) +
            (data.Hbar - data.H)‖ := by
              congr 1
              abel
      _ ≤ ‖p28HermitianEstimate data.U data.X - data.Hbar‖ +
          ‖data.Hbar - data.H‖ := norm_add_le _ _
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale +
          data.eps * data.xScale :=
            add_le_add hestimate_hbar_bound data.hermitian_polar_bound
      _ = (p28CoreCoefficient data.eps data.d + data.eps) *
          data.xScale := by ring

end HighamBench
