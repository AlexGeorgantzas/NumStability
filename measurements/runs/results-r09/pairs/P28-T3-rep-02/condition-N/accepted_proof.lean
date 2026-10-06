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
  have hfXbar_mul_Z : data.fXbar * data.Z = data.Xbar := by
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
      _ = data.P * (data.fSigma * data.recoveryDiagonal) * star data.Q := by
            simp only [Matrix.mul_assoc]
      _ = data.P * data.Sigma * star data.Q := by
            rw [data.singular_recovery]

  have hfHbar_mul_Z : data.fHbar * data.Z = data.Hbar := by
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
      _ = data.Q * (data.fSigma * data.recoveryDiagonal) * star data.Q := by
            simp only [Matrix.mul_assoc]
      _ = data.Q * data.Sigma * star data.Q := by
            rw [data.singular_recovery]

  have hy_identity :
      data.fXbar + data.EY = data.U * (data.fHbar + data.EH) := by
    calc
      data.fXbar + data.EY = data.Yhat := data.y_forward.symm
      _ = data.U * data.HY := data.y_polar
      _ = data.U * (data.fHbar + data.EH) := by rw [data.hy_perturbed]

  have herror_identity :
      data.fXbar - data.U * data.fHbar = data.U * data.EH - data.EY := by
    calc
      data.fXbar - data.U * data.fHbar =
          (data.fXbar + data.EY) - (data.U * data.fHbar + data.EY) := by
            abel
      _ = data.U * (data.fHbar + data.EH) -
          (data.U * data.fHbar + data.EY) := by rw [hy_identity]
      _ = data.U * data.EH - data.EY := by
            rw [Matrix.mul_add]
            abel

  have hxbar_transport :
      data.Xbar - data.U * data.Hbar =
        (data.U * data.EH - data.EY) * data.Z := by
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - data.U * (data.fHbar * data.Z) := by
            rw [hfXbar_mul_Z, hfHbar_mul_Z]
      _ = (data.fXbar - data.U * data.fHbar) * data.Z := by
            noncomm_ring
      _ = (data.U * data.EH - data.EY) * data.Z := by
            rw [herror_identity]

  have hxbar_transport_bound :
      ‖data.Xbar - data.U * data.Hbar‖ ≤
        2 * data.eps * (data.d * data.xScale) := by
    rw [hxbar_transport]
    calc
      ‖(data.U * data.EH - data.EY) * data.Z‖ ≤
          ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ := norm_mul_le _ _
      _ ≤ (‖data.U * data.EH‖ + ‖data.EY‖) * ‖data.Z‖ := by
            gcongr
            exact norm_sub_le _ _
      _ = (‖data.EH‖ + ‖data.EY‖) * ‖data.Z‖ := by
            rw [data.U_left_isometry]
      _ ≤ (data.eps * data.fScale + data.eps * data.fScale) * ‖data.Z‖ := by
            gcongr
            · exact data.eh_bound
            · exact data.ey_bound
      _ = 2 * data.eps * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ 2 * data.eps * (data.d * data.xScale) := by
            exact mul_le_mul_of_nonneg_left data.z_scaled_bound
              (mul_nonneg (by norm_num) data.eps_nonneg)

  have hx_transport_identity :
      data.X - data.U * data.Hbar =
        (data.Xbar - data.U * data.Hbar) - data.EX := by
    rw [data.xbar_eq]
    noncomm_ring

  have hx_transport_bound :
      ‖data.X - data.U * data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [hx_transport_identity]
    calc
      ‖data.Xbar - data.U * data.Hbar - data.EX‖ ≤
          ‖data.Xbar - data.U * data.Hbar‖ + ‖data.EX‖ := norm_sub_le _ _
      _ ≤ 2 * data.eps * (data.d * data.xScale) +
          data.eps * data.xScale :=
            add_le_add hxbar_transport_bound data.ex_bound
      _ = p28CoreCoefficient data.eps data.d * data.xScale := by
            simp only [p28CoreCoefficient]
            ring

  have hstar_transport_identity :
      star data.U * data.X - data.Hbar =
        star data.U * (data.X - data.U * data.Hbar) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, data.unitary_left]
    simp

  have hstar_transport_bound :
      ‖star data.U * data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    calc
      ‖star data.U * data.X - data.Hbar‖ =
          ‖star data.U * (data.X - data.U * data.Hbar)‖ := by
            rw [hstar_transport_identity]
      _ = ‖data.X - data.U * data.Hbar‖ :=
            data.Ustar_left_isometry _
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale :=
            hx_transport_bound

  have hsym_contract (A : P28ComplexMatrix n) : ‖p28Sym A‖ ≤ ‖A‖ := by
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

  have hsym_hbar : p28Sym data.Hbar = data.Hbar := by
    rw [p28Sym, data.hbar_selfadjoint]
    module

  have hestimate_difference :
      p28HermitianEstimate data.U data.X - data.Hbar =
        p28Sym (star data.U * data.X - data.Hbar) := by
    calc
      p28HermitianEstimate data.U data.X - data.Hbar =
          p28Sym (star data.U * data.X) - p28Sym data.Hbar := by
            rw [p28HermitianEstimate, hsym_hbar]
      _ = p28Sym (star data.U * data.X - data.Hbar) := by
            unfold p28Sym
            rw [star_sub]
            module

  have hestimate_hbar_bound :
      ‖p28HermitianEstimate data.U data.X - data.Hbar‖ ≤
        p28CoreCoefficient data.eps data.d * data.xScale := by
    rw [hestimate_difference]
    exact hsym_contract _ |>.trans hstar_transport_bound

  constructor
  · have hresidual_identity :
        data.X - data.U * p28HermitianEstimate data.U data.X =
          (data.X - data.U * data.Hbar) +
            data.U * (data.Hbar - p28HermitianEstimate data.U data.X) := by
      noncomm_ring
    rw [hresidual_identity]
    calc
      ‖(data.X - data.U * data.Hbar) +
          data.U * (data.Hbar - p28HermitianEstimate data.U data.X)‖ ≤
          ‖data.X - data.U * data.Hbar‖ +
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
              add_le_add hx_transport_bound hestimate_hbar_bound
      _ = 2 * p28CoreCoefficient data.eps data.d * data.xScale := by ring
  · have hfactor_identity :
        p28HermitianEstimate data.U data.X - data.H =
          (p28HermitianEstimate data.U data.X - data.Hbar) +
            (data.Hbar - data.H) := by
      abel
    rw [hfactor_identity]
    calc
      ‖(p28HermitianEstimate data.U data.X - data.Hbar) +
          (data.Hbar - data.H)‖ ≤
          ‖p28HermitianEstimate data.U data.X - data.Hbar‖ +
            ‖data.Hbar - data.H‖ := norm_add_le _ _
      _ ≤ p28CoreCoefficient data.eps data.d * data.xScale +
            data.eps * data.xScale :=
              add_le_add hestimate_hbar_bound data.hermitian_polar_bound
      _ = (p28CoreCoefficient data.eps data.d + data.eps) *
            data.xScale := by ring

end HighamBench
