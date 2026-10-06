import HighamBench.P03Definitions

namespace HighamBench

lemma p03VecInfNorm_matVec_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p03VecInfNorm (p03MatVec A x) ≤
      p03MatInfNorm A * p03VecInfNorm x := by
  unfold p03VecInfNorm p03MatInfNorm p03MatVec
  simpa [Matrix.mulVec] using
    (Matrix.linfty_opNorm_mulVec
      (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) x)

lemma p03VecInfNorm_le_of_abs_le {n : ℕ} (x : Fin n → ℝ) {c : ℝ}
    (h : ∀ j, |x j| ≤ c) (hc : 0 ≤ c) :
    p03VecInfNorm x ≤ c := by
  unfold p03VecInfNorm
  rw [pi_norm_le_iff_of_nonneg hc]
  intro j
  simpa using h j

theorem p03_t3_normwise_residual_contraction
    {n : ℕ} (run : P03NormwiseIRRun n) (i : ℕ) :
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
      p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
  -- PROOF_START P03-T3-H001
  have huS : 0 ≤ run.uS :=
    le_trans run.uR_nonneg (le_trans run.uR_le_u run.u_le_uS)
  have hu : 0 ≤ run.u := le_trans run.uR_nonneg run.uR_le_u
  have hgamma :
      0 ≤ gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) := by
    unfold gamma
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) run.uR_nonneg
    · exact le_of_lt (sub_pos.mpr run.gamma_valid)
  have hA : 0 ≤ p03MatInfNorm run.A := by
    unfold p03MatInfNorm
    rw [Matrix.linfty_opNorm_def]
    exact NNReal.coe_nonneg _
  have hAinv : 0 ≤ p03MatInfNorm run.Ainv := by
    unfold p03MatInfNorm
    rw [Matrix.linfty_opNorm_def]
    exact NNReal.coe_nonneg _
  have hres : 0 ≤ p03VecInfNorm (p03ExactResidual run i) := by
    unfold p03VecInfNorm
    exact norm_nonneg _
  have hb : 0 ≤ p03VecInfNorm run.b := by
    unfold p03VecInfNorm
    exact norm_nonneg _
  have hx : 0 ≤ p03VecInfNorm (run.x i) := by
    unfold p03VecInfNorm
    exact norm_nonneg _
  have hxnext : 0 ≤ p03VecInfNorm (run.x (i + 1)) := by
    unfold p03VecInfNorm
    exact norm_nonneg _

  have hdeltaR :
      p03VecInfNorm (run.deltaR i) ≤
        run.uS * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
            gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
    have hright :
        0 ≤ run.uS * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
            gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
      positivity
    apply p03VecInfNorm_le_of_abs_le _ _ hright
    intro j
    have hresj :
        |p03ExactResidual run i j| ≤
          p03VecInfNorm (p03ExactResidual run i) := by
      unfold p03VecInfNorm
      simpa using norm_le_pi_norm (p03ExactResidual run i) j
    have hbj : |run.b j| ≤ p03VecInfNorm run.b := by
      unfold p03VecInfNorm
      simpa using norm_le_pi_norm run.b j
    have hmatj :
        p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j ≤
          p03MatInfNorm run.A * p03VecInfNorm (run.x i) := by
      calc
        p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j
            ≤ |p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j| :=
              le_abs_self _
        _ ≤ p03VecInfNorm
              (p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i))) := by
              unfold p03VecInfNorm
              simpa using norm_le_pi_norm
                (p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i))) j
        _ ≤ p03MatInfNorm (p03MatAbs run.A) *
              p03VecInfNorm (p03VecAbs (run.x i)) :=
              p03VecInfNorm_matVec_le _ _
        _ = p03MatInfNorm run.A * p03VecInfNorm (run.x i) := by
              unfold p03MatInfNorm p03VecInfNorm p03MatAbs p03VecAbs
              simp [Matrix.linfty_opNorm_def, Pi.norm_def]
    have hfirst := mul_le_mul_of_nonneg_left hresj huS
    have hinside := add_le_add hbj hmatj
    have hcoef :
        0 ≤ (1 + run.uS) *
          gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) := by
      positivity
    have hsecond := mul_le_mul_of_nonneg_left hinside hcoef
    exact le_trans (run.residual_error_bound i j) (add_le_add hfirst hsecond)

  have hrHat_eq :
      run.rHat i = p03ExactResidual run i + run.deltaR i := by
    funext j
    simpa [p03ExactResidual] using run.residual_equation i j
  have hrHat :
      p03VecInfNorm (run.rHat i) ≤
        (1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
            gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
    have htri :
        p03VecInfNorm (run.rHat i) ≤
          p03VecInfNorm (p03ExactResidual run i) +
            p03VecInfNorm (run.deltaR i) := by
      rw [hrHat_eq]
      unfold p03VecInfNorm
      exact norm_add_le _ _
    linarith

  let hvec : Fin n → ℝ :=
    fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j
  have hAd_eq :
      p03MatVec run.A (run.dHat i) = run.rHat i - hvec := by
    funext j
    dsimp [hvec]
    ring
  have hAd :
      p03VecInfNorm (p03MatVec run.A (run.dHat i)) ≤
        p03VecInfNorm (run.rHat i) + p03VecInfNorm hvec := by
    rw [hAd_eq]
    unfold p03VecInfNorm
    exact norm_sub_le _ _
  have hd_inverse :
      run.dHat i = p03MatVec run.Ainv (p03MatVec run.A (run.dHat i)) := by
    funext j
    exact (run.inverse_action (run.dHat i) j).symm
  have hdHat :
      p03VecInfNorm (run.dHat i) ≤
        p03MatInfNorm run.Ainv *
          (p03VecInfNorm (run.rHat i) + p03VecInfNorm hvec) := by
    calc
      p03VecInfNorm (run.dHat i) =
          p03VecInfNorm
            (p03MatVec run.Ainv (p03MatVec run.A (run.dHat i))) := by
            exact congrArg p03VecInfNorm hd_inverse
      _ ≤ p03MatInfNorm run.Ainv *
            p03VecInfNorm (p03MatVec run.A (run.dHat i)) :=
            p03VecInfNorm_matVec_le _ _
      _ ≤ p03MatInfNorm run.Ainv *
            (p03VecInfNorm (run.rHat i) + p03VecInfNorm hvec) :=
            mul_le_mul_of_nonneg_left hAd hAinv

  have hc1 : 0 ≤ run.c1 i := run.c1_nonneg i
  have hc2 : 0 ≤ run.c2 i := run.c2_nonneg i
  have hkappa : 0 ≤ p03KappaInf run := by
    unfold p03KappaInf
    positivity
  have hsolver₁ :
      p03VecInfNorm hvec ≤
        run.uS *
          (run.c1 i * p03MatInfNorm run.A *
              (p03MatInfNorm run.Ainv *
                (p03VecInfNorm (run.rHat i) + p03VecInfNorm hvec)) +
            run.c2 i * p03VecInfNorm (run.rHat i)) := by
    calc
      p03VecInfNorm hvec ≤
          run.uS *
            (run.c1 i * p03MatInfNorm run.A *
                p03VecInfNorm (run.dHat i) +
              run.c2 i * p03VecInfNorm (run.rHat i)) := by
              simpa [hvec] using run.correction_solver_bound i
      _ ≤ run.uS *
            (run.c1 i * p03MatInfNorm run.A *
                (p03MatInfNorm run.Ainv *
                  (p03VecInfNorm (run.rHat i) + p03VecInfNorm hvec)) +
              run.c2 i * p03VecInfNorm (run.rHat i)) := by
              apply mul_le_mul_of_nonneg_left _ huS
              exact add_le_add
                (mul_le_mul_of_nonneg_left hdHat (mul_nonneg hc1 hA))
                (le_refl _)
  have hden :
      0 < 1 - run.c1 i * p03KappaInf run * run.uS := by
    simpa [p03KappaInf, mul_assoc] using run.denominator_condition i
  have hsolver_rearranged :
      (1 - run.c1 i * p03KappaInf run * run.uS) *
          p03VecInfNorm hvec ≤
        run.uS * (run.c1 i * p03KappaInf run + run.c2 i) *
          p03VecInfNorm (run.rHat i) := by
    unfold p03KappaInf
    nlinarith [hsolver₁]
  have hsolver :
      p03VecInfNorm hvec ≤
        run.uS * p03CorrectionRatio run i *
          p03VecInfNorm (run.rHat i) := by
    calc
      p03VecInfNorm hvec ≤
          (run.uS * (run.c1 i * p03KappaInf run + run.c2 i) *
              p03VecInfNorm (run.rHat i)) /
            (1 - run.c1 i * p03KappaInf run * run.uS) :=
            (le_div_iff₀ hden).2 (by
              simpa [mul_comm] using hsolver_rearranged)
      _ = run.uS * p03CorrectionRatio run i *
            p03VecInfNorm (run.rHat i) := by
            unfold p03CorrectionRatio
            ring
  have hratio : 0 ≤ p03CorrectionRatio run i := by
    unfold p03CorrectionRatio
    exact div_nonneg (add_nonneg (mul_nonneg hc1 hkappa) hc2)
      (le_of_lt hden)

  have hdeltaX :
      p03VecInfNorm (run.deltaX i) ≤
        run.u * p03VecInfNorm (run.x (i + 1)) := by
    have hright : 0 ≤ run.u * p03VecInfNorm (run.x (i + 1)) :=
      mul_nonneg hu hxnext
    apply p03VecInfNorm_le_of_abs_le _ _ hright
    intro j
    calc
      |run.deltaX i j| ≤ run.u * |run.x (i + 1) j| :=
        run.update_error_bound i j
      _ ≤ run.u * p03VecInfNorm (run.x (i + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hu
        unfold p03VecInfNorm
        simpa using norm_le_pi_norm (run.x (i + 1)) j
  have hAdeltaX :
      p03VecInfNorm (p03MatVec run.A (run.deltaX i)) ≤
        run.u * p03MatInfNorm run.A *
          p03VecInfNorm (run.x (i + 1)) := by
    calc
      p03VecInfNorm (p03MatVec run.A (run.deltaX i)) ≤
          p03MatInfNorm run.A * p03VecInfNorm (run.deltaX i) :=
            p03VecInfNorm_matVec_le _ _
      _ ≤ p03MatInfNorm run.A *
            (run.u * p03VecInfNorm (run.x (i + 1))) :=
            mul_le_mul_of_nonneg_left hdeltaX hA
      _ = run.u * p03MatInfNorm run.A *
            p03VecInfNorm (run.x (i + 1)) := by ring

  have hnext_eq :
      p03ExactResidual run (i + 1) =
        hvec - run.deltaR i - p03MatVec run.A (run.deltaX i) := by
    funext j
    dsimp [hvec]
    unfold p03ExactResidual p03MatVec
    simp_rw [run.update_equation i]
    rw [run.residual_equation i j]
    unfold p03MatVec
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  have hnext :
      p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        p03VecInfNorm hvec + p03VecInfNorm (run.deltaR i) +
          run.u * p03MatInfNorm run.A *
            p03VecInfNorm (run.x (i + 1)) := by
    have htri :
        p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
          p03VecInfNorm hvec + p03VecInfNorm (run.deltaR i) +
            p03VecInfNorm (p03MatVec run.A (run.deltaX i)) := by
      rw [hnext_eq]
      unfold p03VecInfNorm
      exact le_trans (norm_sub_le _ _)
        (add_le_add (norm_sub_le _ _) (le_refl _))
    linarith

  have hcoef : 0 ≤ run.uS * p03CorrectionRatio run i :=
    mul_nonneg huS hratio
  have hsolver_final :
      p03VecInfNorm hvec ≤
        run.uS * p03CorrectionRatio run i *
          ((1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (p03VecInfNorm run.b +
                  p03MatInfNorm run.A * p03VecInfNorm (run.x i))) :=
    le_trans hsolver (mul_le_mul_of_nonneg_left hrHat hcoef)
  calc
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        p03VecInfNorm hvec + p03VecInfNorm (run.deltaR i) +
          run.u * p03MatInfNorm run.A *
            p03VecInfNorm (run.x (i + 1)) := hnext
    _ ≤
        run.uS * p03CorrectionRatio run i *
            ((1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
              (1 + run.uS) *
                gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                  (p03VecInfNorm run.b +
                    p03MatInfNorm run.A * p03VecInfNorm (run.x i))) +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (p03VecInfNorm run.b +
                  p03MatInfNorm run.A * p03VecInfNorm (run.x i))) +
          run.u * p03MatInfNorm run.A *
            p03VecInfNorm (run.x (i + 1)) := by
              linarith
    _ = p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
          p03Beta run i := by
          unfold p03Alpha p03Beta
          ring

end HighamBench
