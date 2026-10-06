import HighamBench.P03Definitions

namespace HighamBench

lemma p03MatVec_norm_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p03VecInfNorm (p03MatVec A x) ≤
      p03MatInfNorm A * p03VecInfNorm x := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  simpa [p03VecInfNorm, p03MatInfNorm, p03MatVec, Matrix.mulVec,
    dotProduct] using
    (Matrix.linfty_opNorm_mulVec (Matrix.of A) x)

lemma p03AbsMatVec_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (j : Fin n) :
    p03MatVec (p03MatAbs A) (p03VecAbs x) j ≤
      p03MatInfNorm A * p03VecInfNorm x := by
  have hcomp :
      |p03MatVec (p03MatAbs A) (p03VecAbs x) j| ≤
        p03VecInfNorm (p03MatVec (p03MatAbs A) (p03VecAbs x)) := by
    simpa [p03VecInfNorm, Real.norm_eq_abs] using
      (norm_le_pi_norm
        (p03MatVec (p03MatAbs A) (p03VecAbs x)) j)
  have hop := p03MatVec_norm_le (p03MatAbs A) (p03VecAbs x)
  have hmat : p03MatInfNorm (p03MatAbs A) = p03MatInfNorm A := by
    simp [p03MatInfNorm, Matrix.linfty_opNorm_def, p03MatAbs,
      Real.norm_eq_abs]
  have hvec : p03VecInfNorm (p03VecAbs x) = p03VecInfNorm x := by
    simp [p03VecInfNorm, p03VecAbs, Pi.norm_def, Real.norm_eq_abs]
  have hnonneg : 0 ≤ p03MatVec (p03MatAbs A) (p03VecAbs x) j := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [abs_of_nonneg hnonneg] at hcomp
  rw [hmat, hvec] at hop
  exact hcomp.trans hop

lemma p03MatInfNorm_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    0 ≤ p03MatInfNorm A := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  exact norm_nonneg _

theorem p03_t3_normwise_residual_contraction
    {n : ℕ} (run : P03NormwiseIRRun n) (i : ℕ) :
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
      p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
  -- PROOF_START P03-T3-H001
  let R := p03VecInfNorm (p03ExactResidual run i)
  let H := p03VecInfNorm
    (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j)
  let D := p03VecInfNorm (run.dHat i)
  let RH := p03VecInfNorm (run.rHat i)
  let dR := p03VecInfNorm (run.deltaR i)
  let dX := p03VecInfNorm (run.deltaX i)
  let AN := p03MatInfNorm run.A
  let AIN := p03MatInfNorm run.Ainv
  let BN := p03VecInfNorm run.b
  let XN := p03VecInfNorm (run.x i)
  let XN1 := p03VecInfNorm (run.x (i + 1))
  let G := (1 + run.uS) *
    gamma run.uR (p03MaxAugmentedRowNnz run.A run.b)
  let E := G * (BN + AN * XN)
  let Q := p03CorrectionRatio run i

  have hu : 0 ≤ run.u :=
    run.uR_nonneg.trans (run.uR_le_u)
  have huS : 0 ≤ run.uS :=
    hu.trans run.u_le_uS
  have hgamma :
      0 ≤ gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) := by
    unfold gamma
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) run.uR_nonneg
    · exact le_of_lt (sub_pos.mpr run.gamma_valid)
  have hG : 0 ≤ G := by
    exact mul_nonneg (by linarith) hgamma
  have hAN : 0 ≤ AN := by
    exact p03MatInfNorm_nonneg run.A
  have hAIN : 0 ≤ AIN := by
    exact p03MatInfNorm_nonneg run.Ainv
  have hR : 0 ≤ R := by
    exact norm_nonneg _
  have hH : 0 ≤ H := by
    exact norm_nonneg _
  have hRH : 0 ≤ RH := by
    exact norm_nonneg _
  have hdR_nonneg : 0 ≤ dR := by
    exact norm_nonneg _
  have hBN : 0 ≤ BN := by
    exact norm_nonneg _
  have hXN : 0 ≤ XN := by
    exact norm_nonneg _
  have hXN1 : 0 ≤ XN1 := by
    exact norm_nonneg _
  have hE : 0 ≤ E := by
    exact mul_nonneg hG (add_nonneg hBN (mul_nonneg hAN hXN))

  have hdR_bound : dR ≤ run.uS * R + E := by
    rw [show dR = ‖run.deltaR i‖ by rfl]
    apply (pi_norm_le_iff_of_nonneg
      (add_nonneg (mul_nonneg huS hR) hE)).2
    intro j
    rw [Real.norm_eq_abs]
    have hrj : |p03ExactResidual run i j| ≤ R := by
      simpa [R, p03VecInfNorm, Real.norm_eq_abs] using
        (norm_le_pi_norm (p03ExactResidual run i) j)
    have hbj : |run.b j| ≤ BN := by
      simpa [BN, p03VecInfNorm, Real.norm_eq_abs] using
        (norm_le_pi_norm run.b j)
    have hmx :
        p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j ≤
          AN * XN := by
      simpa [AN, XN] using p03AbsMatVec_le run.A (run.x i) j
    have hfirst := mul_le_mul_of_nonneg_left hrj huS
    have hsecond := mul_le_mul_of_nonneg_left (add_le_add hbj hmx) hG
    calc
      |run.deltaR i j| ≤
          run.uS * |run.b j - p03MatVec run.A (run.x i) j| +
            (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (|run.b j| +
                  p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j) :=
        run.residual_error_bound i j
      _ ≤ run.uS * R + G * (BN + AN * XN) := by
        simpa [p03ExactResidual, G] using add_le_add hfirst hsecond
      _ = run.uS * R + E := by rfl

  have hdX_bound : dX ≤ run.u * XN1 := by
    rw [show dX = ‖run.deltaX i‖ by rfl]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hu hXN1)).2
    intro j
    have hxj : |run.x (i + 1) j| ≤ XN1 := by
      simpa [XN1, p03VecInfNorm, Real.norm_eq_abs] using
        (norm_le_pi_norm (run.x (i + 1)) j)
    calc
      ‖run.deltaX i j‖ = |run.deltaX i j| := Real.norm_eq_abs _
      _ ≤ run.u * |run.x (i + 1) j| := run.update_error_bound i j
      _ ≤ run.u * XN1 := mul_le_mul_of_nonneg_left hxj hu

  have hd_inverse :
      run.dHat i = p03MatVec run.Ainv (p03MatVec run.A (run.dHat i)) := by
    funext j
    exact (run.inverse_action (run.dHat i) j).symm
  have hAd_split :
      p03MatVec run.A (run.dHat i) =
        fun j => run.rHat i j -
          (run.rHat i j - p03MatVec run.A (run.dHat i) j) := by
    funext j
    ring
  have hAd_bound :
      p03VecInfNorm (p03MatVec run.A (run.dHat i)) ≤ RH + H := by
    rw [hAd_split]
    change
      ‖run.rHat i -
          (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j)‖ ≤
        ‖run.rHat i‖ +
          ‖fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j‖
    exact norm_sub_le _ _
  have hD_bound : D ≤ AIN * (RH + H) := by
    calc
      D = p03VecInfNorm
          (p03MatVec run.Ainv (p03MatVec run.A (run.dHat i))) := by
            exact congrArg p03VecInfNorm hd_inverse
      _ ≤ AIN * p03VecInfNorm (p03MatVec run.A (run.dHat i)) := by
            simpa [AIN] using
              p03MatVec_norm_le run.Ainv (p03MatVec run.A (run.dHat i))
      _ ≤ AIN * (RH + H) :=
            mul_le_mul_of_nonneg_left hAd_bound hAIN

  have hc1 : 0 ≤ run.c1 i := run.c1_nonneg i
  have hc2 : 0 ≤ run.c2 i := run.c2_nonneg i
  have hsolver :
      H ≤ run.uS * (run.c1 i * AN * D + run.c2 i * RH) := by
    exact run.correction_solver_bound i
  have hDterm :
      run.c1 i * AN * D ≤
        run.c1 i * AN * (AIN * (RH + H)) :=
    mul_le_mul_of_nonneg_left hD_bound (mul_nonneg hc1 hAN)
  have hsolver' :
      H ≤ run.uS *
        (run.c1 i * AN * (AIN * (RH + H)) + run.c2 i * RH) := by
    exact hsolver.trans
      (mul_le_mul_of_nonneg_left (add_le_add hDterm le_rfl) huS)
  have hden :
      0 < 1 - run.c1 i * (AIN * AN) * run.uS := by
    apply sub_pos.mpr
    simpa [AIN, AN, p03KappaInf] using run.denominator_condition i
  have hQ_formula :
      Q = (run.c1 i * (AIN * AN) + run.c2 i) /
        (1 - run.c1 i * (AIN * AN) * run.uS) := by
    rfl
  have hQ : 0 ≤ Q := by
    rw [hQ_formula]
    exact div_nonneg
      (add_nonneg (mul_nonneg hc1 (mul_nonneg hAIN hAN)) hc2)
      (le_of_lt hden)
  have hH_bound : H ≤ run.uS * Q * RH := by
    rw [hQ_formula]
    rw [show
      run.uS *
          ((run.c1 i * (AIN * AN) + run.c2 i) /
            (1 - run.c1 i * (AIN * AN) * run.uS)) * RH =
        (run.uS * (run.c1 i * (AIN * AN) + run.c2 i) * RH) /
          (1 - run.c1 i * (AIN * AN) * run.uS) by ring]
    apply (le_div_iff₀ hden).2
    nlinarith [hsolver']

  have hrHat_eq :
      run.rHat i = p03ExactResidual run i + run.deltaR i := by
    funext j
    simpa [p03ExactResidual] using run.residual_equation i j
  have hRH_bound : RH ≤ R + dR := by
    rw [show RH = ‖run.rHat i‖ by rfl, hrHat_eq]
    exact norm_add_le _ _
  have hcoef : 0 ≤ run.uS * Q := mul_nonneg huS hQ
  have hH_residual : H ≤ run.uS * Q * (R + dR) :=
    hH_bound.trans (mul_le_mul_of_nonneg_left hRH_bound hcoef)

  have hAdX_bound :
      p03VecInfNorm (p03MatVec run.A (run.deltaX i)) ≤
        run.u * AN * XN1 := by
    calc
      p03VecInfNorm (p03MatVec run.A (run.deltaX i)) ≤ AN * dX := by
        simpa [AN, dX] using p03MatVec_norm_le run.A (run.deltaX i)
      _ ≤ AN * (run.u * XN1) :=
        mul_le_mul_of_nonneg_left hdX_bound hAN
      _ = run.u * AN * XN1 := by ring

  have hresidual_eq :
      p03ExactResidual run (i + 1) =
        fun j =>
          (run.rHat i j - p03MatVec run.A (run.dHat i) j) -
            run.deltaR i j - p03MatVec run.A (run.deltaX i) j := by
    funext j
    unfold p03ExactResidual p03MatVec
    simp_rw [run.update_equation i, mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [run.residual_equation i j]
    unfold p03MatVec
    ring
  have hnew_residual :
      p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        H + dR + run.u * AN * XN1 := by
    rw [hresidual_eq]
    change
      ‖((fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) -
          run.deltaR i) - p03MatVec run.A (run.deltaX i)‖ ≤
        H + dR + run.u * AN * XN1
    calc
      ‖((fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) -
          run.deltaR i) - p03MatVec run.A (run.deltaX i)‖ ≤
          ‖(fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) -
              run.deltaR i‖ +
            ‖p03MatVec run.A (run.deltaX i)‖ := norm_sub_le _ _
      _ ≤ (H + dR) +
          p03VecInfNorm (p03MatVec run.A (run.deltaX i)) := by
        have hhd :
            ‖(fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) -
                run.deltaR i‖ ≤ H + dR := by
          simpa [H, dR, p03VecInfNorm] using
            (norm_sub_le
              (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j)
              (run.deltaR i))
        exact add_le_add_left hhd _
      _ ≤ H + dR + run.u * AN * XN1 :=
        add_le_add_right hAdX_bound _

  have hreplace_inside :
      run.uS * Q * (R + dR) ≤
        run.uS * Q * (R + (run.uS * R + E)) := by
    have hinside : R + dR ≤ R + (run.uS * R + E) := by
      linarith [hdR_bound]
    exact mul_le_mul_of_nonneg_left hinside hcoef
  calc
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        H + dR + run.u * AN * XN1 := hnew_residual
    _ ≤ run.uS * Q * (R + dR) + dR + run.u * AN * XN1 := by
      linarith [hH_residual]
    _ ≤ run.uS * Q * (R + (run.uS * R + E)) +
          (run.uS * R + E) + run.u * AN * XN1 := by
      linarith [hreplace_inside, hdR_bound]
    _ = p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
          p03Beta run i := by
      simp [p03Alpha, p03Beta, R, E, G, AN, BN, XN, XN1, Q]
      ring

end HighamBench
