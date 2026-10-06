import HighamBench.P03Definitions

namespace HighamBench

lemma p03MatVec_norm_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03VecInfNorm (p03MatVec A x) ≤
      p03MatInfNorm A * p03VecInfNorm x := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  simpa [p03VecInfNorm, p03MatVec, Matrix.mulVec, p03MatInfNorm] using
    (Matrix.linfty_opNorm_mulVec (Matrix.of A) x)

@[simp] lemma p03VecInfNorm_abs {n : ℕ} (x : Fin n → ℝ) :
    p03VecInfNorm (p03VecAbs x) = p03VecInfNorm x := by
  simp [p03VecInfNorm, p03VecAbs, Pi.norm_def]

@[simp] lemma p03MatInfNorm_abs {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatInfNorm (p03MatAbs A) = p03MatInfNorm A := by
  simp [p03MatInfNorm, p03MatAbs, Matrix.linfty_opNorm_def]

lemma p03VecInfNorm_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ p03VecInfNorm x := by
  exact norm_nonneg _

lemma p03MatInfNorm_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    0 ≤ p03MatInfNorm A := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  exact norm_nonneg (Matrix.of A)

theorem p03_t3_normwise_residual_contraction
    {n : ℕ} (run : P03NormwiseIRRun n) (i : ℕ) :
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
      p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
  -- PROOF_START P03-T3-H001
  have hu : 0 ≤ run.u := le_trans run.uR_nonneg run.uR_le_u
  have huS : 0 ≤ run.uS := le_trans hu run.u_le_uS
  have hgamma :
      0 ≤ gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) := by
    rw [gamma]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) run.uR_nonneg)
      (sub_nonneg.mpr (le_of_lt run.gamma_valid))
  have hkappa : 0 ≤ p03KappaInf run := by
    exact mul_nonneg (p03MatInfNorm_nonneg _) (p03MatInfNorm_nonneg _)
  have hden :
      0 < 1 - run.c1 i * p03KappaInf run * run.uS := by
    exact sub_pos.mpr (by
      simpa [p03KappaInf] using run.denominator_condition i)
  have hratio : 0 ≤ p03CorrectionRatio run i := by
    rw [p03CorrectionRatio]
    exact div_nonneg
      (add_nonneg (mul_nonneg (run.c1_nonneg i) hkappa)
        (run.c2_nonneg i))
      hden.le

  have hres_component (j : Fin n) :
      |p03ExactResidual run i j| ≤
        p03VecInfNorm (p03ExactResidual run i) := by
    simpa [p03VecInfNorm, Real.norm_eq_abs] using
      (norm_le_pi_norm (p03ExactResidual run i) j)
  have hb_component (j : Fin n) :
      |run.b j| ≤ p03VecInfNorm run.b := by
    simpa [p03VecInfNorm, Real.norm_eq_abs] using
      (norm_le_pi_norm run.b j)
  have hrow (j : Fin n) :
      p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j ≤
        p03MatInfNorm run.A * p03VecInfNorm (run.x i) := by
    have hrow_nonneg :
        0 ≤ p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hcomponent :=
      norm_le_pi_norm
        (p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i))) j
    rw [Real.norm_eq_abs, abs_of_nonneg hrow_nonneg] at hcomponent
    calc
      p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j ≤
          p03VecInfNorm
            (p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i))) := by
        simpa [p03VecInfNorm] using hcomponent
      _ ≤ p03MatInfNorm (p03MatAbs run.A) *
          p03VecInfNorm (p03VecAbs (run.x i)) :=
        p03MatVec_norm_le _ _
      _ = p03MatInfNorm run.A * p03VecInfNorm (run.x i) := by simp

  have hdeltaR :
      p03VecInfNorm (run.deltaR i) ≤
        run.uS * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
            gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
    have hbound_nonneg :
        0 ≤ run.uS * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
            gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
      exact add_nonneg
        (mul_nonneg huS (p03VecInfNorm_nonneg _))
        (mul_nonneg
          (mul_nonneg (by linarith) hgamma)
          (add_nonneg (p03VecInfNorm_nonneg _)
            (mul_nonneg (p03MatInfNorm_nonneg _)
              (p03VecInfNorm_nonneg _))))
    rw [p03VecInfNorm, pi_norm_le_iff_of_nonneg hbound_nonneg]
    intro j
    rw [Real.norm_eq_abs]
    calc
      |run.deltaR i j| ≤
          run.uS * |run.b j - p03MatVec run.A (run.x i) j| +
            (1 + run.uS) *
                gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (|run.b j| +
                p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j) :=
        run.residual_error_bound i j
      _ ≤ run.uS * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
            gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
        have hrj :
            |run.b j - p03MatVec run.A (run.x i) j| ≤
              p03VecInfNorm (p03ExactResidual run i) := by
          simpa [p03ExactResidual] using hres_component j
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hrj huS
        · apply mul_le_mul_of_nonneg_left
          · exact add_le_add (hb_component j) (hrow j)
          · exact mul_nonneg (by linarith) hgamma

  have hdeltaX :
      p03VecInfNorm (run.deltaX i) ≤
        run.u * p03VecInfNorm (run.x (i + 1)) := by
    rw [p03VecInfNorm, pi_norm_le_iff_of_nonneg
      (mul_nonneg hu (p03VecInfNorm_nonneg _))]
    intro j
    rw [Real.norm_eq_abs]
    calc
      |run.deltaX i j| ≤ run.u * |run.x (i + 1) j| :=
        run.update_error_bound i j
      _ ≤ run.u * p03VecInfNorm (run.x (i + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hu
        simpa [p03VecInfNorm, Real.norm_eq_abs] using
          (norm_le_pi_norm (run.x (i + 1)) j)

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
    rw [hrHat_eq]
    calc
      p03VecInfNorm (p03ExactResidual run i + run.deltaR i) ≤
          p03VecInfNorm (p03ExactResidual run i) +
            p03VecInfNorm (run.deltaR i) := norm_add_le _ _
      _ ≤ p03VecInfNorm (p03ExactResidual run i) +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (p03VecInfNorm run.b +
                  p03MatInfNorm run.A * p03VecInfNorm (run.x i))) :=
        add_le_add (le_refl _) hdeltaR
      _ = (1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
            gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by ring

  let h : Fin n → ℝ :=
    fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j
  have hh_solver :
      p03VecInfNorm h ≤
        run.uS *
          (run.c1 i * p03MatInfNorm run.A *
              p03VecInfNorm (run.dHat i) +
            run.c2 i * p03VecInfNorm (run.rHat i)) := by
    simpa [h] using run.correction_solver_bound i
  have hd_inverse :
      run.dHat i =
        p03MatVec run.Ainv (p03MatVec run.A (run.dHat i)) := by
    funext j
    exact (run.inverse_action (run.dHat i) j).symm
  have hAd_eq :
      p03MatVec run.A (run.dHat i) = run.rHat i - h := by
    funext j
    simp [h]
  have hAd :
      p03VecInfNorm (p03MatVec run.A (run.dHat i)) ≤
        p03VecInfNorm (run.rHat i) + p03VecInfNorm h := by
    rw [hAd_eq]
    exact norm_sub_le _ _
  have hd :
      p03VecInfNorm (run.dHat i) ≤
        p03MatInfNorm run.Ainv *
          (p03VecInfNorm (run.rHat i) + p03VecInfNorm h) := by
    calc
      p03VecInfNorm (run.dHat i) =
          p03VecInfNorm
            (p03MatVec run.Ainv (p03MatVec run.A (run.dHat i))) := by
        exact congrArg p03VecInfNorm hd_inverse
      _ ≤ p03MatInfNorm run.Ainv *
          p03VecInfNorm (p03MatVec run.A (run.dHat i)) :=
        p03MatVec_norm_le _ _
      _ ≤ p03MatInfNorm run.Ainv *
          (p03VecInfNorm (run.rHat i) + p03VecInfNorm h) := by
        exact mul_le_mul_of_nonneg_left hAd (p03MatInfNorm_nonneg _)
  have hh_solver' :
      p03VecInfNorm h ≤
        run.uS *
          (run.c1 i * p03KappaInf run *
              (p03VecInfNorm (run.rHat i) + p03VecInfNorm h) +
            run.c2 i * p03VecInfNorm (run.rHat i)) := by
    calc
      p03VecInfNorm h ≤
          run.uS *
            (run.c1 i * p03MatInfNorm run.A *
                p03VecInfNorm (run.dHat i) +
              run.c2 i * p03VecInfNorm (run.rHat i)) := hh_solver
      _ ≤ run.uS *
          (run.c1 i * p03MatInfNorm run.A *
              (p03MatInfNorm run.Ainv *
                (p03VecInfNorm (run.rHat i) + p03VecInfNorm h)) +
            run.c2 i * p03VecInfNorm (run.rHat i)) := by
        apply mul_le_mul_of_nonneg_left _ huS
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hd
            (mul_nonneg (run.c1_nonneg i) (p03MatInfNorm_nonneg _))
        · exact le_rfl
      _ = run.uS *
          (run.c1 i * p03KappaInf run *
              (p03VecInfNorm (run.rHat i) + p03VecInfNorm h) +
            run.c2 i * p03VecInfNorm (run.rHat i)) := by
        rw [p03KappaInf]
        ring
  have hh_prediv :
      (1 - run.c1 i * p03KappaInf run * run.uS) *
          p03VecInfNorm h ≤
        run.uS * (run.c1 i * p03KappaInf run + run.c2 i) *
          p03VecInfNorm (run.rHat i) := by
    nlinarith [hh_solver']
  have hh :
      p03VecInfNorm h ≤
        run.uS * p03CorrectionRatio run i *
          p03VecInfNorm (run.rHat i) := by
    have hdiv :
        p03VecInfNorm h ≤
          (run.uS * (run.c1 i * p03KappaInf run + run.c2 i) *
              p03VecInfNorm (run.rHat i)) /
            (1 - run.c1 i * p03KappaInf run * run.uS) := by
      apply (le_div_iff₀ hden).2
      simpa [mul_comm] using hh_prediv
    calc
      p03VecInfNorm h ≤
          (run.uS * (run.c1 i * p03KappaInf run + run.c2 i) *
              p03VecInfNorm (run.rHat i)) /
            (1 - run.c1 i * p03KappaInf run * run.uS) := hdiv
      _ = run.uS * p03CorrectionRatio run i *
          p03VecInfNorm (run.rHat i) := by
        rw [p03CorrectionRatio]
        ring

  have hnext_eq :
      p03ExactResidual run (i + 1) =
        h - run.deltaR i - p03MatVec run.A (run.deltaX i) := by
    funext j
    simp only [p03ExactResidual, h, Pi.sub_apply]
    rw [run.residual_equation i j]
    unfold p03MatVec
    simp_rw [run.update_equation i, mul_add, Finset.sum_add_distrib]
    ring
  have hnext_basic :
      p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        p03VecInfNorm h + p03VecInfNorm (run.deltaR i) +
          p03MatInfNorm run.A * p03VecInfNorm (run.deltaX i) := by
    rw [hnext_eq]
    calc
      p03VecInfNorm (h - run.deltaR i -
          p03MatVec run.A (run.deltaX i)) ≤
          p03VecInfNorm (h - run.deltaR i) +
            p03VecInfNorm (p03MatVec run.A (run.deltaX i)) :=
        norm_sub_le _ _
      _ ≤ (p03VecInfNorm h + p03VecInfNorm (run.deltaR i)) +
          p03MatInfNorm run.A * p03VecInfNorm (run.deltaX i) := by
        exact add_le_add (norm_sub_le _ _) (p03MatVec_norm_le _ _)
  have hnext :
      p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        p03VecInfNorm h +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (p03VecInfNorm run.b +
                  p03MatInfNorm run.A * p03VecInfNorm (run.x i))) +
          run.u * p03MatInfNorm run.A *
            p03VecInfNorm (run.x (i + 1)) := by
    calc
      p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
          p03VecInfNorm h + p03VecInfNorm (run.deltaR i) +
            p03MatInfNorm run.A * p03VecInfNorm (run.deltaX i) := hnext_basic
      _ ≤ p03VecInfNorm h +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (p03VecInfNorm run.b +
                  p03MatInfNorm run.A * p03VecInfNorm (run.x i))) +
          p03MatInfNorm run.A *
            (run.u * p03VecInfNorm (run.x (i + 1))) := by
        apply add_le_add
        · exact add_le_add (le_refl _) hdeltaR
        · exact mul_le_mul_of_nonneg_left hdeltaX
            (p03MatInfNorm_nonneg _)
      _ = p03VecInfNorm h +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (p03VecInfNorm run.b +
                  p03MatInfNorm run.A * p03VecInfNorm (run.x i))) +
          run.u * p03MatInfNorm run.A *
            p03VecInfNorm (run.x (i + 1)) := by ring
  have hh_full :
      p03VecInfNorm h ≤
        run.uS * p03CorrectionRatio run i *
          ((1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (p03VecInfNorm run.b +
                  p03MatInfNorm run.A * p03VecInfNorm (run.x i))) := by
    exact hh.trans (mul_le_mul_of_nonneg_left hrHat
      (mul_nonneg huS hratio))
  calc
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
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
      nlinarith [hnext, hh_full]
    _ = p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
      rw [p03Alpha, p03Beta]
      ring

end HighamBench
