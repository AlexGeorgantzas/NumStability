import HighamBench.P03Definitions

namespace HighamBench

lemma p03MatVec_norm_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03VecInfNorm (p03MatVec A x) ≤
      p03MatInfNorm A * p03VecInfNorm x := by
  classical
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  simpa [p03VecInfNorm, p03MatInfNorm, p03MatVec, Matrix.mulVec,
    dotProduct] using
    (Matrix.linfty_opNorm_mulVec (Matrix.of A) x)

lemma p03MatInfNorm_abs {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatInfNorm (p03MatAbs A) = p03MatInfNorm A := by
  classical
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  simp only [p03MatInfNorm, Matrix.linfty_opNorm_def, p03MatAbs,
    Matrix.of_apply, Real.nnnorm_abs]

lemma p03MatInfNorm_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    0 ≤ p03MatInfNorm A := by
  classical
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  exact norm_nonneg _

lemma p03VecInfNorm_abs {n : ℕ} (x : Fin n → ℝ) :
    p03VecInfNorm (p03VecAbs x) = p03VecInfNorm x := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_
    intro j
    simpa [p03VecAbs] using (norm_le_pi_norm x j)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg (p03VecAbs x))).2 ?_
    intro j
    simpa [p03VecAbs] using (norm_le_pi_norm (p03VecAbs x) j)

lemma p03AbsMatVec_norm_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03VecInfNorm (p03MatVec (p03MatAbs A) (p03VecAbs x)) ≤
      p03MatInfNorm A * p03VecInfNorm x := by
  simpa [p03MatInfNorm_abs, p03VecInfNorm_abs] using
    p03MatVec_norm_le (p03MatAbs A) (p03VecAbs x)

lemma p03AbsMatVec_apply_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (j : Fin n) :
    p03MatVec (p03MatAbs A) (p03VecAbs x) j ≤
      p03MatInfNorm A * p03VecInfNorm x := by
  have hnonneg :
      0 ≤ p03MatVec (p03MatAbs A) (p03VecAbs x) j := by
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc
    p03MatVec (p03MatAbs A) (p03VecAbs x) j =
        ‖p03MatVec (p03MatAbs A) (p03VecAbs x) j‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ ≤ p03VecInfNorm
          (p03MatVec (p03MatAbs A) (p03VecAbs x)) := by
          exact norm_le_pi_norm _ j
    _ ≤ p03MatInfNorm A * p03VecInfNorm x :=
      p03AbsMatVec_norm_le A x

theorem p03_t3_normwise_residual_contraction
    {n : ℕ} (run : P03NormwiseIRRun n) (i : ℕ) :
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
      p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
  -- PROOF_START P03-T3-H001
  have huS : 0 ≤ run.uS :=
    le_trans (le_trans run.uR_nonneg run.uR_le_u) run.u_le_uS
  have hu : 0 ≤ run.u := le_trans run.uR_nonneg run.uR_le_u
  have hgamma :
      0 ≤ gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) := by
    rw [gamma]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) run.uR_nonneg)
      (le_of_lt (sub_pos.mpr run.gamma_valid))
  have hresidual_error :
      p03VecInfNorm (run.deltaR i) ≤
        run.uS * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
            (p03VecInfNorm run.b +
              p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
    refine (pi_norm_le_iff_of_nonneg ?_).2 ?_
    · apply add_nonneg
      · exact mul_nonneg huS (norm_nonneg _)
      · apply mul_nonneg
        · exact mul_nonneg (by linarith) hgamma
        · exact add_nonneg (norm_nonneg _)
            (mul_nonneg (p03MatInfNorm_nonneg _) (norm_nonneg _))
    · intro j
      change |run.deltaR i j| ≤ _
      calc
        |run.deltaR i j| ≤
            run.uS * |run.b j - p03MatVec run.A (run.x i) j| +
              (1 + run.uS) *
                  gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (|run.b j| +
                  p03MatVec (p03MatAbs run.A)
                    (p03VecAbs (run.x i)) j) :=
          run.residual_error_bound i j
        _ ≤
            run.uS * p03VecInfNorm (p03ExactResidual run i) +
              (1 + run.uS) *
                  gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (p03VecInfNorm run.b +
                  p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
          gcongr
          · simpa [p03ExactResidual, p03VecInfNorm,
              Real.norm_eq_abs] using
              (norm_le_pi_norm (p03ExactResidual run i) j)
          · simpa [p03VecInfNorm, Real.norm_eq_abs] using
              (norm_le_pi_norm run.b j)
          · exact p03AbsMatVec_apply_le run.A (run.x i) j
  have hupdate_error :
      p03VecInfNorm (run.deltaX i) ≤
        run.u * p03VecInfNorm (run.x (i + 1)) := by
    refine (pi_norm_le_iff_of_nonneg ?_).2 ?_
    · exact mul_nonneg hu (norm_nonneg _)
    · intro j
      change |run.deltaX i j| ≤
        run.u * p03VecInfNorm (run.x (i + 1))
      calc
        |run.deltaX i j| ≤ run.u * |run.x (i + 1) j| :=
          run.update_error_bound i j
        _ ≤ run.u * p03VecInfNorm (run.x (i + 1)) := by
          gcongr
          simpa [p03VecInfNorm, Real.norm_eq_abs] using
            (norm_le_pi_norm (run.x (i + 1)) j)
  let h : Fin n → ℝ :=
    fun j ↦ run.rHat i j - p03MatVec run.A (run.dHat i) j
  have hsolver :
      p03VecInfNorm h ≤
        run.uS *
          (run.c1 i * p03MatInfNorm run.A *
              p03VecInfNorm (run.dHat i) +
            run.c2 i * p03VecInfNorm (run.rHat i)) := by
    simpa [h] using run.correction_solver_bound i
  have hd_identity :
      run.dHat i =
        p03MatVec run.Ainv (fun j ↦ run.rHat i j - h j) := by
    funext j
    simpa [h] using (run.inverse_action (run.dHat i) j).symm
  have hd_bound :
      p03VecInfNorm (run.dHat i) ≤
        p03MatInfNorm run.Ainv *
          (p03VecInfNorm (run.rHat i) + p03VecInfNorm h) := by
    calc
      p03VecInfNorm (run.dHat i) =
          p03VecInfNorm
            (p03MatVec run.Ainv (fun j ↦ run.rHat i j - h j)) := by
            rw [hd_identity]
      _ ≤ p03MatInfNorm run.Ainv *
          p03VecInfNorm (fun j ↦ run.rHat i j - h j) :=
        p03MatVec_norm_le run.Ainv _
      _ ≤ p03MatInfNorm run.Ainv *
          (p03VecInfNorm (run.rHat i) + p03VecInfNorm h) := by
        apply mul_le_mul_of_nonneg_left
        · exact norm_sub_le _ _
        · exact p03MatInfNorm_nonneg _
  have hkappa_nonneg : 0 ≤ p03KappaInf run := by
    exact mul_nonneg (p03MatInfNorm_nonneg _) (p03MatInfNorm_nonneg _)
  have hdenom :
      0 < 1 - run.c1 i * p03KappaInf run * run.uS := by
    exact sub_pos.mpr (by
      simpa [p03KappaInf] using run.denominator_condition i)
  have hratio_nonneg : 0 ≤ p03CorrectionRatio run i := by
    rw [p03CorrectionRatio]
    exact div_nonneg
      (add_nonneg (mul_nonneg (run.c1_nonneg i) hkappa_nonneg)
        (run.c2_nonneg i))
      hdenom.le
  have hsolver_expanded :
      p03VecInfNorm h ≤
        run.uS *
          ((run.c1 i * p03KappaInf run + run.c2 i) *
              p03VecInfNorm (run.rHat i) +
            run.c1 i * p03KappaInf run * p03VecInfNorm h) := by
    calc
      p03VecInfNorm h ≤
          run.uS *
            (run.c1 i * p03MatInfNorm run.A *
                p03VecInfNorm (run.dHat i) +
              run.c2 i * p03VecInfNorm (run.rHat i)) := hsolver
      _ ≤ run.uS *
            (run.c1 i * p03MatInfNorm run.A *
                (p03MatInfNorm run.Ainv *
                  (p03VecInfNorm (run.rHat i) + p03VecInfNorm h)) +
              run.c2 i * p03VecInfNorm (run.rHat i)) := by
          gcongr
          exact mul_nonneg (run.c1_nonneg i) (p03MatInfNorm_nonneg _)
      _ = run.uS *
          ((run.c1 i * p03KappaInf run + run.c2 i) *
              p03VecInfNorm (run.rHat i) +
            run.c1 i * p03KappaInf run * p03VecInfNorm h) := by
          rw [p03KappaInf]
          ring
  have hcorrection :
      p03VecInfNorm h ≤
        run.uS * p03CorrectionRatio run i *
          p03VecInfNorm (run.rHat i) := by
    rw [p03CorrectionRatio]
    rw [show
      run.uS *
            ((run.c1 i * p03KappaInf run + run.c2 i) /
              (1 - run.c1 i * p03KappaInf run * run.uS)) *
            p03VecInfNorm (run.rHat i) =
          (run.uS * (run.c1 i * p03KappaInf run + run.c2 i) *
              p03VecInfNorm (run.rHat i)) /
            (1 - run.c1 i * p03KappaInf run * run.uS) by ring]
    apply (le_div_iff₀ hdenom).2
    nlinarith [hsolver_expanded]
  have hrHat :
      p03VecInfNorm (run.rHat i) ≤
        (1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
            (p03VecInfNorm run.b +
              p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
    calc
      p03VecInfNorm (run.rHat i) =
          p03VecInfNorm
            (fun j ↦ p03ExactResidual run i j + run.deltaR i j) := by
            congr 1
            funext j
            exact run.residual_equation i j
      _ ≤ p03VecInfNorm (p03ExactResidual run i) +
          p03VecInfNorm (run.deltaR i) := norm_add_le _ _
      _ ≤ p03VecInfNorm (p03ExactResidual run i) +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
                gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i))) := by
          gcongr
      _ = (1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
            (p03VecInfNorm run.b +
              p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by ring
  have hnext_identity :
      p03ExactResidual run (i + 1) =
        fun j ↦ h j - run.deltaR i j -
          p03MatVec run.A (run.deltaX i) j := by
    funext j
    simp only [p03ExactResidual, p03MatVec]
    have hxupdate : run.x (i + 1) =
        fun k ↦ run.x i k + run.dHat i k + run.deltaX i k := by
      funext k
      exact run.update_equation i k
    rw [hxupdate]
    simp only [h, p03MatVec]
    rw [run.residual_equation i j]
    simp only [p03MatVec]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  calc
    p03VecInfNorm (p03ExactResidual run (i + 1)) =
        p03VecInfNorm
          (fun j ↦ h j - run.deltaR i j -
            p03MatVec run.A (run.deltaX i) j) := by rw [hnext_identity]
    _ ≤ p03VecInfNorm (fun j ↦ h j - run.deltaR i j) +
        p03VecInfNorm (p03MatVec run.A (run.deltaX i)) :=
      norm_sub_le _ _
    _ ≤ (p03VecInfNorm h + p03VecInfNorm (run.deltaR i)) +
        p03VecInfNorm (p03MatVec run.A (run.deltaX i)) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (p03VecInfNorm h + p03VecInfNorm (run.deltaR i)) +
        p03MatInfNorm run.A * p03VecInfNorm (run.deltaX i) := by
      gcongr
      exact p03MatVec_norm_le run.A (run.deltaX i)
    _ ≤
        (run.uS * p03CorrectionRatio run i *
            p03VecInfNorm (run.rHat i) +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
                gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i)))) +
          p03MatInfNorm run.A *
            (run.u * p03VecInfNorm (run.x (i + 1))) := by
      apply add_le_add
      · exact add_le_add hcorrection hresidual_error
      · exact mul_le_mul_of_nonneg_left hupdate_error
          (p03MatInfNorm_nonneg _)
    _ ≤
        (run.uS * p03CorrectionRatio run i *
            ((1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
              (1 + run.uS) *
                  gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
                (p03VecInfNorm run.b +
                  p03MatInfNorm run.A * p03VecInfNorm (run.x i))) +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
                gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i)))) +
          p03MatInfNorm run.A *
            (run.u * p03VecInfNorm (run.x (i + 1))) := by
      gcongr
    _ = p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
      rw [p03Alpha, p03Beta]
      ring

end HighamBench
