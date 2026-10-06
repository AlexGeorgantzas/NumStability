import HighamBench.P03Definitions

namespace HighamBench

lemma p03VecInfNorm_le_of_abs_le {n : ℕ} {v : Fin n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ j, |v j| ≤ C) : p03VecInfNorm v ≤ C := by
  rw [p03VecInfNorm]
  exact (pi_norm_le_iff_of_nonneg hC).2 fun j => by
    simpa [Real.norm_eq_abs] using h j

lemma p03MatVec_norm_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) :
    p03VecInfNorm (p03MatVec A v) ≤
      p03MatInfNorm A * p03VecInfNorm v := by
  unfold p03VecInfNorm p03MatInfNorm
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  exact Matrix.linfty_opNorm_mulVec (Matrix.of A) v

lemma p03MatInfNorm_abs {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatInfNorm (p03MatAbs A) = p03MatInfNorm A := by
  unfold p03MatInfNorm p03MatAbs
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  simp only [Matrix.linfty_opNorm_def, Matrix.of_apply, Real.nnnorm_abs]

lemma p03VecInfNorm_abs {n : ℕ} (v : Fin n → ℝ) :
    p03VecInfNorm (p03VecAbs v) = p03VecInfNorm v := by
  unfold p03VecInfNorm p03VecAbs
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2
    intro j
    simpa [Real.norm_eq_abs] using norm_le_pi_norm v j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg fun j => |v j|)).2
    intro j
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun j => |v j|) j

lemma p03VecInfNorm_nonneg {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ p03VecInfNorm v := by
  exact norm_nonneg v

lemma p03MatInfNorm_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    0 ≤ p03MatInfNorm A := by
  unfold p03MatInfNorm
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  exact norm_nonneg (Matrix.of A)

theorem p03_t3_normwise_residual_contraction
    {n : ℕ} (run : P03NormwiseIRRun n) (i : ℕ) :
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
      p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
  -- PROOF_START P03-T3-H001
  let h : Fin n → ℝ := fun j =>
    run.rHat i j - p03MatVec run.A (run.dHat i) j
  let g : ℝ :=
    (1 + run.uS) * gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
      (p03VecInfNorm run.b +
        p03MatInfNorm run.A * p03VecInfNorm (run.x i))

  have hu : 0 ≤ run.u := run.uR_nonneg.trans run.uR_le_u
  have huS : 0 ≤ run.uS := hu.trans run.u_le_uS
  have hgamma :
      0 ≤ gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) := by
    unfold gamma
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) run.uR_nonneg)
      (sub_nonneg.mpr (le_of_lt run.gamma_valid))
  have hg : 0 ≤ g := by
    dsimp [g]
    exact mul_nonneg (mul_nonneg (add_nonneg zero_le_one huS) hgamma)
      (add_nonneg (p03VecInfNorm_nonneg _)
        (mul_nonneg (p03MatInfNorm_nonneg _) (p03VecInfNorm_nonneg _)))
  have hkappa : 0 ≤ p03KappaInf run := by
    unfold p03KappaInf
    exact mul_nonneg (p03MatInfNorm_nonneg _) (p03MatInfNorm_nonneg _)
  have hden :
      0 < 1 - run.c1 i * p03KappaInf run * run.uS := by
    exact sub_pos.mpr (by
      simpa only [p03KappaInf] using run.denominator_condition i)
  have hratio : 0 ≤ p03CorrectionRatio run i := by
    unfold p03CorrectionRatio
    exact div_nonneg
      (add_nonneg (mul_nonneg (run.c1_nonneg i) hkappa)
        (run.c2_nonneg i))
      hden.le

  have hmat_component (j : Fin n) :
      p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j ≤
        p03MatInfNorm run.A * p03VecInfNorm (run.x i) := by
    calc
      p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j ≤
          |p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j| :=
        le_abs_self _
      _ = ‖p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ p03VecInfNorm
          (p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i))) := by
        exact norm_le_pi_norm _ j
      _ ≤ p03MatInfNorm (p03MatAbs run.A) *
          p03VecInfNorm (p03VecAbs (run.x i)) :=
        p03MatVec_norm_le _ _
      _ = p03MatInfNorm run.A * p03VecInfNorm (run.x i) := by
        rw [p03MatInfNorm_abs, p03VecInfNorm_abs]

  have hdr_point (j : Fin n) :
      |run.deltaR i j| ≤
        run.uS * |p03ExactResidual run i j| + g := by
    calc
      |run.deltaR i j| ≤
          run.uS * |run.b j - p03MatVec run.A (run.x i) j| +
            (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (|run.b j| +
                p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j) :=
        run.residual_error_bound i j
      _ ≤ run.uS * |p03ExactResidual run i j| + g := by
        dsimp [p03ExactResidual, g]
        gcongr
        · simpa [Real.norm_eq_abs] using norm_le_pi_norm run.b j
        · exact hmat_component j
  have hdr :
      p03VecInfNorm (run.deltaR i) ≤
        run.uS * p03VecInfNorm (p03ExactResidual run i) + g := by
    apply p03VecInfNorm_le_of_abs_le
    · exact add_nonneg
        (mul_nonneg huS (p03VecInfNorm_nonneg _)) hg
    intro j
    calc
      |run.deltaR i j| ≤
          run.uS * |p03ExactResidual run i j| + g := hdr_point j
      _ ≤ run.uS * p03VecInfNorm (p03ExactResidual run i) + g := by
        gcongr
        simpa [Real.norm_eq_abs] using
          norm_le_pi_norm (p03ExactResidual run i) j

  have hrhat_eq :
      run.rHat i = fun j =>
        p03ExactResidual run i j + run.deltaR i j := by
    funext j
    exact run.residual_equation i j
  have hrhat :
      p03VecInfNorm (run.rHat i) ≤
        (1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) + g := by
    calc
      p03VecInfNorm (run.rHat i) =
          p03VecInfNorm
            (fun j => p03ExactResidual run i j + run.deltaR i j) := by
        rw [hrhat_eq]
      _ ≤ p03VecInfNorm (p03ExactResidual run i) +
          p03VecInfNorm (run.deltaR i) := by
        exact norm_add_le _ _
      _ ≤ p03VecInfNorm (p03ExactResidual run i) +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) + g) := by
        gcongr
      _ = (1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) + g := by
        ring

  have hd_inverse :
      run.dHat i =
        p03MatVec run.Ainv (p03MatVec run.A (run.dHat i)) := by
    funext j
    exact (run.inverse_action (run.dHat i) j).symm
  have hAd_eq :
      p03MatVec run.A (run.dHat i) = fun j => run.rHat i j - h j := by
    funext j
    dsimp [h]
    ring
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

  have hh_pre :
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
              run.c2 i * p03VecInfNorm (run.rHat i)) :=
        run.correction_solver_bound i
      _ ≤ run.uS *
          (run.c1 i * p03MatInfNorm run.A *
                (p03MatInfNorm run.Ainv *
                  (p03VecInfNorm (run.rHat i) + p03VecInfNorm h)) +
            run.c2 i * p03VecInfNorm (run.rHat i)) := by
        apply mul_le_mul_of_nonneg_left _ huS
        exact add_le_add
          (mul_le_mul_of_nonneg_left hd
            (mul_nonneg (run.c1_nonneg i) (p03MatInfNorm_nonneg _)))
          le_rfl
      _ = run.uS *
          (run.c1 i * p03KappaInf run *
              (p03VecInfNorm (run.rHat i) + p03VecInfNorm h) +
            run.c2 i * p03VecInfNorm (run.rHat i)) := by
        unfold p03KappaInf
        ring
  have hh :
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
    apply (le_div_iff₀ hden).2
    nlinarith [hh_pre]

  have hdx :
      p03VecInfNorm (run.deltaX i) ≤
        run.u * p03VecInfNorm (run.x (i + 1)) := by
    apply p03VecInfNorm_le_of_abs_le
    · exact mul_nonneg hu (p03VecInfNorm_nonneg _)
    intro j
    calc
      |run.deltaX i j| ≤ run.u * |run.x (i + 1) j| :=
        run.update_error_bound i j
      _ ≤ run.u * p03VecInfNorm (run.x (i + 1)) := by
        gcongr
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (run.x (i + 1)) j
  have hAdx :
      p03VecInfNorm (p03MatVec run.A (run.deltaX i)) ≤
        run.u * p03MatInfNorm run.A *
          p03VecInfNorm (run.x (i + 1)) := by
    calc
      p03VecInfNorm (p03MatVec run.A (run.deltaX i)) ≤
          p03MatInfNorm run.A * p03VecInfNorm (run.deltaX i) :=
        p03MatVec_norm_le _ _
      _ ≤ p03MatInfNorm run.A *
          (run.u * p03VecInfNorm (run.x (i + 1))) := by
        exact mul_le_mul_of_nonneg_left hdx (p03MatInfNorm_nonneg _)
      _ = run.u * p03MatInfNorm run.A *
          p03VecInfNorm (run.x (i + 1)) := by
        ring

  have hnext_eq :
      p03ExactResidual run (i + 1) = fun j =>
        h j - run.deltaR i j - p03MatVec run.A (run.deltaX i) j := by
    funext j
    dsimp [p03ExactResidual, h, p03MatVec]
    rw [run.residual_equation i j]
    simp_rw [run.update_equation i]
    simp only [mul_add, Finset.sum_add_distrib]
    simp only [p03MatVec]
    ring
  have hnext :
      p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        p03VecInfNorm h + p03VecInfNorm (run.deltaR i) +
          p03VecInfNorm (p03MatVec run.A (run.deltaX i)) := by
    rw [hnext_eq]
    calc
      p03VecInfNorm
          (fun j => h j - run.deltaR i j -
            p03MatVec run.A (run.deltaX i) j) ≤
          p03VecInfNorm (fun j => h j - run.deltaR i j) +
            p03VecInfNorm (p03MatVec run.A (run.deltaX i)) := by
        exact norm_sub_le _ _
      _ ≤ (p03VecInfNorm h + p03VecInfNorm (run.deltaR i)) +
          p03VecInfNorm (p03MatVec run.A (run.deltaX i)) := by
        gcongr
        exact norm_sub_le _ _

  calc
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        p03VecInfNorm h + p03VecInfNorm (run.deltaR i) +
          p03VecInfNorm (p03MatVec run.A (run.deltaX i)) := hnext
    _ ≤ run.uS * p03CorrectionRatio run i *
          p03VecInfNorm (run.rHat i) +
        (run.uS * p03VecInfNorm (p03ExactResidual run i) + g) +
        (run.u * p03MatInfNorm run.A *
          p03VecInfNorm (run.x (i + 1))) := by
      gcongr
    _ ≤ run.uS * p03CorrectionRatio run i *
          ((1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) + g) +
        (run.uS * p03VecInfNorm (p03ExactResidual run i) + g) +
        (run.u * p03MatInfNorm run.A *
          p03VecInfNorm (run.x (i + 1))) := by
      gcongr
    _ = p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
      dsimp [p03Alpha, p03Beta, g]
      ring

end HighamBench
