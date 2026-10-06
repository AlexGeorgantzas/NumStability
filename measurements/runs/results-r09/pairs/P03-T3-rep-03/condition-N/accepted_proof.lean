import HighamBench.P03Definitions

namespace HighamBench

private lemma p03_matvec_norm_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p03VecInfNorm (p03MatVec A x) ≤
      p03MatInfNorm A * p03VecInfNorm x := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  exact Matrix.linfty_opNorm_mulVec (Matrix.of A) x

private lemma p03_mat_norm_nonneg {n : ℕ}
    (A : Fin n → Fin n → ℝ) : 0 ≤ p03MatInfNorm A := by
  unfold p03MatInfNorm
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  exact norm_nonneg _

private lemma p03_vec_abs_norm {n : ℕ} (x : Fin n → ℝ) :
    p03VecInfNorm (p03VecAbs x) = p03VecInfNorm x := by
  simp [p03VecInfNorm, p03VecAbs, Pi.norm_def, Real.norm_eq_abs]

private lemma p03_mat_abs_norm {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatInfNorm (p03MatAbs A) = p03MatInfNorm A := by
  unfold p03MatInfNorm p03MatAbs
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  simp [Matrix.linfty_opNorm_def, Real.norm_eq_abs]

private lemma p03_gamma_nonneg (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hv : GammaValid u m) : 0 ≤ gamma u m := by
  unfold GammaValid at hv
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (le_of_lt (sub_pos.mpr hv))

theorem p03_t3_normwise_residual_contraction
    {n : ℕ} (run : P03NormwiseIRRun n) (i : ℕ) :
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
      p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
  -- PROOF_START P03-T3-H001
  have hu : 0 ≤ run.u := run.uR_nonneg.trans run.uR_le_u
  have huS : 0 ≤ run.uS := hu.trans run.u_le_uS
  have hc1 : 0 ≤ run.c1 i := run.c1_nonneg i
  have hc2 : 0 ≤ run.c2 i := run.c2_nonneg i
  have hA : 0 ≤ p03MatInfNorm run.A := p03_mat_norm_nonneg run.A
  have hAi : 0 ≤ p03MatInfNorm run.Ainv := p03_mat_norm_nonneg run.Ainv
  have hkappa : 0 ≤ p03KappaInf run := by
    exact mul_nonneg hAi hA
  have hgamma :
      0 ≤ gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) :=
    p03_gamma_nonneg run.uR _ run.uR_nonneg run.gamma_valid
  have hden :
      0 < 1 - run.c1 i * p03KappaInf run * run.uS := by
    simpa [p03KappaInf] using run.denominator_condition i
  have hratio : 0 ≤ p03CorrectionRatio run i := by
    unfold p03CorrectionRatio
    exact div_nonneg (add_nonneg (mul_nonneg hc1 hkappa) hc2) hden.le

  have hrow_nonneg (j : Fin n) :
      0 ≤ p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j := by
    unfold p03MatVec p03MatAbs p03VecAbs
    positivity
  have hrow (j : Fin n) :
      p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j ≤
        p03MatInfNorm run.A * p03VecInfNorm (run.x i) := by
    calc
      p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j ≤
          p03VecInfNorm
            (p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i))) := by
        have hj := norm_le_pi_norm
          (p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i))) j
        simpa [p03VecInfNorm, Real.norm_eq_abs,
          abs_of_nonneg (hrow_nonneg j)] using hj
      _ ≤ p03MatInfNorm (p03MatAbs run.A) *
          p03VecInfNorm (p03VecAbs (run.x i)) :=
        p03_matvec_norm_le _ _
      _ = p03MatInfNorm run.A * p03VecInfNorm (run.x i) := by
        rw [p03_mat_abs_norm, p03_vec_abs_norm]
  have hbcomp (j : Fin n) :
      |run.b j| ≤ p03VecInfNorm run.b := by
    simpa [p03VecInfNorm, Real.norm_eq_abs] using norm_le_pi_norm run.b j
  have hecomp (j : Fin n) :
      |p03ExactResidual run i j| ≤
        p03VecInfNorm (p03ExactResidual run i) := by
    simpa [p03VecInfNorm, Real.norm_eq_abs] using
      norm_le_pi_norm (p03ExactResidual run i) j
  have hdr_point (j : Fin n) :
      |run.deltaR i j| ≤
        run.uS * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
            (p03VecInfNorm run.b +
              p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
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
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (by simpa [p03ExactResidual] using hecomp j) huS
        · exact mul_le_mul_of_nonneg_left
            (add_le_add (hbcomp j) (hrow j))
            (mul_nonneg (by linarith) hgamma)
  have hdr_rhs_nonneg :
      0 ≤ run.uS * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
            (p03VecInfNorm run.b +
              p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
    exact add_nonneg
      (mul_nonneg huS (norm_nonneg _))
      (mul_nonneg
        (mul_nonneg (by linarith) hgamma)
        (add_nonneg (norm_nonneg _) (mul_nonneg hA (norm_nonneg _))))
  have hdr :
      p03VecInfNorm (run.deltaR i) ≤
        run.uS * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
            (p03VecInfNorm run.b +
              p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
    apply (pi_norm_le_iff_of_nonneg hdr_rhs_nonneg).2
    intro j
    simpa [p03VecInfNorm, Real.norm_eq_abs] using hdr_point j

  have hd_eq :
      run.dHat i =
        p03MatVec run.Ainv
          (fun j => run.rHat i j -
            (run.rHat i j - p03MatVec run.A (run.dHat i) j)) := by
    funext j
    symm
    simpa only [sub_sub_cancel] using
      run.inverse_action (run.dHat i) j
  have hinner :
      p03VecInfNorm
          (fun j => run.rHat i j -
            (run.rHat i j - p03MatVec run.A (run.dHat i) j)) ≤
        p03VecInfNorm (run.rHat i) +
          p03VecInfNorm
            (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) := by
    simpa only [p03VecInfNorm] using
      norm_sub_le (run.rHat i)
        (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j)
  have hd :
      p03VecInfNorm (run.dHat i) ≤
        p03MatInfNorm run.Ainv *
          (p03VecInfNorm (run.rHat i) +
            p03VecInfNorm
              (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j)) := by
    calc
      p03VecInfNorm (run.dHat i) =
          p03VecInfNorm
            (p03MatVec run.Ainv
              (fun j => run.rHat i j -
                (run.rHat i j - p03MatVec run.A (run.dHat i) j))) :=
        congrArg p03VecInfNorm hd_eq
      _ ≤ p03MatInfNorm run.Ainv *
          p03VecInfNorm
            (fun j => run.rHat i j -
              (run.rHat i j - p03MatVec run.A (run.dHat i) j)) :=
        p03_matvec_norm_le _ _
      _ ≤ p03MatInfNorm run.Ainv *
          (p03VecInfNorm (run.rHat i) +
            p03VecInfNorm
              (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j)) :=
        mul_le_mul_of_nonneg_left hinner hAi
  have hh_rough :
      p03VecInfNorm
          (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) ≤
        run.uS *
          (run.c1 i * p03MatInfNorm run.A *
              (p03MatInfNorm run.Ainv *
                (p03VecInfNorm (run.rHat i) +
                  p03VecInfNorm
                    (fun j => run.rHat i j -
                      p03MatVec run.A (run.dHat i) j))) +
            run.c2 i * p03VecInfNorm (run.rHat i)) := by
    exact (run.correction_solver_bound i).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left hd (mul_nonneg hc1 hA))
          (le_refl _)) huS)
  have hh_scaled :
      (1 - run.c1 i * p03KappaInf run * run.uS) *
          p03VecInfNorm
            (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) ≤
        run.uS * (run.c1 i * p03KappaInf run + run.c2 i) *
          p03VecInfNorm (run.rHat i) := by
    unfold p03KappaInf
    nlinarith [hh_rough]
  have hh :
      p03VecInfNorm
          (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) ≤
        run.uS * p03CorrectionRatio run i *
          p03VecInfNorm (run.rHat i) := by
    calc
      p03VecInfNorm
          (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) ≤
          (run.uS * (run.c1 i * p03KappaInf run + run.c2 i) *
              p03VecInfNorm (run.rHat i)) /
            (1 - run.c1 i * p03KappaInf run * run.uS) := by
        apply (le_div_iff₀ hden).2
        simpa [mul_comm] using hh_scaled
      _ = run.uS * p03CorrectionRatio run i *
          p03VecInfNorm (run.rHat i) := by
        unfold p03CorrectionRatio
        ring

  have hrhat_eq :
      run.rHat i = p03ExactResidual run i + run.deltaR i := by
    funext j
    simpa [p03ExactResidual] using run.residual_equation i j
  have hrhat :
      p03VecInfNorm (run.rHat i) ≤
        (1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
            (p03VecInfNorm run.b +
              p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
    calc
      p03VecInfNorm (run.rHat i) =
          p03VecInfNorm (p03ExactResidual run i + run.deltaR i) := by
        rw [hrhat_eq]
      _ ≤ p03VecInfNorm (p03ExactResidual run i) +
          p03VecInfNorm (run.deltaR i) := by
        exact norm_add_le _ _
      _ ≤ p03VecInfNorm (p03ExactResidual run i) +
          (run.uS * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
                gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i))) :=
        add_le_add (le_refl _) hdr
      _ = (1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
          (1 + run.uS) *
              gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
            (p03VecInfNorm run.b +
              p03MatInfNorm run.A * p03VecInfNorm (run.x i)) := by
        ring
  have hh_final :
      p03VecInfNorm
          (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) ≤
        run.uS * p03CorrectionRatio run i *
          ((1 + run.uS) * p03VecInfNorm (p03ExactResidual run i) +
            (1 + run.uS) *
                gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
              (p03VecInfNorm run.b +
                p03MatInfNorm run.A * p03VecInfNorm (run.x i))) := by
    exact hh.trans (mul_le_mul_of_nonneg_left hrhat (mul_nonneg huS hratio))

  have hdx :
      p03VecInfNorm (run.deltaX i) ≤
        run.u * p03VecInfNorm (run.x (i + 1)) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hu (norm_nonneg _))).2
    intro j
    have hxj : |run.x (i + 1) j| ≤
        p03VecInfNorm (run.x (i + 1)) := by
      simpa [p03VecInfNorm, Real.norm_eq_abs] using
        norm_le_pi_norm (run.x (i + 1)) j
    simpa [p03VecInfNorm, Real.norm_eq_abs] using
      (run.update_error_bound i j).trans
        (mul_le_mul_of_nonneg_left hxj hu)
  have hAdx :
      p03VecInfNorm (p03MatVec run.A (run.deltaX i)) ≤
        run.u * p03MatInfNorm run.A *
          p03VecInfNorm (run.x (i + 1)) := by
    calc
      p03VecInfNorm (p03MatVec run.A (run.deltaX i)) ≤
          p03MatInfNorm run.A * p03VecInfNorm (run.deltaX i) :=
        p03_matvec_norm_le _ _
      _ ≤ p03MatInfNorm run.A *
          (run.u * p03VecInfNorm (run.x (i + 1))) :=
        mul_le_mul_of_nonneg_left hdx hA
      _ = run.u * p03MatInfNorm run.A *
          p03VecInfNorm (run.x (i + 1)) := by ring
  have hAxnext (j : Fin n) :
      p03MatVec run.A (run.x (i + 1)) j =
        p03MatVec run.A (run.x i) j +
          p03MatVec run.A (run.dHat i) j +
            p03MatVec run.A (run.deltaX i) j := by
    unfold p03MatVec
    simp_rw [run.update_equation i, mul_add, Finset.sum_add_distrib]
  have hres_eq :
      p03ExactResidual run (i + 1) =
        (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) -
          run.deltaR i - p03MatVec run.A (run.deltaX i) := by
    funext j
    simp only [p03ExactResidual, Pi.sub_apply]
    rw [hAxnext j, run.residual_equation i j]
    ring
  have hres_triangle :
      p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        p03VecInfNorm
            (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) +
          p03VecInfNorm (run.deltaR i) +
            p03VecInfNorm (p03MatVec run.A (run.deltaX i)) := by
    rw [hres_eq]
    exact (norm_sub_le _ _).trans
      (add_le_add (norm_sub_le _ _) (le_refl _))
  calc
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
        p03VecInfNorm
            (fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j) +
          p03VecInfNorm (run.deltaR i) +
            p03VecInfNorm (p03MatVec run.A (run.deltaX i)) := hres_triangle
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
          run.u * p03MatInfNorm run.A *
            p03VecInfNorm (run.x (i + 1)) := by
      exact add_le_add (add_le_add hh_final hdr) hAdx
    _ = p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
      unfold p03Alpha p03Beta
      ring

end HighamBench
