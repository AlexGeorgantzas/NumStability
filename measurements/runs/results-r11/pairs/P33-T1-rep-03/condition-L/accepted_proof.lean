import HighamBench.P33Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

open scoped BigOperators

/-- The paper-local arithmetic model, viewed as NumStability's standard model. -/
noncomputable def p33NumStabilityFPModel (fp : P33FPModel) :
    NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := by
    intro y _hy
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let nfp := p33NumStabilityFPModel fp
  let dHat := p33RoundedSparseRowProduct fp s a x
  let d := ∑ j : Fin s, a j * x j
  let A := ∑ j : Fin s, |a j| * |x j|
  have hvalid' : NumStability.gammaValid nfp (s + 1) := by
    simpa [NumStability.gammaValid, P33GammaValid, nfp,
      p33NumStabilityFPModel] using hvalid
  have hvalid_s : NumStability.gammaValid nfp s :=
    NumStability.gammaValid_mono nfp (Nat.le_succ s) hvalid'
  have hdot :
      |dHat - d| ≤ NumStability.gamma nfp s * A := by
    simpa [dHat, d, A, nfp, p33NumStabilityFPModel,
      p33RoundedSparseRowProduct, NumStability.fl_dotProduct] using
      (NumStability.dotProduct_error_bound nfp s a x hvalid_s)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hd_abs : |d| ≤ A := by
    dsimp [d, A]
    calc
      |∑ j : Fin s, a j * x j|
          ≤ ∑ j : Fin s, |a j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin s, |a j| * |x j| := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [abs_mul]
  have hgamma_s_nonneg : 0 ≤ NumStability.gamma nfp s :=
    NumStability.gamma_nonneg nfp hvalid_s
  have hdHat_abs :
      |dHat| ≤ (1 + NumStability.gamma nfp s) * A := by
    calc
      |dHat| = |(dHat - d) + d| := by ring_nf
      _ ≤ |dHat - d| + |d| := abs_add_le _ _
      _ ≤ NumStability.gamma nfp s * A + A := add_le_add hdot hd_abs
      _ = (1 + NumStability.gamma nfp s) * A := by ring
  obtain ⟨delta, hdelta, hsub⟩ :=
    fp.model_sub b (p33RoundedSparseRowProduct fp s a x)
  have hu_gamma : fp.u ≤ NumStability.gamma nfp (s + 1) := by
    simpa [nfp, p33NumStabilityFPModel] using
      (NumStability.u_le_gamma nfp (Nat.succ_pos s) hvalid')
  have hcoef :
      NumStability.gamma nfp s + fp.u * (1 + NumStability.gamma nfp s) ≤
        NumStability.gamma nfp (s + 1) := by
    have hvalid_one : NumStability.gammaValid nfp 1 :=
      NumStability.gammaValid_mono nfp (by omega) hvalid'
    have hu_gamma_one : fp.u ≤ NumStability.gamma nfp 1 := by
      simpa [nfp, p33NumStabilityFPModel] using
        (NumStability.u_le_gamma nfp one_pos hvalid_one)
    have hmul :
        fp.u * NumStability.gamma nfp s ≤
          NumStability.gamma nfp 1 * NumStability.gamma nfp s :=
      mul_le_mul_of_nonneg_right hu_gamma_one hgamma_s_nonneg
    have hsum := NumStability.gamma_sum_le nfp s 1 (by
      simpa [Nat.add_comm] using hvalid')
    nlinarith
  have hresult :
      |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
        NumStability.gamma nfp (s + 1) * (|b| + A) := by
    have hdecomp :
        p33RoundedResidual fp s a x b - p33ExactResidual s a x b =
          (d - dHat) + delta * (b - dHat) := by
      simp only [p33RoundedResidual, p33ExactResidual]
      rw [hsub]
      dsimp [dHat, d]
      ring
    rw [hdecomp]
    calc
      |(d - dHat) + delta * (b - dHat)|
          ≤ |d - dHat| + |delta * (b - dHat)| := abs_add_le _ _
      _ = |dHat - d| + |delta| * |b - dHat| := by
            rw [abs_sub_comm d dHat, abs_mul]
      _ ≤ NumStability.gamma nfp s * A + fp.u * |b - dHat| := by
            exact add_le_add hdot
              (mul_le_mul_of_nonneg_right hdelta (abs_nonneg _))
      _ ≤ NumStability.gamma nfp s * A + fp.u * (|b| + |dHat|) := by
            exact add_le_add (le_refl _)
              (mul_le_mul_of_nonneg_left
                (by simpa using (abs_sub_le b 0 dHat)) fp.u_nonneg)
      _ ≤ NumStability.gamma nfp s * A +
            fp.u * (|b| + (1 + NumStability.gamma nfp s) * A) := by
            exact add_le_add (le_refl _)
              (mul_le_mul_of_nonneg_left
                (add_le_add (le_refl (|b|)) hdHat_abs) fp.u_nonneg)
      _ = fp.u * |b| +
            (NumStability.gamma nfp s +
              fp.u * (1 + NumStability.gamma nfp s)) * A := by ring
      _ ≤ NumStability.gamma nfp (s + 1) * |b| +
            NumStability.gamma nfp (s + 1) * A := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hu_gamma (abs_nonneg b))
              (mul_le_mul_of_nonneg_right hcoef hA)
      _ = NumStability.gamma nfp (s + 1) * (|b| + A) := by ring
  simpa [p33ResidualErrorMajorant, p33Gamma, A, nfp,
    p33NumStabilityFPModel, NumStability.gamma] using hresult

end HighamBench
