import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec

namespace HighamBench

/-- Regard the benchmark's standard model as the library's identical model. -/
def p15StandardFPModelToFPModel (fp : StandardFPModel) :
    NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := fp.fl_sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := fp.model_sqrt

/-- P15-T1: equations (3.3) and (3.4) in the proof of Lemma 3.1, including
their Frobenius-norm bounds and the composition used immediately afterward. -/
theorem p15_t1_low_rank_matvec_backward_representation
    {b r : ℕ} (fp : StandardFPModel)
    (X Y : P15RectMatrix b r) (v : P15Vector b)
    (hb : GammaValid fp.u b) (hr : GammaValid fp.u r) :
    let wHat := p15RoundedRectMatVec fp (p15RectTranspose Y) v
    let zHat := p15RoundedRectMatVec fp X wHat
    ∃ ΔYT : P15RectMatrix r b, ∃ ΔX : P15RectMatrix b r,
      p15RectFrobNorm ΔYT ≤
          gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) ∧
      p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X ∧
      wHat = p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT) v ∧
      zHat = p15RectMatVec (p15RectAdd X ΔX) wHat ∧
      zHat = p15RectMatVec
        (p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT)) v := by
  -- PROOF_START P15-T1-H001
  dsimp only
  let fp' : NumStability.FPModel := p15StandardFPModelToFPModel fp
  have hb' : NumStability.gammaValid fp' b := by
    simpa [fp', p15StandardFPModelToFPModel, GammaValid,
      NumStability.gammaValid] using hb
  have hr' : NumStability.gammaValid fp' r := by
    simpa [fp', p15StandardFPModelToFPModel, GammaValid,
      NumStability.gammaValid] using hr
  obtain ⟨ΔYT, hΔYTentry, hw⟩ :=
    NumStability.matVec_backward_error fp' r b (p15RectTranspose Y) v hb'
  let wHat := p15RoundedRectMatVec fp (p15RectTranspose Y) v
  obtain ⟨ΔX, hΔXentry, hz⟩ :=
    NumStability.matVec_backward_error fp' b r X wHat hr'
  have hgamma_b : NumStability.gamma fp' b = gamma fp.u b := by
    rfl
  have hgamma_r : NumStability.gamma fp' r = gamma fp.u r := by
    rfl
  have hΔYTnorm :
      p15RectFrobNorm ΔYT ≤
        gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) := by
    have hnonneg : 0 ≤ NumStability.gamma fp' b :=
      NumStability.gamma_nonneg fp' hb'
    have h := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      ΔYT (p15RectTranspose Y) hnonneg hΔYTentry
    simpa [p15RectFrobNorm, NumStability.frobNorm_eq_sqrt_frobNormSq,
      NumStability.frobNormSq, hgamma_b] using h
  have hΔXnorm :
      p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X := by
    have hnonneg : 0 ≤ NumStability.gamma fp' r :=
      NumStability.gamma_nonneg fp' hr'
    have h := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      ΔX X hnonneg hΔXentry
    simpa [p15RectFrobNorm, NumStability.frobNorm_eq_sqrt_frobNormSq,
      NumStability.frobNormSq, hgamma_r] using h
  have hw' :
      wHat = p15RectMatVec
        (p15RectAdd (p15RectTranspose Y) ΔYT) v := by
    funext i
    simpa [wHat, p15RoundedRectMatVec, roundedMatVec, roundedDotProduct,
      fp', p15StandardFPModelToFPModel, NumStability.fl_matVec,
      NumStability.fl_dotProduct, p15RectMatVec, p15RectAdd] using hw i
  have hz' :
      p15RoundedRectMatVec fp X wHat =
        p15RectMatVec (p15RectAdd X ΔX) wHat := by
    funext i
    simpa [wHat, p15RoundedRectMatVec, roundedMatVec, roundedDotProduct,
      fp', p15StandardFPModelToFPModel, NumStability.fl_matVec,
      NumStability.fl_dotProduct, p15RectMatVec, p15RectAdd] using hz i
  refine ⟨ΔYT, ΔX, hΔYTnorm, hΔXnorm, hw', hz', ?_⟩
  rw [hz', hw']
  ext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

end HighamBench
