import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec

namespace HighamBench

private noncomputable def p15AsFPModel (fp : StandardFPModel) :
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

private lemma p15_frob_bound_of_entrywise_bound {m n : ℕ}
    (A E : P15RectMatrix m n) {c : ℝ} (hc : 0 ≤ c)
    (hE : ∀ i j, |E i j| ≤ c * |A i j|) :
    p15RectFrobNorm E ≤ c * p15RectFrobNorm A := by
  have h := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    E A hc hE
  rw [NumStability.frobNorm_eq_sqrt_frobNormSq,
    NumStability.frobNorm_eq_sqrt_frobNormSq] at h
  simpa [p15RectFrobNorm, NumStability.frobNormSq] using h

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
  dsimp
  let fp' : NumStability.FPModel := p15AsFPModel fp
  have hb' : NumStability.gammaValid fp' b := by
    simpa [fp', p15AsFPModel, NumStability.gammaValid, GammaValid] using hb
  have hr' : NumStability.gammaValid fp' r := by
    simpa [fp', p15AsFPModel, NumStability.gammaValid, GammaValid] using hr
  obtain ⟨ΔYT, hΔYTentry, hw⟩ :=
    NumStability.matVec_backward_error fp' r b (p15RectTranspose Y) v hb'
  let wHat := p15RoundedRectMatVec fp (p15RectTranspose Y) v
  have hw' : wHat = p15RectMatVec
      (p15RectAdd (p15RectTranspose Y) ΔYT) v := by
    funext i
    simpa [wHat, p15RoundedRectMatVec, roundedMatVec, roundedDotProduct,
      fp', p15AsFPModel, NumStability.fl_matVec,
      NumStability.fl_dotProduct, p15RectMatVec, p15RectAdd] using hw i
  obtain ⟨ΔX, hΔXentry, hz⟩ :=
    NumStability.matVec_backward_error fp' b r X wHat hr'
  have hz' : p15RoundedRectMatVec fp X wHat =
      p15RectMatVec (p15RectAdd X ΔX) wHat := by
    funext i
    simpa [p15RoundedRectMatVec, roundedMatVec, roundedDotProduct,
      fp', p15AsFPModel, NumStability.fl_matVec,
      NumStability.fl_dotProduct, p15RectMatVec, p15RectAdd] using hz i
  have hgamma_b : NumStability.gamma fp' b = gamma fp.u b := by
    rfl
  have hgamma_r : NumStability.gamma fp' r = gamma fp.u r := by
    rfl
  have hgb_nonneg : 0 ≤ gamma fp.u b := by
    rw [← hgamma_b]
    exact NumStability.gamma_nonneg fp' hb'
  have hgr_nonneg : 0 ≤ gamma fp.u r := by
    rw [← hgamma_r]
    exact NumStability.gamma_nonneg fp' hr'
  have hΔYTnorm : p15RectFrobNorm ΔYT ≤
      gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) := by
    apply p15_frob_bound_of_entrywise_bound _ _ hgb_nonneg
    intro i j
    simpa [hgamma_b] using hΔYTentry i j
  have hΔXnorm : p15RectFrobNorm ΔX ≤
      gamma fp.u r * p15RectFrobNorm X := by
    apply p15_frob_bound_of_entrywise_bound _ _ hgr_nonneg
    intro i j
    simpa [hgamma_r] using hΔXentry i j
  refine ⟨ΔYT, ΔX, hΔYTnorm, hΔXnorm, hw', hz', ?_⟩
  rw [hz', hw']
  funext i
  simp only [p15RectMatVec, p15RectMatMul]
  calc
    (∑ x : Fin r, p15RectAdd X ΔX i x *
        ∑ j : Fin b, p15RectAdd (p15RectTranspose Y) ΔYT x j * v j) =
        ∑ x : Fin r, ∑ j : Fin b,
          (p15RectAdd X ΔX i x *
            p15RectAdd (p15RectTranspose Y) ΔYT x j) * v j := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin b, ∑ x : Fin r,
          (p15RectAdd X ΔX i x *
            p15RectAdd (p15RectTranspose Y) ΔYT x j) * v j :=
      Finset.sum_comm
    _ = ∑ j : Fin b,
          (∑ x : Fin r, p15RectAdd X ΔX i x *
            p15RectAdd (p15RectTranspose Y) ΔYT x j) * v j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]

end HighamBench
