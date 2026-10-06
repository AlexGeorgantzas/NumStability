import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec

namespace HighamBench

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
  let fp' : NumStability.FPModel :=
    { u := fp.u
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
      model_sqrt := fp.model_sqrt }
  have hb' : NumStability.gammaValid fp' b := by
    simpa [fp', NumStability.gammaValid, GammaValid] using hb
  have hr' : NumStability.gammaValid fp' r := by
    simpa [fp', NumStability.gammaValid, GammaValid] using hr
  obtain ⟨ΔYT, hΔYT, hw⟩ :=
    NumStability.matVec_backward_error fp' r b (p15RectTranspose Y) v hb'
  let wHat := p15RoundedRectMatVec fp (p15RectTranspose Y) v
  obtain ⟨ΔX, hΔX, hz⟩ :=
    NumStability.matVec_backward_error fp' b r X wHat hr'
  have hw' :
      wHat = p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT) v := by
    funext i
    simpa [wHat, p15RoundedRectMatVec, roundedMatVec, roundedDotProduct,
      p15RectMatVec, p15RectAdd, fp', NumStability.fl_matVec,
      NumStability.fl_dotProduct] using hw i
  have hz' :
      p15RoundedRectMatVec fp X wHat =
        p15RectMatVec (p15RectAdd X ΔX) wHat := by
    funext i
    simpa [p15RoundedRectMatVec, roundedMatVec, roundedDotProduct,
      p15RectMatVec, p15RectAdd, fp', NumStability.fl_matVec,
      NumStability.fl_dotProduct] using hz i
  have hΔYTnorm :
      p15RectFrobNorm ΔYT ≤
        gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) := by
    have hγ : 0 ≤ NumStability.gamma fp' b :=
      NumStability.gamma_nonneg fp' hb'
    let B : Fin r → Fin b → ℝ :=
      fun i j ↦ NumStability.gamma fp' b * |p15RectTranspose Y i j|
    have hB : ∀ i j, 0 ≤ B i j := by
      intro i j
      exact mul_nonneg hγ (abs_nonneg _)
    have hraw := NumStability.frobNormRect_le_of_entry_abs_le ΔYT B hB hΔYT
    have hBnorm :
        NumStability.frobNormRect B =
          NumStability.gamma fp' b *
            NumStability.frobNormRect (p15RectTranspose Y) := by
      calc
        NumStability.frobNormRect B =
            |NumStability.gamma fp' b| *
              NumStability.frobNormRect
                (fun i j ↦ |p15RectTranspose Y i j|) := by
          simpa [B] using
            (NumStability.frobNormRect_smul
              (NumStability.gamma fp' b)
              (fun i j ↦ |p15RectTranspose Y i j|))
        _ = NumStability.gamma fp' b *
              NumStability.frobNormRect (p15RectTranspose Y) := by
          rw [abs_of_nonneg hγ, NumStability.frobNormRect_abs]
    rw [hBnorm] at hraw
    simpa [p15RectFrobNorm, NumStability.frobNormRect,
      NumStability.frobNormSqRect, gamma, NumStability.gamma, fp'] using hraw
  have hΔXnorm :
      p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X := by
    have hγ : 0 ≤ NumStability.gamma fp' r :=
      NumStability.gamma_nonneg fp' hr'
    let B : Fin b → Fin r → ℝ :=
      fun i j ↦ NumStability.gamma fp' r * |X i j|
    have hB : ∀ i j, 0 ≤ B i j := by
      intro i j
      exact mul_nonneg hγ (abs_nonneg _)
    have hraw := NumStability.frobNormRect_le_of_entry_abs_le ΔX B hB hΔX
    have hBnorm :
        NumStability.frobNormRect B =
          NumStability.gamma fp' r * NumStability.frobNormRect X := by
      calc
        NumStability.frobNormRect B =
            |NumStability.gamma fp' r| *
              NumStability.frobNormRect (fun i j ↦ |X i j|) := by
          simpa [B] using
            (NumStability.frobNormRect_smul
              (NumStability.gamma fp' r) (fun i j ↦ |X i j|))
        _ = NumStability.gamma fp' r * NumStability.frobNormRect X := by
          rw [abs_of_nonneg hγ, NumStability.frobNormRect_abs]
    rw [hBnorm] at hraw
    simpa [p15RectFrobNorm, NumStability.frobNormRect,
      NumStability.frobNormSqRect, gamma, NumStability.gamma, fp'] using hraw
  refine ⟨ΔYT, ΔX, hΔYTnorm, hΔXnorm, hw', hz', ?_⟩
  rw [hz', hw']
  funext i
  simp only [p15RectMatVec, p15RectMatMul, p15RectAdd]
  calc
    (∑ k : Fin r, (X i k + ΔX i k) *
        ∑ j : Fin b, (p15RectTranspose Y k j + ΔYT k j) * v j) =
        ∑ k : Fin r, ∑ j : Fin b,
          (X i k + ΔX i k) *
            ((p15RectTranspose Y k j + ΔYT k j) * v j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ j : Fin b, ∑ k : Fin r,
          (X i k + ΔX i k) *
            ((p15RectTranspose Y k j + ΔYT k j) * v j) := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin b,
          (∑ k : Fin r,
            (X i k + ΔX i k) *
              (p15RectTranspose Y k j + ΔYT k j)) * v j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

end HighamBench
