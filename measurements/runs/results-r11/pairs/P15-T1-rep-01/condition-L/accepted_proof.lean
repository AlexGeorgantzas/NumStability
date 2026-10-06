import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec

namespace HighamBench

private noncomputable def p15ToFPModel (fp : StandardFPModel) :
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

private theorem p15RoundedRectMatVec_backward_error
    {m n : ℕ} (fp : StandardFPModel)
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hn : GammaValid fp.u n) :
    ∃ ΔA : P15RectMatrix m n,
      p15RectFrobNorm ΔA ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A ΔA) x := by
  let fp' := p15ToFPModel fp
  have hn' : NumStability.gammaValid fp' n := by
    simpa [fp', p15ToFPModel, GammaValid, NumStability.gammaValid] using hn
  obtain ⟨ΔA, hΔA, hresult⟩ :=
    NumStability.matVec_backward_error fp' m n A x hn'
  refine ⟨ΔA, ?_, ?_⟩
  · have hgamma : 0 ≤ NumStability.gamma fp' n :=
      NumStability.gamma_nonneg fp' hn'
    let B : Fin m → Fin n → ℝ :=
      fun i j ↦ NumStability.gamma fp' n * |A i j|
    have hBnonneg : ∀ i j, 0 ≤ B i j := by
      intro i j
      exact mul_nonneg hgamma (abs_nonneg (A i j))
    have hle : NumStability.frobNormRect ΔA ≤
        NumStability.frobNormRect B :=
      NumStability.frobNormRect_le_of_entry_abs_le ΔA B hBnonneg hΔA
    have hB : NumStability.frobNormRect B =
        NumStability.gamma fp' n * NumStability.frobNormRect A := by
      calc
        NumStability.frobNormRect B =
            |NumStability.gamma fp' n| *
              NumStability.frobNormRect (fun i j ↦ |A i j|) := by
                simpa [B] using
                  (NumStability.frobNormRect_smul
                    (NumStability.gamma fp' n) (fun i j ↦ |A i j|))
        _ = NumStability.gamma fp' n * NumStability.frobNormRect A := by
              rw [abs_of_nonneg hgamma, NumStability.frobNormRect_abs]
    rw [hB] at hle
    simpa [p15RectFrobNorm, NumStability.frobNormRect,
      NumStability.frobNormSqRect, gamma, NumStability.gamma,
      fp', p15ToFPModel] using hle
  · funext i
    simpa [p15RoundedRectMatVec, roundedMatVec, roundedDotProduct,
      p15RectMatVec, p15RectAdd, NumStability.fl_matVec,
      NumStability.fl_dotProduct, fp', p15ToFPModel] using hresult i

private theorem p15RectMatVec_matMul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  simpa [p15RectMatVec, p15RectMatMul,
    NumStability.rectMatMulVec, NumStability.rectMatMul] using
      (NumStability.rectMatMulVec_rectMatMul A B x)

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
  obtain ⟨ΔYT, hΔYT, hw⟩ :=
    p15RoundedRectMatVec_backward_error fp (p15RectTranspose Y) v hb
  obtain ⟨ΔX, hΔX, hz⟩ :=
    p15RoundedRectMatVec_backward_error fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y) v) hr
  refine ⟨ΔYT, ΔX, hΔYT, hΔX, hw, hz, ?_⟩
  calc
    p15RoundedRectMatVec fp X
        (p15RoundedRectMatVec fp (p15RectTranspose Y) v) =
        p15RectMatVec (p15RectAdd X ΔX)
          (p15RoundedRectMatVec fp (p15RectTranspose Y) v) := hz
    _ = p15RectMatVec (p15RectAdd X ΔX)
          (p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT) v) := by
            rw [hw]
    _ = p15RectMatVec
          (p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT)) v := by
              symm
              exact p15RectMatVec_matMul _ _ _

end HighamBench
