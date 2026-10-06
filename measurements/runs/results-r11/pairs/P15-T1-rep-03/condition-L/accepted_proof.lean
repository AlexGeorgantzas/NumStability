import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec

namespace HighamBench

private def p15ToNumStabilityFPModel (fp : StandardFPModel) :
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

private theorem p15RoundedRectMatVec_backward_frob
    (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : P15Vector n)
    (hn : GammaValid fp.u n) :
    ∃ ΔA : P15RectMatrix m n,
      p15RectFrobNorm ΔA ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A ΔA) x := by
  let nfp := p15ToNumStabilityFPModel fp
  have hn' : NumStability.gammaValid nfp n := by
    simpa [nfp, p15ToNumStabilityFPModel, GammaValid,
      NumStability.gammaValid] using hn
  obtain ⟨ΔA, hΔA, hfl⟩ :=
    NumStability.matVec_backward_error nfp m n A x hn'
  have hgamma : 0 ≤ gamma fp.u n := by
    simpa [nfp, p15ToNumStabilityFPModel, gamma,
      NumStability.gamma] using NumStability.gamma_nonneg nfp hn'
  let B : P15RectMatrix m n := fun i j => gamma fp.u n * |A i j|
  have hB : ∀ i j, 0 ≤ B i j := by
    intro i j
    exact mul_nonneg hgamma (abs_nonneg (A i j))
  have hentry : ∀ i j, |ΔA i j| ≤ B i j := by
    intro i j
    simpa [B, nfp, p15ToNumStabilityFPModel, gamma,
      NumStability.gamma] using hΔA i j
  have hnorm : p15RectFrobNorm ΔA ≤ p15RectFrobNorm B := by
    simpa [p15RectFrobNorm, NumStability.frobNormRect,
      NumStability.frobNormSqRect] using
        NumStability.frobNormRect_le_of_entry_abs_le ΔA B hB hentry
  have hBnorm :
      p15RectFrobNorm B = gamma fp.u n * p15RectFrobNorm A := by
    calc
      p15RectFrobNorm B =
          |gamma fp.u n| * p15RectFrobNorm (fun i j => |A i j|) := by
            simpa [B, p15RectFrobNorm, NumStability.frobNormRect,
              NumStability.frobNormSqRect] using
                NumStability.frobNormRect_smul
                  (gamma fp.u n) (fun i j => |A i j|)
      _ = gamma fp.u n * p15RectFrobNorm A := by
            rw [abs_of_nonneg hgamma]
            congr 1
            simpa [p15RectFrobNorm, NumStability.frobNormRect,
              NumStability.frobNormSqRect] using
                NumStability.frobNormRect_abs A
  refine ⟨ΔA, hnorm.trans_eq hBnorm, ?_⟩
  funext i
  simpa [p15RoundedRectMatVec, roundedMatVec, roundedDotProduct,
    p15RectMatVec, p15RectAdd, nfp, p15ToNumStabilityFPModel,
    NumStability.fl_matVec, NumStability.fl_dotProduct] using hfl i

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
  obtain ⟨ΔYT, hΔYT, hwHat⟩ :=
    p15RoundedRectMatVec_backward_frob fp (p15RectTranspose Y) v hb
  obtain ⟨ΔX, hΔX, hzHat⟩ :=
    p15RoundedRectMatVec_backward_frob fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y) v) hr
  refine ⟨ΔYT, ΔX, hΔYT, hΔX, hwHat, hzHat, ?_⟩
  rw [hzHat, hwHat]
  ext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

end HighamBench
