import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec

namespace HighamBench

private def p15ToFPModel (fp : StandardFPModel) : NumStability.FPModel where
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

private theorem p15RectFrobNorm_le_mul_of_entrywise_abs_le
    {m n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (D A : P15RectMatrix m n)
    (h : ∀ i j, |D i j| ≤ c * |A i j|) :
    p15RectFrobNorm D ≤ c * p15RectFrobNorm A := by
  have hterm : ∀ i j, D i j ^ 2 ≤ c ^ 2 * A i j ^ 2 := by
    intro i j
    have hs := (sq_le_sq₀ (abs_nonneg (D i j))
      (mul_nonneg hc (abs_nonneg (A i j)))).mpr (h i j)
    simpa [mul_pow] using hs
  have hsum :
      (∑ i : Fin m, ∑ j : Fin n, D i j ^ 2) ≤
        c ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    calc
      (∑ i : Fin m, ∑ j : Fin n, D i j ^ 2) ≤
          ∑ i : Fin m, ∑ j : Fin n, c ^ 2 * A i j ^ 2 := by
            exact Finset.sum_le_sum (fun i _ =>
              Finset.sum_le_sum (fun j _ => hterm i j))
      _ = c ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
  have hD : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, D i j ^ 2 := by positivity
  have hA : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by positivity
  have hleft :
      (Real.sqrt (∑ i : Fin m, ∑ j : Fin n, D i j ^ 2)) ^ 2 =
        ∑ i : Fin m, ∑ j : Fin n, D i j ^ 2 := Real.sq_sqrt hD
  have hright :
      (c * Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) ^ 2 =
        c ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hA]
  unfold p15RectFrobNorm
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hc (Real.sqrt_nonneg _))).mp
  rw [hleft, hright]
  exact hsum

private theorem p15RoundedRectMatVec_backward
    {m n : ℕ} (fp : StandardFPModel)
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hn : GammaValid fp.u n) :
    ∃ D : P15RectMatrix m n,
      p15RectFrobNorm D ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A D) x := by
  have hn' : NumStability.gammaValid (p15ToFPModel fp) n := by
    simpa [NumStability.gammaValid, GammaValid, p15ToFPModel] using hn
  obtain ⟨D, hD, hresult⟩ :=
    NumStability.matVec_backward_error (p15ToFPModel fp) m n A x hn'
  have hgamma : 0 ≤ gamma fp.u n := by
    unfold gamma
    apply div_nonneg
    · exact mul_nonneg (by positivity) fp.u_nonneg
    · unfold GammaValid at hn
      linarith
  refine ⟨D, p15RectFrobNorm_le_mul_of_entrywise_abs_le hgamma D A ?_, ?_⟩
  · intro i j
    simpa [NumStability.gamma, gamma, p15ToFPModel] using hD i j
  · funext i
    simpa [p15RoundedRectMatVec, roundedMatVec, roundedDotProduct,
      NumStability.fl_matVec, NumStability.fl_dotProduct, p15RectMatVec,
      p15RectAdd, p15ToFPModel] using hresult i

private theorem p15RectMatVec_mul
    {m n p : ℕ} (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  simp only [p15RectMatVec, p15RectMatMul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

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
    p15RoundedRectMatVec_backward fp (p15RectTranspose Y) v hb
  obtain ⟨ΔX, hΔX, hz⟩ :=
    p15RoundedRectMatVec_backward fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y) v) hr
  refine ⟨ΔYT, ΔX, hΔYT, hΔX, hw, hz, ?_⟩
  calc
    p15RoundedRectMatVec fp X
        (p15RoundedRectMatVec fp (p15RectTranspose Y) v) =
        p15RectMatVec (p15RectAdd X ΔX)
          (p15RoundedRectMatVec fp (p15RectTranspose Y) v) := hz
    _ = p15RectMatVec (p15RectAdd X ΔX)
          (p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT) v) :=
        congrArg (p15RectMatVec (p15RectAdd X ΔX)) hw
    _ = p15RectMatVec
          (p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT)) v :=
        (p15RectMatVec_mul _ _ _).symm

end HighamBench
