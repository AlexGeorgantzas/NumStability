import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace HighamBench

def StandardFPModel.toNumStability (fp : StandardFPModel) :
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

private lemma roundedDotProduct_eq_numStability (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    roundedDotProduct fp n x y =
      NumStability.fl_dotProduct fp.toNumStability n x y := by
  cases n <;> rfl

private lemma roundedForwardSubSteps_eq_numStability (fp : StandardFPModel)
    (n : ℕ) (L : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      roundedForwardSubSteps fp n L v k hk x =
        NumStability.fl_forwardSub_steps fp.toNumStability n L v k hk x := by
  intro k
  induction k with
  | zero =>
      intro hk x
      rfl
  | succ k ih =>
      intro hk x
      simp only [roundedForwardSubSteps, NumStability.fl_forwardSub_steps]
      apply ih

private lemma roundedForwardSub_eq_numStability (fp : StandardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    roundedForwardSub fp n L v =
      NumStability.fl_forwardSub fp.toNumStability n L v := by
  unfold roundedForwardSub NumStability.fl_forwardSub
  exact roundedForwardSubSteps_eq_numStability fp n L v n (le_refl n) _

private lemma p15_frobNorm_le_of_entrywise_relative
    {m n : ℕ} (A B : P15RectMatrix m n) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p15RectFrobNorm A ≤ c * p15RectFrobNorm B := by
  change NumStability.frobNormRect A ≤ c * NumStability.frobNormRect B
  rw [NumStability.frobNormRect_eq_frobNormFn,
    NumStability.frobNormRect_eq_frobNormFn]
  exact NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    A B hc h

private lemma p15RoundedRectMatVec_backward_error
    (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hn : GammaValid fp.u n) :
    ∃ ΔA : P15RectMatrix m n,
      p15RectFrobNorm ΔA ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A ΔA) x := by
  have hn' : NumStability.gammaValid fp.toNumStability n := by
    simpa [GammaValid, NumStability.gammaValid] using hn
  rcases NumStability.matVec_backward_error fp.toNumStability m n A x hn' with
    ⟨ΔA, hΔA, heq⟩
  refine ⟨ΔA, ?_, ?_⟩
  · apply p15_frobNorm_le_of_entrywise_relative ΔA A
      (gamma fp.u n)
    · simpa [gamma, NumStability.gamma] using
        (NumStability.gamma_nonneg fp.toNumStability hn')
    · intro i j
      simpa [gamma, NumStability.gamma] using hΔA i j
  · funext i
    change roundedDotProduct fp n (A i) x =
      ∑ j : Fin n, (A i j + ΔA i j) * x j
    rw [roundedDotProduct_eq_numStability]
    exact heq i

private lemma roundedForwardSub_backward_error
    (fp : StandardFPModel) (n : ℕ) (L : P15Matrix n) (v : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hn : GammaValid fp.u n) :
    ∃ ΔL : P15Matrix n,
      p15RectFrobNorm ΔL ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L ΔL) (roundedForwardSub fp n L v) = v := by
  have hn' : NumStability.gammaValid fp.toNumStability n := by
    simpa [GammaValid, NumStability.gammaValid] using hn
  rcases NumStability.forwardSub_backward_error fp.toNumStability n L v
      hdiag hlower hn' with ⟨ΔL, hΔL, heq⟩
  refine ⟨ΔL, ?_, ?_⟩
  · apply p15_frobNorm_le_of_entrywise_relative ΔL L
      (gamma fp.u n)
    · simpa [gamma, NumStability.gamma] using
        (NumStability.gamma_nonneg fp.toNumStability hn')
    · intro i j
      simpa [gamma, NumStability.gamma] using hΔL i j
  · funext i
    change (∑ j : Fin n, (L i j + ΔL i j) *
      roundedForwardSub fp n L v j) = v i
    rw [roundedForwardSub_eq_numStability]
    exact heq i

private lemma p15RectMatVec_matMul
    {m n p : ℕ} (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- P15-T2: the two-block instance of equation (4.22) in the proof of
Theorem 4.4, with the source's low-rank and triangular-solve perturbations. -/
theorem p15_t2_two_block_equation_4_22
    {b r : ℕ} (fp : StandardFPModel)
    (T₀ T₁ : P15Matrix b) (X Y : P15RectMatrix b r)
    (v₀ v₁ : P15Vector b)
    (hT₀diag : ∀ i, T₀ i i ≠ 0)
    (hT₁diag : ∀ i, T₁ i i ≠ 0)
    (hT₀lower : p15LowerTriangular T₀)
    (hT₁lower : p15LowerTriangular T₁)
    (hb : GammaValid fp.u b) (hr : GammaValid fp.u r) :
    let x₀ := roundedForwardSub fp b T₀ v₀
    let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
    let wHat := p15RoundedRectMatVec fp X wInner
    let rhsHat := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
    let x₁ := roundedForwardSub fp b T₁ rhsHat
    ∃ ΔT₀ : P15Matrix b, ∃ ΔYT : P15RectMatrix r b,
      ∃ ΔX : P15RectMatrix b r, ∃ θ : P15Vector b,
      ∃ ΔT₁ : P15Matrix b, ∃ ΔT₁₀ : P15Matrix b,
        p15RectFrobNorm ΔT₀ ≤ gamma fp.u b * p15RectFrobNorm T₀ ∧
        p15RectFrobNorm ΔYT ≤
          gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) ∧
        p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X ∧
        (∀ i, |θ i| ≤ fp.u) ∧
        p15RectFrobNorm ΔT₁ ≤ gamma fp.u b * p15RectFrobNorm T₁ ∧
        p15RectMatVec (p15RectAdd T₀ ΔT₀) x₀ = v₀ ∧
        wInner = p15RectMatVec
          (p15RectAdd (p15RectTranspose Y) ΔYT) x₀ ∧
        wHat = p15RectMatVec (p15RectAdd X ΔX) wInner ∧
        (∀ i, rhsHat i = (v₁ i - wHat i) * (1 + θ i)) ∧
        p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ = rhsHat ∧
        (∀ i j,
          p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
            (1 + θ i) *
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j) ∧
        ∀ i,
          p15RectMatVec
                (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i +
              p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ i =
            v₁ i * (1 + θ i) := by
  -- PROOF_START P15-T2-H001
  dsimp only
  set x₀ := roundedForwardSub fp b T₀ v₀
  set wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
  set wHat := p15RoundedRectMatVec fp X wInner
  set rhsHat : P15Vector b := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
  set x₁ := roundedForwardSub fp b T₁ rhsHat
  rcases roundedForwardSub_backward_error fp b T₀ v₀
      hT₀diag hT₀lower hb with ⟨ΔT₀, hΔT₀, hsolve₀⟩
  rcases p15RoundedRectMatVec_backward_error fp (p15RectTranspose Y) x₀ hb with
    ⟨ΔYT, hΔYT, hwInner⟩
  rcases p15RoundedRectMatVec_backward_error fp X wInner hr with
    ⟨ΔX, hΔX, hwHat⟩
  have hsub : ∀ i : Fin b, ∃ δ : ℝ,
      |δ| ≤ fp.u ∧ rhsHat i = (v₁ i - wHat i) * (1 + δ) := by
    intro i
    simpa only [rhsHat] using fp.model_sub (v₁ i) (wHat i)
  let θ : P15Vector b := fun i ↦ Classical.choose (hsub i)
  have hθ : ∀ i, |θ i| ≤ fp.u := fun i ↦
    (Classical.choose_spec (hsub i)).1
  have hrhsHat : ∀ i, rhsHat i = (v₁ i - wHat i) * (1 + θ i) :=
    fun i ↦ (Classical.choose_spec (hsub i)).2
  rcases roundedForwardSub_backward_error fp b T₁ rhsHat
      hT₁diag hT₁lower hb with ⟨ΔT₁, hΔT₁, hsolve₁⟩
  let ΔT₁₀ : P15Matrix b := fun i j ↦
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  have hblock : ∀ i j,
      p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
        (1 + θ i) *
          p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT) i j := by
    intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, ?_, ?_, ?_, hrhsHat, ?_, hblock, ?_⟩
  · simpa only [x₀] using hsolve₀
  · simpa only [wInner] using hwInner
  · simpa only [wHat] using hwHat
  · simpa only [x₁] using hsolve₁
  · intro i
    have hscaled :
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
          (1 + θ i) * wHat i := by
      calc
        p15RectMatVec
              (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
            ∑ j : Fin b,
              ((1 + θ i) *
                p15RectMatMul (p15RectAdd X ΔX)
                  (p15RectAdd (p15RectTranspose Y) ΔYT) i j) * x₀ j := by
              unfold p15RectMatVec
              apply Finset.sum_congr rfl
              intro j _
              rw [hblock i j]
        _ = (1 + θ i) *
              p15RectMatVec
                (p15RectMatMul (p15RectAdd X ΔX)
                  (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ i := by
              unfold p15RectMatVec
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = (1 + θ i) *
              p15RectMatVec (p15RectAdd X ΔX)
                (p15RectMatVec
                  (p15RectAdd (p15RectTranspose Y) ΔYT) x₀) i := by
              rw [p15RectMatVec_matMul]
        _ = (1 + θ i) * wHat i := by
              rw [← hwInner, ← hwHat]
    rw [hscaled, congrFun hsolve₁ i, hrhsHat i]
    ring

end HighamBench
