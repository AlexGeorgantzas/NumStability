import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace HighamBench

noncomputable def p15ToFPModel (fp : StandardFPModel) : NumStability.FPModel where
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

lemma p15_gamma_eq (fp : StandardFPModel) (n : ℕ) :
    NumStability.gamma (p15ToFPModel fp) n = gamma fp.u n := by
  rfl

lemma p15_gammaValid_iff (fp : StandardFPModel) (n : ℕ) :
    NumStability.gammaValid (p15ToFPModel fp) n ↔ GammaValid fp.u n := by
  rfl

lemma p15_roundedRectMatVec_eq (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ) :
    p15RoundedRectMatVec fp A x =
      NumStability.fl_matVec (p15ToFPModel fp) m n A x := by
  rfl

lemma p15_roundedForwardSubSteps_eq (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) :
    roundedForwardSubSteps fp n L v k hk x =
      NumStability.fl_forwardSub_steps (p15ToFPModel fp) n L v k hk x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      simp only [roundedForwardSubSteps,
        NumStability.fl_forwardSub_steps]
      apply ih

lemma p15_roundedForwardSub_eq (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n) :
    roundedForwardSub fp n L v =
      NumStability.fl_forwardSub (p15ToFPModel fp) n L v := by
  unfold roundedForwardSub NumStability.fl_forwardSub
  exact p15_roundedForwardSubSteps_eq fp n L v n (le_refl n) _

lemma p15_frobNorm_le_of_entrywise {m n : ℕ}
    (A B : P15RectMatrix m n) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p15RectFrobNorm A ≤ c * p15RectFrobNorm B := by
  have h' := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    A B hc h
  simpa only [p15RectFrobNorm, NumStability.frobNorm_eq_sqrt_frobNormSq,
    NumStability.frobNormSq] using h'

lemma p15_rectMatVec_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
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
  let gfp := p15ToFPModel fp
  have hb' : NumStability.gammaValid gfp b :=
    (p15_gammaValid_iff fp b).2 hb
  have hr' : NumStability.gammaValid gfp r :=
    (p15_gammaValid_iff fp r).2 hr
  have hgb : 0 ≤ gamma fp.u b := by
    rw [← p15_gamma_eq fp b]
    exact NumStability.gamma_nonneg gfp hb'
  have hgr : 0 ≤ gamma fp.u r := by
    rw [← p15_gamma_eq fp r]
    exact NumStability.gamma_nonneg gfp hr'

  obtain ⟨ΔT₀, hΔT₀entry, hΔT₀eq⟩ :=
    NumStability.forwardSub_backward_error gfp b T₀ v₀ hT₀diag hT₀lower hb'
  have hΔT₀norm :
      p15RectFrobNorm ΔT₀ ≤ gamma fp.u b * p15RectFrobNorm T₀ := by
    apply p15_frobNorm_le_of_entrywise ΔT₀ T₀ hgb
    intro i j
    simpa only [p15_gamma_eq] using hΔT₀entry i j
  have hΔT₀solve :
      p15RectMatVec (p15RectAdd T₀ ΔT₀)
          (roundedForwardSub fp b T₀ v₀) = v₀ := by
    funext i
    simpa only [p15RectMatVec, p15RectAdd, p15_roundedForwardSub_eq]
      using hΔT₀eq i

  obtain ⟨ΔYT, hΔYTentry, hΔYTeq⟩ :=
    NumStability.matVec_backward_error gfp r b (p15RectTranspose Y)
      (roundedForwardSub fp b T₀ v₀) hb'
  have hΔYTnorm :
      p15RectFrobNorm ΔYT ≤
        gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) := by
    apply p15_frobNorm_le_of_entrywise ΔYT (p15RectTranspose Y) hgb
    intro i j
    simpa only [p15_gamma_eq] using hΔYTentry i j
  have hInner :
      p15RoundedRectMatVec fp (p15RectTranspose Y)
          (roundedForwardSub fp b T₀ v₀) =
        p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT)
          (roundedForwardSub fp b T₀ v₀) := by
    funext i
    simpa only [p15_roundedRectMatVec_eq, p15RectMatVec, p15RectAdd]
      using hΔYTeq i

  obtain ⟨ΔX, hΔXentry, hΔXeq⟩ :=
    NumStability.matVec_backward_error gfp b r X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) hr'
  have hΔXnorm :
      p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X := by
    apply p15_frobNorm_le_of_entrywise ΔX X hgr
    intro i j
    simpa only [p15_gamma_eq] using hΔXentry i j
  have hOuter :
      p15RoundedRectMatVec fp X
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) =
        p15RectMatVec (p15RectAdd X ΔX)
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) := by
    funext i
    simpa only [p15_roundedRectMatVec_eq, p15RectMatVec, p15RectAdd]
      using hΔXeq i

  let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y)
    (roundedForwardSub fp b T₀ v₀)
  let wHat := p15RoundedRectMatVec fp X wInner
  let rhsHat : P15Vector b := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
  have hsub : ∀ i, ∃ d : ℝ, |d| ≤ fp.u ∧
      rhsHat i = (v₁ i - wHat i) * (1 + d) := by
    intro i
    exact fp.model_sub (v₁ i) (wHat i)
  let θ : P15Vector b := fun i ↦ Classical.choose (hsub i)
  have hθ : ∀ i, |θ i| ≤ fp.u := fun i ↦
    (Classical.choose_spec (hsub i)).1
  have hrhs : ∀ i, rhsHat i = (v₁ i - wHat i) * (1 + θ i) := fun i ↦
    (Classical.choose_spec (hsub i)).2

  obtain ⟨ΔT₁, hΔT₁entry, hΔT₁eq⟩ :=
    NumStability.forwardSub_backward_error gfp b T₁ rhsHat
      hT₁diag hT₁lower hb'
  have hΔT₁norm :
      p15RectFrobNorm ΔT₁ ≤ gamma fp.u b * p15RectFrobNorm T₁ := by
    apply p15_frobNorm_le_of_entrywise ΔT₁ T₁ hgb
    intro i j
    simpa only [p15_gamma_eq] using hΔT₁entry i j
  have hΔT₁solve :
      p15RectMatVec (p15RectAdd T₁ ΔT₁)
          (roundedForwardSub fp b T₁ rhsHat) = rhsHat := by
    funext i
    simpa only [p15RectMatVec, p15RectAdd, p15_roundedForwardSub_eq]
      using hΔT₁eq i

  let ΔT₁₀ : P15Matrix b := fun i j ↦
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  have hΔT₁₀ : ∀ i j,
      p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
        (1 + θ i) *
          p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT) i j := by
    intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring
  have hblock : ∀ i,
      p15RectMatVec (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀)
          (roundedForwardSub fp b T₀ v₀) i =
        (1 + θ i) * wHat i := by
    intro i
    rw [show p15RectMatVec
          (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀)
          (roundedForwardSub fp b T₀ v₀) i =
        (1 + θ i) *
          p15RectMatVec
            (p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT))
            (roundedForwardSub fp b T₀ v₀) i by
      unfold p15RectMatVec
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hΔT₁₀ i j]
      ring]
    rw [p15_rectMatVec_mul]
    change (1 + θ i) *
        p15RectMatVec (p15RectAdd X ΔX)
          (p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT)
            (roundedForwardSub fp b T₀ v₀)) i =
      (1 + θ i) * wHat i
    rw [← hInner, ← hOuter]

  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀norm, hΔYTnorm, hΔXnorm, hθ, hΔT₁norm,
    hΔT₀solve, ?_, ?_, ?_, hΔT₁solve, hΔT₁₀, ?_⟩
  · exact hInner
  · exact hOuter
  · exact hrhs
  · intro i
    rw [hblock i, hΔT₁solve]
    rw [hrhs i]
    ring

end HighamBench
