import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

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

private lemma p15FrobNorm_le_of_entrywise {m n : ℕ}
    (A E : P15RectMatrix m n) {c : ℝ} (hc : 0 ≤ c)
    (hE : ∀ i j, |E i j| ≤ c * |A i j|) :
    p15RectFrobNorm E ≤ c * p15RectFrobNorm A := by
  have h := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    E A hc hE
  calc
    p15RectFrobNorm E = NumStability.frobNormRect E := rfl
    _ = NumStability.frobNorm E :=
      NumStability.frobNormRect_eq_frobNormFn E
    _ ≤ c * NumStability.frobNorm A := h
    _ = c * NumStability.frobNormRect A := by
      rw [NumStability.frobNormRect_eq_frobNormFn]
    _ = c * p15RectFrobNorm A := rfl

private lemma p15RoundedRectMatVec_backward_error
    (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hn : GammaValid fp.u n) :
    ∃ E : P15RectMatrix m n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x = p15RectMatVec (p15RectAdd A E) x := by
  let fp' := p15AsFPModel fp
  have hn' : NumStability.gammaValid fp' n := by
    exact hn
  obtain ⟨E, hE, heq⟩ :=
    NumStability.matVec_backward_error fp' m n A x hn'
  refine ⟨E, ?_, ?_⟩
  · apply p15FrobNorm_le_of_entrywise A E
    · exact NumStability.gamma_nonneg fp' hn'
    · exact hE
  · funext i
    exact heq i

private lemma p15RoundedForwardSubSteps_eq
    (fp : StandardFPModel) (n : ℕ) (L : P15Matrix n) (v : P15Vector n)
    (k : ℕ) (hk : k ≤ n) (x : P15Vector n) :
    roundedForwardSubSteps fp n L v k hk x =
      NumStability.fl_forwardSub_steps (p15AsFPModel fp) n L v k hk x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      simp only [roundedForwardSubSteps,
        NumStability.fl_forwardSub_steps]
      apply ih

private lemma p15RoundedForwardSub_eq
    (fp : StandardFPModel) (n : ℕ) (L : P15Matrix n) (v : P15Vector n) :
    roundedForwardSub fp n L v =
      NumStability.fl_forwardSub (p15AsFPModel fp) n L v := by
  exact p15RoundedForwardSubSteps_eq fp n L v n (le_refl n) (fun _ ↦ 0)

private lemma p15RoundedForwardSub_backward_error
    (fp : StandardFPModel) (n : ℕ) (L : P15Matrix n) (v : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hn : GammaValid fp.u n) :
    ∃ E : P15Matrix n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L E) (roundedForwardSub fp n L v) = v := by
  let fp' := p15AsFPModel fp
  have hn' : NumStability.gammaValid fp' n := by
    exact hn
  obtain ⟨E, hE, heq⟩ :=
    NumStability.forwardSub_backward_error fp' n L v hdiag hlower hn'
  refine ⟨E, ?_, ?_⟩
  · apply p15FrobNorm_le_of_entrywise L E
    · exact NumStability.gamma_nonneg fp' hn'
    · exact hE
  · funext i
    change (∑ j : Fin n,
      (L i j + E i j) * roundedForwardSub fp n L v j) = v i
    rw [p15RoundedForwardSub_eq]
    exact heq i

private lemma p15RectMatVec_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  simp only [p15RectMatVec, p15RectMatMul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
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
  dsimp
  let x₀ := roundedForwardSub fp b T₀ v₀
  let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
  let wHat := p15RoundedRectMatVec fp X wInner
  let rhsHat : P15Vector b := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
  let x₁ := roundedForwardSub fp b T₁ rhsHat
  obtain ⟨ΔT₀, hΔT₀, hx₀⟩ :=
    p15RoundedForwardSub_backward_error fp b T₀ v₀
      hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hΔYT, hwInner⟩ :=
    p15RoundedRectMatVec_backward_error fp (p15RectTranspose Y) x₀ hb
  obtain ⟨ΔX, hΔX, hwHat⟩ :=
    p15RoundedRectMatVec_backward_error fp X wInner hr
  have hwInner' :
      wInner = p15RectMatVec
        (p15RectAdd (p15RectTranspose Y) ΔYT) x₀ := hwInner
  have hwHat' :
      wHat = p15RectMatVec (p15RectAdd X ΔX) wInner := hwHat
  let θ : P15Vector b := fun i ↦
    Classical.choose (fp.model_sub (v₁ i) (wHat i))
  have hθ : ∀ i, |θ i| ≤ fp.u := by
    intro i
    exact (Classical.choose_spec (fp.model_sub (v₁ i) (wHat i))).1
  have hrhsHat : ∀ i, rhsHat i = (v₁ i - wHat i) * (1 + θ i) := by
    intro i
    exact (Classical.choose_spec (fp.model_sub (v₁ i) (wHat i))).2
  obtain ⟨ΔT₁, hΔT₁, hx₁⟩ :=
    p15RoundedForwardSub_backward_error fp b T₁ rhsHat
      hT₁diag hT₁lower hb
  let ΔT₁₀ : P15Matrix b := fun i j ↦
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, hx₀, hwInner, hwHat,
    hrhsHat, hx₁, ?_, ?_⟩
  · intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring
  · intro i
    have hblock :
        p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ =
          fun q j ↦ (1 + θ q) *
            p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT) q j := by
      funext q j
      simp only [p15RectAdd, ΔT₁₀]
      ring
    have hlow :
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
          (1 + θ i) * wHat i := by
      calc
        p15RectMatVec
              (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
            p15RectMatVec
              (fun q j ↦ (1 + θ q) *
                p15RectMatMul (p15RectAdd X ΔX)
                  (p15RectAdd (p15RectTranspose Y) ΔYT) q j) x₀ i := by
                rw [hblock]
        _ = (1 + θ i) *
              p15RectMatVec
                (p15RectMatMul (p15RectAdd X ΔX)
                  (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ i := by
              simp only [p15RectMatVec]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = (1 + θ i) *
              p15RectMatVec (p15RectAdd X ΔX)
                (p15RectMatVec
                  (p15RectAdd (p15RectTranspose Y) ΔYT) x₀) i := by
              rw [p15RectMatVec_mul]
        _ = (1 + θ i) *
              p15RectMatVec (p15RectAdd X ΔX) wInner i := by
              rw [← hwInner']
        _ = (1 + θ i) * wHat i := by
              rw [hwHat']
    have hx₁i := congrFun hx₁ i
    rw [hlow, hx₁i, hrhsHat i]
    ring

end HighamBench
