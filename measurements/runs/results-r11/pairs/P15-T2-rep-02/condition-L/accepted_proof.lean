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

private lemma p15_gamma_bridge (fp : StandardFPModel) (n : ℕ) :
    NumStability.gamma (p15ToFPModel fp) n = gamma fp.u n := by
  rfl

private lemma p15_gammaValid_bridge (fp : StandardFPModel) (n : ℕ) :
    NumStability.gammaValid (p15ToFPModel fp) n = GammaValid fp.u n := by
  rfl

private lemma p15_matVec_bridge (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ) :
    NumStability.fl_matVec (p15ToFPModel fp) m n A x =
      p15RoundedRectMatVec fp A x := by
  rfl

private lemma p15_forwardSub_bridge (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n) :
    NumStability.fl_forwardSub (p15ToFPModel fp) n L v =
      roundedForwardSub fp n L v := by
  unfold NumStability.fl_forwardSub roundedForwardSub
  have hsteps : ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      NumStability.fl_forwardSub_steps (p15ToFPModel fp) n L v k hk x =
        roundedForwardSubSteps fp n L v k hk x := by
    intro k
    induction k with
    | zero =>
        intro hk x
        rfl
    | succ k ih =>
        intro hk x
        unfold NumStability.fl_forwardSub_steps roundedForwardSubSteps
        apply ih
  exact hsteps n (le_refl n) (fun _ ↦ 0)

private lemma p15_frob_bound_of_componentwise {m n : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (A E : P15RectMatrix m n)
    (hE : ∀ i j, |E i j| ≤ c * |A i j|) :
    p15RectFrobNorm E ≤ c * p15RectFrobNorm A := by
  let B : Fin m → Fin n → ℝ := fun i j ↦ c * |A i j|
  have hB0 : ∀ i j, 0 ≤ B i j := by
    intro i j
    exact mul_nonneg hc (abs_nonneg _)
  have hraw : NumStability.frobNormRect E ≤ NumStability.frobNormRect B :=
    NumStability.frobNormRect_le_of_entry_abs_le E B hB0 hE
  have hB : NumStability.frobNormRect B =
      c * NumStability.frobNormRect A := by
    calc
      NumStability.frobNormRect B = |c| *
          NumStability.frobNormRect (fun i j ↦ |A i j|) := by
            simpa [B] using
              (NumStability.frobNormRect_smul c (fun i j ↦ |A i j|))
      _ = c * NumStability.frobNormRect A := by
            rw [abs_of_nonneg hc, NumStability.frobNormRect_abs]
  change NumStability.frobNormRect E ≤ c * NumStability.frobNormRect A
  rw [← hB]
  exact hraw

private lemma p15_roundedRectMatVec_backward
    (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hn : GammaValid fp.u n) :
    ∃ E : P15RectMatrix m n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A E) x := by
  let fp' := p15ToFPModel fp
  have hn' : NumStability.gammaValid fp' n := by
    simpa [fp', p15_gammaValid_bridge] using hn
  obtain ⟨E, hE, hEq⟩ :=
    NumStability.matVec_backward_error fp' m n A x hn'
  refine ⟨E, ?_, ?_⟩
  · apply p15_frob_bound_of_componentwise (gamma fp.u n)
    · simpa [fp', p15_gamma_bridge] using
        (NumStability.gamma_nonneg fp' hn')
    · intro i j
      simpa [fp', p15_gamma_bridge] using hE i j
  · rw [← p15_matVec_bridge]
    funext i
    simpa [p15RectMatVec, p15RectAdd] using hEq i

private lemma p15_roundedForwardSub_backward
    (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : p15LowerTriangular L)
    (hn : GammaValid fp.u n) :
    ∃ E : P15Matrix n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L E) (roundedForwardSub fp n L v) = v := by
  let fp' := p15ToFPModel fp
  have hn' : NumStability.gammaValid fp' n := by
    simpa [fp', p15_gammaValid_bridge] using hn
  obtain ⟨E, hE, hEq⟩ :=
    NumStability.forwardSub_backward_error fp' n L v hdiag hlower hn'
  refine ⟨E, ?_, ?_⟩
  · apply p15_frob_bound_of_componentwise (gamma fp.u n)
    · simpa [fp', p15_gamma_bridge] using
        (NumStability.gamma_nonneg fp' hn')
    · intro i j
      simpa [fp', p15_gamma_bridge] using hE i j
  · rw [← p15_forwardSub_bridge]
    funext i
    simpa [p15RectMatVec, p15RectAdd] using hEq i

private lemma p15_rectMatMul_matVec {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) (i : Fin m) :
    p15RectMatVec (p15RectMatMul A B) x i =
      p15RectMatVec A (p15RectMatVec B x) i := by
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
  dsimp only
  obtain ⟨ΔT₀, hΔT₀, hx₀⟩ :=
    p15_roundedForwardSub_backward fp b T₀ v₀ hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hΔYT, hwInner⟩ :=
    p15_roundedRectMatVec_backward fp (p15RectTranspose Y)
      (roundedForwardSub fp b T₀ v₀) hb
  obtain ⟨ΔX, hΔX, hwHat⟩ :=
    p15_roundedRectMatVec_backward fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) hr
  let θ : P15Vector b := fun i ↦
    Classical.choose
      (fp.model_sub (v₁ i)
        (p15RoundedRectMatVec fp X
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) i))
  have hθ : ∀ i, |θ i| ≤ fp.u := by
    intro i
    exact (Classical.choose_spec
      (fp.model_sub (v₁ i)
        (p15RoundedRectMatVec fp X
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) i))).1
  have hrhs : ∀ i,
      fp.fl_sub (v₁ i)
          (p15RoundedRectMatVec fp X
            (p15RoundedRectMatVec fp (p15RectTranspose Y)
              (roundedForwardSub fp b T₀ v₀)) i) =
        (v₁ i -
          p15RoundedRectMatVec fp X
            (p15RoundedRectMatVec fp (p15RectTranspose Y)
              (roundedForwardSub fp b T₀ v₀)) i) * (1 + θ i) := by
    intro i
    exact (Classical.choose_spec
      (fp.model_sub (v₁ i)
        (p15RoundedRectMatVec fp X
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) i))).2
  obtain ⟨ΔT₁, hΔT₁, hx₁⟩ :=
    p15_roundedForwardSub_backward fp b T₁
      (fun i ↦ fp.fl_sub (v₁ i)
        (p15RoundedRectMatVec fp X
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) i))
      hT₁diag hT₁lower hb
  let ΔT₁₀ : P15Matrix b := fun i j ↦
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, hx₀, hwInner, hwHat,
    hrhs, hx₁, ?_, ?_⟩
  · intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring
  · intro i
    have hscaled :
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀)
            (roundedForwardSub fp b T₀ v₀) i =
          (1 + θ i) *
            p15RoundedRectMatVec fp X
              (p15RoundedRectMatVec fp (p15RectTranspose Y)
                (roundedForwardSub fp b T₀ v₀)) i := by
      calc
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀)
            (roundedForwardSub fp b T₀ v₀) i =
            (1 + θ i) *
              p15RectMatVec
                (p15RectMatMul (p15RectAdd X ΔX)
                  (p15RectAdd (p15RectTranspose Y) ΔYT))
                (roundedForwardSub fp b T₀ v₀) i := by
              simp only [p15RectMatVec, p15RectAdd, ΔT₁₀]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = (1 + θ i) *
              p15RectMatVec (p15RectAdd X ΔX)
                (p15RectMatVec
                  (p15RectAdd (p15RectTranspose Y) ΔYT)
                  (roundedForwardSub fp b T₀ v₀)) i := by
              rw [p15_rectMatMul_matVec]
        _ = (1 + θ i) *
              p15RoundedRectMatVec fp X
                (p15RoundedRectMatVec fp (p15RectTranspose Y)
                  (roundedForwardSub fp b T₀ v₀)) i := by
              rw [← hwInner, ← hwHat]
    rw [hscaled]
    have hx₁i := congrFun hx₁ i
    rw [hx₁i, hrhs i]
    ring

end HighamBench
