import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace HighamBench

private def StandardFPModel.toNumStability (fp : StandardFPModel) :
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

private lemma p15RectFrobNorm_le_mul_of_entrywise
    {m n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (A E : P15RectMatrix m n)
    (hE : ∀ i j, |E i j| ≤ c * |A i j|) :
    p15RectFrobNorm E ≤ c * p15RectFrobNorm A := by
  have hraw :
      NumStability.frobNormRect E ≤
        NumStability.frobNormRect (fun i j ↦ c * |A i j|) :=
    NumStability.frobNormRect_le_of_entry_abs_le E
      (fun i j ↦ c * |A i j|)
      (fun i j ↦ mul_nonneg hc (abs_nonneg _)) hE
  change NumStability.frobNormRect E ≤ c * NumStability.frobNormRect A
  calc
    NumStability.frobNormRect E
        ≤ NumStability.frobNormRect (fun i j ↦ c * |A i j|) := hraw
    _ = |c| * NumStability.frobNormRect (fun i j ↦ |A i j|) := by
      simpa using
        (NumStability.frobNormRect_smul c (fun i j ↦ |A i j|))
    _ = c * NumStability.frobNormRect A := by
      rw [abs_of_nonneg hc, NumStability.frobNormRect_abs]

private lemma p15RectMatVec_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

private lemma p15RoundedRectMatVec_eq_numStability
    (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ) :
    p15RoundedRectMatVec fp A x =
      NumStability.fl_matVec fp.toNumStability m n A x := by
  rfl

private lemma roundedForwardSub_eq_numStability
    (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n) :
    roundedForwardSub fp n L v =
      NumStability.fl_forwardSub fp.toNumStability n L v := by
  have hsteps : ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      roundedForwardSubSteps fp n L v k hk x =
        NumStability.fl_forwardSub_steps fp.toNumStability n L v k hk x := by
    intro k
    induction k with
    | zero =>
        intro hk x
        rfl
    | succ k ih =>
        intro hk x
        unfold roundedForwardSubSteps NumStability.fl_forwardSub_steps
        apply ih
  exact hsteps n (le_refl n) (fun _ ↦ 0)

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
  let nfp := fp.toNumStability
  have hbNS : NumStability.gammaValid nfp b := by
    exact hb
  have hrNS : NumStability.gammaValid nfp r := by
    exact hr
  have hgammaB : 0 ≤ gamma fp.u b := by
    simpa [nfp, StandardFPModel.toNumStability, gamma,
      NumStability.gamma] using
      (NumStability.gamma_nonneg nfp hbNS)
  have hgammaR : 0 ≤ gamma fp.u r := by
    simpa [nfp, StandardFPModel.toNumStability, gamma,
      NumStability.gamma] using
      (NumStability.gamma_nonneg nfp hrNS)

  obtain ⟨ΔT₀, hΔT₀entry, hT₀solveNS⟩ :=
    NumStability.forwardSub_backward_error nfp b T₀ v₀
      hT₀diag hT₀lower hbNS
  have hΔT₀entry' :
      ∀ i j, |ΔT₀ i j| ≤ gamma fp.u b * |T₀ i j| := by
    intro i j
    simpa [nfp, StandardFPModel.toNumStability, gamma,
      NumStability.gamma] using hΔT₀entry i j
  have hΔT₀norm :
      p15RectFrobNorm ΔT₀ ≤ gamma fp.u b * p15RectFrobNorm T₀ :=
    p15RectFrobNorm_le_mul_of_entrywise
      (gamma fp.u b) hgammaB T₀ ΔT₀ hΔT₀entry'
  have hT₀solve :
      p15RectMatVec (p15RectAdd T₀ ΔT₀)
          (roundedForwardSub fp b T₀ v₀) = v₀ := by
    funext i
    rw [roundedForwardSub_eq_numStability]
    simpa [p15RectMatVec, p15RectAdd] using hT₀solveNS i

  obtain ⟨ΔYT, hΔYTentry, hInnerNS⟩ :=
    NumStability.matVec_backward_error nfp r b
      (p15RectTranspose Y) (roundedForwardSub fp b T₀ v₀) hbNS
  have hΔYTentry' :
      ∀ i j, |ΔYT i j| ≤
        gamma fp.u b * |p15RectTranspose Y i j| := by
    intro i j
    simpa [nfp, StandardFPModel.toNumStability, gamma,
      NumStability.gamma] using hΔYTentry i j
  have hΔYTnorm :
      p15RectFrobNorm ΔYT ≤
        gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) :=
    p15RectFrobNorm_le_mul_of_entrywise
      (gamma fp.u b) hgammaB (p15RectTranspose Y) ΔYT hΔYTentry'
  have hInner :
      p15RoundedRectMatVec fp (p15RectTranspose Y)
          (roundedForwardSub fp b T₀ v₀) =
        p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT)
          (roundedForwardSub fp b T₀ v₀) := by
    rw [p15RoundedRectMatVec_eq_numStability]
    funext i
    simpa [p15RectMatVec, p15RectAdd] using hInnerNS i

  obtain ⟨ΔX, hΔXentry, hHatNS⟩ :=
    NumStability.matVec_backward_error nfp b r X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) hrNS
  have hΔXentry' : ∀ i j, |ΔX i j| ≤ gamma fp.u r * |X i j| := by
    intro i j
    simpa [nfp, StandardFPModel.toNumStability, gamma,
      NumStability.gamma] using hΔXentry i j
  have hΔXnorm :
      p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X :=
    p15RectFrobNorm_le_mul_of_entrywise
      (gamma fp.u r) hgammaR X ΔX hΔXentry'
  have hHat :
      p15RoundedRectMatVec fp X
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) =
        p15RectMatVec (p15RectAdd X ΔX)
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) := by
    rw [p15RoundedRectMatVec_eq_numStability]
    funext i
    simpa [p15RectMatVec, p15RectAdd] using hHatNS i

  let x₀ := roundedForwardSub fp b T₀ v₀
  let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
  let wHat := p15RoundedRectMatVec fp X wInner
  let rhsHat : P15Vector b := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
  let θ : P15Vector b := fun i ↦
    Classical.choose (fp.model_sub (v₁ i) (wHat i))
  have hθ : ∀ i, |θ i| ≤ fp.u := by
    intro i
    exact (Classical.choose_spec (fp.model_sub (v₁ i) (wHat i))).1
  have hrhs : ∀ i, rhsHat i = (v₁ i - wHat i) * (1 + θ i) := by
    intro i
    exact (Classical.choose_spec (fp.model_sub (v₁ i) (wHat i))).2

  obtain ⟨ΔT₁, hΔT₁entry, hT₁solveNS⟩ :=
    NumStability.forwardSub_backward_error nfp b T₁ rhsHat
      hT₁diag hT₁lower hbNS
  have hΔT₁entry' :
      ∀ i j, |ΔT₁ i j| ≤ gamma fp.u b * |T₁ i j| := by
    intro i j
    simpa [nfp, StandardFPModel.toNumStability, gamma,
      NumStability.gamma] using hΔT₁entry i j
  have hΔT₁norm :
      p15RectFrobNorm ΔT₁ ≤ gamma fp.u b * p15RectFrobNorm T₁ :=
    p15RectFrobNorm_le_mul_of_entrywise
      (gamma fp.u b) hgammaB T₁ ΔT₁ hΔT₁entry'
  have hT₁solve :
      p15RectMatVec (p15RectAdd T₁ ΔT₁)
          (roundedForwardSub fp b T₁ rhsHat) = rhsHat := by
    funext i
    rw [roundedForwardSub_eq_numStability]
    simpa [p15RectMatVec, p15RectAdd] using hT₁solveNS i

  let ΔT₁₀ : P15Matrix b := fun i j ↦
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  have hT₁₀ : ∀ i j,
      p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
        (1 + θ i) *
          p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT) i j := by
    intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring

  have hInner' :
      wInner = p15RectMatVec
        (p15RectAdd (p15RectTranspose Y) ΔYT) x₀ := by
    exact hInner
  have hHat' :
      wHat = p15RectMatVec (p15RectAdd X ΔX) wInner := by
    exact hHat
  have hProductVec :
      p15RectMatVec
          (p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ = wHat := by
    rw [p15RectMatVec_mul, ← hInner', ← hHat']
  have hScaledVec : ∀ i,
      p15RectMatVec
          (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
        (1 + θ i) * wHat i := by
    intro i
    unfold p15RectMatVec
    simp_rw [hT₁₀ i]
    calc
      ∑ j : Fin b,
          ((1 + θ i) *
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j) * x₀ j =
          (1 + θ i) *
            ∑ j : Fin b,
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j * x₀ j := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
      _ = (1 + θ i) * wHat i := by
        rw [show (∑ j : Fin b,
            p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT) i j * x₀ j) =
            wHat i from congrFun hProductVec i]

  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀norm, hΔYTnorm, hΔXnorm, hθ, hΔT₁norm,
    hT₀solve, hInner', hHat', hrhs, hT₁solve, hT₁₀, ?_⟩
  intro i
  rw [hScaledVec i]
  rw [show p15RectMatVec (p15RectAdd T₁ ΔT₁)
      (roundedForwardSub fp b T₁ rhsHat) i = rhsHat i from
    congrFun hT₁solve i]
  rw [hrhs i]
  ring

end HighamBench
