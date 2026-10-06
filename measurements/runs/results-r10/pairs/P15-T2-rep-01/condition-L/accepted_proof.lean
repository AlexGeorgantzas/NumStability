import HighamBench.P15Definitions
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace HighamBench

open scoped BigOperators

/- The benchmark's floating-point record deliberately has the same primitive
interface as the library model.  This adapter lets us reuse the library's
checked dot-product and triangular-solve analyses. -/
noncomputable def p15FPModel (fp : StandardFPModel) : NumStability.FPModel where
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

lemma p15_forwardSubSteps_eq (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      NumStability.fl_forwardSub_steps (p15FPModel fp) n L v k hk x =
        roundedForwardSubSteps fp n L v k hk x := by
  intro k
  induction k with
  | zero =>
      intro hk x
      rfl
  | succ k ih =>
      intro hk x
      simp only [NumStability.fl_forwardSub_steps, roundedForwardSubSteps]
      apply ih

lemma p15_forwardSub_eq (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n) :
    NumStability.fl_forwardSub (p15FPModel fp) n L v =
      roundedForwardSub fp n L v := by
  unfold NumStability.fl_forwardSub roundedForwardSub
  exact p15_forwardSubSteps_eq fp n L v n (le_refl n) (fun _ ↦ 0)

lemma p15_frobNorm_of_componentwise_bound {m n : ℕ}
    (fp : StandardFPModel) (A E : P15RectMatrix m n)
    (hn : GammaValid fp.u n)
    (hE : ∀ i j, |E i j| ≤ gamma fp.u n * |A i j|) :
    p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm A := by
  let G : P15RectMatrix m n := fun i j ↦ gamma fp.u n * |A i j|
  have hvalid : NumStability.gammaValid (p15FPModel fp) n := hn
  have hgamma : 0 ≤ gamma fp.u n :=
    NumStability.gamma_nonneg (p15FPModel fp) hvalid
  have hraw : NumStability.frobNormRect E ≤
      NumStability.frobNormRect G :=
    NumStability.frobNormRect_le_of_entry_abs_le E G
      (fun i j ↦ mul_nonneg hgamma (abs_nonneg _)) hE
  have hG : NumStability.frobNormRect G =
      gamma fp.u n * NumStability.frobNormRect A := by
    calc
      NumStability.frobNormRect G =
          |gamma fp.u n| *
            NumStability.frobNormRect (fun i j ↦ |A i j|) := by
              simpa [G] using
                (NumStability.frobNormRect_smul (gamma fp.u n)
                  (fun i j ↦ |A i j|))
      _ = gamma fp.u n * NumStability.frobNormRect A := by
              rw [abs_of_nonneg hgamma, NumStability.frobNormRect_abs]
  change NumStability.frobNormRect E ≤
    gamma fp.u n * NumStability.frobNormRect A
  rw [← hG]
  exact hraw

lemma p15_roundedRectMatVec_backward_error {m n : ℕ}
    (fp : StandardFPModel) (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hn : GammaValid fp.u n) :
    ∃ E : P15RectMatrix m n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A E) x := by
  have hvalid : NumStability.gammaValid (p15FPModel fp) n := hn
  obtain ⟨E, hE, heq⟩ :=
    NumStability.matVec_backward_error (p15FPModel fp) m n A x hvalid
  refine ⟨E, p15_frobNorm_of_componentwise_bound fp A E hn hE, ?_⟩
  funext i
  exact heq i

lemma p15_roundedForwardSub_backward_error {n : ℕ}
    (fp : StandardFPModel) (L : P15Matrix n) (v : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hn : GammaValid fp.u n) :
    ∃ E : P15Matrix n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L E) (roundedForwardSub fp n L v) = v := by
  have hvalid : NumStability.gammaValid (p15FPModel fp) n := hn
  obtain ⟨E, hE, heq⟩ :=
    NumStability.forwardSub_backward_error (p15FPModel fp) n L v
      hdiag hlower hvalid
  rw [p15_forwardSub_eq] at heq
  refine ⟨E, p15_frobNorm_of_componentwise_bound fp L E hn hE, ?_⟩
  funext i
  simpa only [p15RectMatVec, p15RectAdd] using heq i

lemma p15_rectMatVec_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  calc
    ∑ j : Fin p, (∑ k : Fin n, A i k * B k j) * x j =
        ∑ j : Fin p, ∑ k : Fin n, (A i k * B k j) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ k : Fin n, ∑ j : Fin p, (A i k * B k j) * x j :=
          Finset.sum_comm
    _ = ∑ k : Fin n, A i k * (∑ j : Fin p, B k j * x j) := by
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
  obtain ⟨ΔT₀, hΔT₀, hsolve₀⟩ :=
    p15_roundedForwardSub_backward_error fp T₀ v₀
      hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hΔYT, hinner⟩ :=
    p15_roundedRectMatVec_backward_error fp (p15RectTranspose Y)
      (roundedForwardSub fp b T₀ v₀) hb
  obtain ⟨ΔX, hΔX, hhat⟩ :=
    p15_roundedRectMatVec_backward_error fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) hr
  let θ : P15Vector b := fun i ↦
    Classical.choose (fp.model_sub (v₁ i)
      (p15RoundedRectMatVec fp X
        (p15RoundedRectMatVec fp (p15RectTranspose Y)
          (roundedForwardSub fp b T₀ v₀)) i))
  have hθ : ∀ i, |θ i| ≤ fp.u := by
    intro i
    exact (Classical.choose_spec (fp.model_sub (v₁ i)
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
    exact (Classical.choose_spec (fp.model_sub (v₁ i)
      (p15RoundedRectMatVec fp X
        (p15RoundedRectMatVec fp (p15RectTranspose Y)
          (roundedForwardSub fp b T₀ v₀)) i))).2
  obtain ⟨ΔT₁, hΔT₁, hsolve₁⟩ :=
    p15_roundedForwardSub_backward_error fp T₁
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
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, hsolve₀,
    hinner, hhat, hrhs, hsolve₁, ?_, ?_⟩
  · intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring
  · intro i
    have hmatrix :
        p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ =
          fun i j ↦ (1 + θ i) *
            p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT) i j := by
      funext i j
      simp only [p15RectAdd, ΔT₁₀]
      ring
    have hlr :
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀)
            (roundedForwardSub fp b T₀ v₀) i =
          (1 + θ i) *
            p15RoundedRectMatVec fp X
              (p15RoundedRectMatVec fp (p15RectTranspose Y)
                (roundedForwardSub fp b T₀ v₀)) i := by
      rw [hmatrix]
      unfold p15RectMatVec
      change (∑ j : Fin b,
        ((1 + θ i) *
          p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT) i j) *
          roundedForwardSub fp b T₀ v₀ j) = _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      apply congrArg (fun z : ℝ ↦ (1 + θ i) * z)
      have hassoc := p15_rectMatVec_mul (p15RectAdd X ΔX)
        (p15RectAdd (p15RectTranspose Y) ΔYT)
        (roundedForwardSub fp b T₀ v₀)
      have hassoc_i := congrFun hassoc i
      rw [← hinner] at hassoc_i
      exact hassoc_i.trans (congrFun hhat.symm i)
    rw [hlr, congrFun hsolve₁ i, hrhs i]
    ring

end HighamBench
