import HighamBench.P15Definitions

namespace HighamBench

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
  sorry

end HighamBench
