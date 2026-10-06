import HighamBench.P67Definitions

namespace HighamBench

open scoped BigOperators

/-- Section 2 multiword-product accumulation representation. -/
theorem p67_t1_multiword_accumulation
    (fp : P67FPModel) (p n : ℕ)
    (pairs : Fin (p * p) ≃ Fin p × Fin p)
    (a b : Fin p → Fin n → ℝ)
    (hp : 0 < p)
    (hvalid : P67GammaValid fp.u (p * p - 1)) :
    ∃ θ : Fin (p * p) → ℝ,
      (∀ t, |θ t| ≤ p67Gamma fp.u (p * p - 1)) ∧
      p67MultiwordDotMany fp p n pairs a b =
        ∑ t : Fin (p * p),
          p67BlockDot fp n (a (pairs t).1) (b (pairs t).2) * (1 + θ t) := by
  -- PROOF_START P67-T1-H001
  sorry

end HighamBench
