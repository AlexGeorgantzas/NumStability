import HighamBench.P43Definitions

open scoped BigOperators

namespace HighamBench

/-- P43-T3: the inverse-action and multiplier bounds used in Theorem 3.6. -/
theorem p43_t3_calu_multiplier_growth
    (b H : ℕ) (ell : ℕ → ℕ → ℕ → ℝ)
    (probeIn probeOut z : ℕ → ℕ → ℝ)
    (hp : P43CALUMultiplierProcess b H ell probeIn probeOut z) :
    (∀ h, h < H → ∀ i, i < b →
      |probeOut h i| ≤ (2 : ℝ) ^ i) ∧
    (∀ i, i < b → |z H i| ≤ (2 : ℝ) ^ (b * H)) := by
  -- PROOF_START P43-T3-H001
  sorry

end HighamBench
