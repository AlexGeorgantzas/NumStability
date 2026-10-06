import HighamBench.P43Definitions

open scoped BigOperators

namespace HighamBench

/-- P43-T1: the scalar-panel arbitrary-height form of Theorem 3.4. -/
theorem p43_t1_calu_scalar_gepp_chain
    (H : ℕ) (a : ℕ → ℝ) (u r q : ℝ)
    (ha : ∀ i, i ≤ H → a i ≠ 0) :
    ∃ L U : Fin (H + 2) → Fin (H + 2) → ℝ,
      P43LUFactSpec (H + 2) (p43Chain H a u r q) L U ∧
        U (p43Last H) (p43Last H) = q - r / a 0 * u := by
  -- PROOF_START P43-T1-H001
  sorry

end HighamBench
