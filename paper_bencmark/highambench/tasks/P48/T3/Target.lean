import HighamBench.P48Definitions

namespace HighamBench

/-- P48-T3: the invariant-subspace conclusion of Proposition 3.4. -/
theorem p48_t3_rank_breakdown_invariant
    (n m : ℕ) (hm : 1 ≤ m)
    (v : ℤ → Fin n → ℝ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hstep : ∀ j, A (v j) = v (j + 1))
    (hbreak : ¬ LinearIndependent ℝ (p48BreakdownDirections v m)) :
    ∀ x ∈ p48LaurentSpan v (m + 1),
      A x ∈ p48LaurentSpan v (m + 1) := by
  -- PROOF_START P48-T3-H001
  sorry

end HighamBench
