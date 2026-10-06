import HighamBench.P50Definitions

namespace HighamBench

/-- P50-T3: the real scalar specialization of the factorization in Lemma 3.4. -/
theorem p50_t3_first_companion_factorization
    (m : ℕ) (hm : 0 < m) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p50MatMul (p50Multiplier m A alpha beta)
        (p50FirstCompanion m hm A alpha beta) =
      fun i j => if i = j then p50Polynomial m A alpha beta else 0 := by
  -- PROOF_START P50-T3-H001
  sorry

end HighamBench
