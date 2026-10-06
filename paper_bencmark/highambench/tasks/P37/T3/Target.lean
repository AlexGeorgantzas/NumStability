import HighamBench.P37Definitions

namespace HighamBench

/-- P37-T3: the shifted-vector spanning equalities in Theorem 6.1. -/
theorem p37_t3_consecutive_shifted_vectors_span
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (hA : Function.Bijective A)
    (B : Fin n → ℝ) (hB : B ≠ 0)
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hv0 : v 0 = B)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (s : ℤ) :
    p37TwoSidedSpan v = p37ConsecutiveSpan v s n ∧
      p37ConsecutiveSpan v s n = p37KrylovSpan A (v s) n ∧
      p37KrylovSpan A (v s) n = p37KrylovSpan A B n := by
  -- PROOF_START P37-T3-H001
  sorry

end HighamBench
