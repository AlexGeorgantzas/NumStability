import HighamBench.P34Definitions

namespace HighamBench

/-- P34-T3: Lemma 4.1 and the structural guarantees of Algorithm 4.1. -/
theorem p34_t3_dqd2_refactorization
    (n q : ℕ) (b c : ℕ → ℝ)
    (hn : 0 < n) (hqpos : 0 < q) (hqn : q ≤ n)
    (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0)
    (hstop : q < n → b q = 0) :
    (∀ i, i < n → 0 ≤ p34DqdB q b c i) ∧
    (∀ i, i < n → 0 ≤ p34DqdC q b c i) ∧
    p34DqdB q b c 0 = 0 ∧
    p34UnitLowerBidiagonal n (p34DqdB q b c) *
        p34UnitLowerBidiagonal n (p34DqdC q b c) =
      p34UnitLowerBidiagonal n b * p34UnitLowerBidiagonal n c ∧
    (∀ i, 0 < i → i < n →
      (p34DqdB q b c i = 0 ↔ b i = 0)) ∧
    (∀ i, i < n → p34DqdC q b c i = 0 → c i = 0) ∧
    (∀ i, i < n → c i = 0 → p34DqdC q b c i ≠ 0 → i + 1 = q) ∧
    (∀ i, q ≤ i →
      p34DqdB q b c i = b i ∧ p34DqdC q b c i = c i) ∧
    4 * q ≤ 4 * n := by
  -- PROOF_START P34-T3-H001
  sorry

end HighamBench
