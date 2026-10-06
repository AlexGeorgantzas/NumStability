import HighamBench.P24Definitions

namespace HighamBench

open scoped BigOperators Topology
open Filter

/-- P24-T3: the cycle-reindexed linear majorant constructed in Lemma 21. -/
theorem p24_t3_lemma21_linear_convergence
    (data : P24Lemma21Data) :
    (∀ n, Summable (fun k : ℕ => 2 * data.width (n + 1 + k))) ∧
      (∀ n,
        data.relativeEven n ≤
            p24LinearMajorant data.toP24WidthSequence n ∧
          data.relativeOdd n ≤
            p24LinearMajorant data.toP24WidthSequence n) ∧
      (∀ n, 0 ≤ p24LinearMajorant data.toP24WidthSequence n) ∧
      (∀ n, p24LinearMajorant data.toP24WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p24LinearMajorant data.toP24WidthSequence n) ∧
      Tendsto (p24LinearMajorant data.toP24WidthSequence) atTop (nhds 0) := by
  -- PROOF_START P24-T3-H001
  sorry

end HighamBench
