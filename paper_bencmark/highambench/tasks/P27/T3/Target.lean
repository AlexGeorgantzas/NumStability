import HighamBench.P27Definitions

namespace HighamBench

/-- P27-T3: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p27_t3_theorem3_2 {k q : ℕ} (data : P27Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p27StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p27StrongFactor k q data.f) := by
  -- PROOF_START P27-T3-H001
  sorry

end HighamBench
