import HighamBench.P03Definitions

namespace HighamBench

theorem p03_t3_normwise_residual_contraction
    {n : ℕ} (run : P03NormwiseIRRun n) (i : ℕ) :
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
      p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
  -- PROOF_START P03-T3-H001
  sorry

end HighamBench
