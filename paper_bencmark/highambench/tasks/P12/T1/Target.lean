import HighamBench.P12Definitions

namespace HighamBench

theorem p12_t1_exact_subtraction
    (fmt : P12RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P12NormalizedExponentRepresentation fmt x ex)
    (hy : P12NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p12FaithfulInFormat fmt (x - y) rounded) :
    p12FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P12-T1-H001
  sorry

end HighamBench
