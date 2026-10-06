import HighamBench.P66Definitions

namespace HighamBench

open scoped BigOperators

/-- Proposition 3.2, two-level equal-block specialization. -/
theorem p66_t2_two_level_superblock_dot_error
    (fp : P66FPModel) (b : ℕ)
    (x y : Fin b → Fin b → ℝ)
    (hb : 0 < b)
    (hvalid : P66GammaValid fp.u (2 * b - 1)) :
    |p66SuperblockDot fp b x y -
      ∑ i : Fin b, ∑ j : Fin b, x i j * y i j| ≤
      p66Gamma fp.u (2 * b - 1) *
        ∑ i : Fin b, ∑ j : Fin b, |x i j * y i j| := by
  -- PROOF_START P66-T2-H001
  sorry

end HighamBench
