import HighamBench.P66Definitions

namespace HighamBench

open scoped BigOperators

/-- Two-level superblock summation forward error. -/
theorem p66_t1_two_level_superblock_sum_error
    (fp : P66FPModel) (b : ℕ) (x : Fin b → Fin b → ℝ)
    (hb : 0 < b)
    (hvalid : P66GammaValid fp.u (2 * (b - 1))) :
    |p66SuperblockSum fp b x -
      ∑ i : Fin b, ∑ j : Fin b, x i j| ≤
      p66Gamma fp.u (2 * (b - 1)) *
        ∑ i : Fin b, ∑ j : Fin b, |x i j| := by
  -- PROOF_START P66-T1-H001
  sorry

end HighamBench
