import HighamBench.P65Definitions

namespace HighamBench

open scoped BigOperators

/-- Theorem 3.1, recursive-block and pairwise-outer specialization. -/
theorem p65_t2_fabsum_backward_error
    (fp : P65FPModel) (b r : ℕ)
    (x : Fin (2 ^ r) → Fin b → ℝ)
    (hb : 0 < b)
    (hbvalid : P65GammaValid fp.u (b - 1))
    (hrvalid : P65GammaValid fp.u r) :
    ∃ μ : Fin (2 ^ r) → Fin b → ℝ,
      (∀ i j, |μ i j| ≤
        p65Gamma fp.u (b - 1) + p65Gamma fp.u r +
          p65Gamma fp.u (b - 1) * p65Gamma fp.u r) ∧
      p65FABsum fp b r x =
        ∑ i : Fin (2 ^ r), ∑ j : Fin b, x i j * (1 + μ i j) := by
  -- PROOF_START P65-T2-H001
  sorry

end HighamBench
