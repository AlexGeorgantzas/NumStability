import HighamBench.P57Definitions

open scoped BigOperators

namespace HighamBench

/-- P57-T3: the interior-interval positivity argument in Theorem 1. -/
theorem p57_t3_denominator_positive_between_nodes
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (hdpos : 0 < d) (hdn : d ≤ n) (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1)) :
    0 < p57Denominator nodes n d x := by
  -- PROOF_START P57-T3-H001
  sorry

end HighamBench
