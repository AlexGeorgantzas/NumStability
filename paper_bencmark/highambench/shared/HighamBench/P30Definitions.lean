import Mathlib.Data.Real.Basic

namespace HighamBench

/-- The dimension-only upper bound for `lambda_max (L L^T)` in equation (3.7). -/
noncomputable def p30BbkFactorUpperBound (n : ℕ) : ℝ :=
  4 * (n : ℝ) ^ 2 - 3 * (n : ℝ)

/-- The final perturbation-ratio upper bound for a negative-definite input in Section 5. -/
noncomputable def p30NegativeDefiniteRatioUpperBound
    (n : ℕ) (delta aFrobeniusNorm : ℝ) : ℝ :=
  1 + p30BbkFactorUpperBound n * delta / aFrobeniusNorm

end HighamBench
