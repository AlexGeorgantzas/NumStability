import Mathlib

namespace HighamBench

/-- The ratio of two consecutive residual norms used in the proof of Theorem 2.3. -/
noncomputable def p39ResidualRatio (residual : ℕ → ℝ) (k : ℕ) : ℝ :=
  residual (k + 1) / residual k

/-- The scaled residual ratio introduced in the R-order part of Theorem 2.3. -/
noncomputable def p39ScaledResidualRatio (residual : ℕ → ℝ) (D : ℝ) (k : ℕ) : ℝ :=
  D * p39ResidualRatio residual k

end HighamBench
