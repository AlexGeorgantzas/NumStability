import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace HighamBench

open scoped BigOperators

/-- The vector 1-norm used by the block estimator. -/
noncomputable def p31VecOneNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, |x i|

/-- The real sign convention used in Algorithms 2.1--2.4, including `sign 0 = 1`. -/
noncomputable def p31Sign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

/-- The explicit upper-triangular entries of the worst-case family `A_n(alpha)`. -/
noncomputable def p31WorstCaseEntry {n : ℕ}
    (alpha : ℝ) (i j : Fin n) : ℝ :=
  if i.val ≤ j.val then -((-alpha) ^ (j.val - i.val)) else 0

/-- The estimate obtained after `p` visited columns in the worst-case example. -/
noncomputable def p31WorstCaseEstimate (alpha : ℝ) (p : ℕ) : ℝ :=
  (1 - alpha ^ p) / (1 - alpha)

end HighamBench
