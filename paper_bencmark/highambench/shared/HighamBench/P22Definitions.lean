import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace HighamBench

/-- The standard accumulated rounding-error constant from equation (2.2). -/
noncomputable def p22Gamma (u : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) * u) / (1 - (k : ℝ) * u)

/-- The VS basis function from equation (4.2). -/
noncomputable def p22VSBasis (n : ℕ) (i : Fin (n + 1)) (t : ℝ) : ℝ :=
  t ^ i.val * (1 - t) ^ (n - i.val)

/-- The coefficientwise absolute sum used in the VS forward bound. -/
noncomputable def p22VSConditionSum
    (n : ℕ) (c : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), |c i| * p22VSBasis n i t

/-- The computable first-order relative-error envelope in Theorem 3.1. -/
noncomputable def p22RunningRelativeEnvelope
    (computed absoluteBudget : ℝ) : ℝ :=
  absoluteBudget / |computed|

end HighamBench
