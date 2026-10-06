import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt

namespace HighamBench

/-- The relaxed product-error constant in equation (2.1). -/
noncomputable def p21GammaTilde (n : ℕ) (u lambda : ℝ) : ℝ :=
  Real.exp
      (lambda * Real.sqrt (n : ℝ) * u +
        (n : ℝ) * u ^ 2 / (1 - u)) -
    1

/-- The probability lower bound in equation (2.2). -/
noncomputable def p21ProductProbability (u lambda : ℝ) : ℝ :=
  1 - 2 * Real.exp (-(lambda ^ 2 * (1 - u) ^ 2) / 2)

/-- The union-bound probability used in equation (3.1). -/
noncomputable def p21UnionProbability (u lambda : ℝ) (count : ℕ) : ℝ :=
  1 - (count : ℝ) * (1 - p21ProductProbability u lambda)

end HighamBench
