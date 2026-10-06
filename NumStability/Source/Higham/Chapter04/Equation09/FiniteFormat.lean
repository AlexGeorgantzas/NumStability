import NumStability.Algorithms.Summation.Compensated.Kahan.ErrorBounds
import NumStability.Source.Higham.Chapter04.Equation08.FiniteFormat

open Classical
open scoped BigOperators

namespace NumStability

/-!
# Higham equation (4.9): finite-format realization

Finite binary round-to-even forward-error consequence of the equation-(4.8)
backward-error closure.
-/

/-- **Higham equation (4.9)** in the finite binary round-to-even format: the
forward-error form of (4.8) for ordinary Kahan compensated summation.

Under the same hypotheses as `kahanFF_kahanSum_backward_error`,

`|Eₙ| = |Ŝₙ − Σᵢ xᵢ| ≤ (2u + 2(3 + 40n)u²) · Σᵢ |xᵢ|`,

an explicit realization of Higham's `|Eₙ| ≤ (2u + O(nu²)) Σ|xᵢ|`.  Reference:
Higham, 2nd ed., §4.3, equation (4.9), p. 85. -/
theorem kahanFF_kahanSum_forward_error
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hY : ∀ i : Fin n,
      fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).y)
    (hstep : ∀ i : Fin n,
      (fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).temp ∧
        |(kahanTrace (kahanFF_model fmt) v i).y| ≤
          |(kahanTrace (kahanFF_model fmt) v i).temp| ∧
        fmt.finiteNormalRange
          ((kahanTrace (kahanFF_model fmt) v i).temp +
            (kahanTrace (kahanFF_model fmt) v i).y)) ∨
        (kahanTrace (kahanFF_model fmt) v i).temp = 0)
    (huSmall : fmt.unitRoundoff ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fmt.unitRoundoff ≤ 1) :
    |fl_kahanSum (kahanFF_model fmt) n v - ∑ i : Fin n, v i| ≤
      (2 * fmt.unitRoundoff +
          2 * (3 + 40 * (n : ℝ)) * fmt.unitRoundoff ^ 2) *
        ∑ i : Fin n, |v i| :=
  fl_kahanSum_forward_error_bound_of_backward (kahanFF_model fmt) n v
    (kahanFF_kahanSum_backward_error fmt hbeta ht n v hY hstep huSmall hBudget)

end NumStability
