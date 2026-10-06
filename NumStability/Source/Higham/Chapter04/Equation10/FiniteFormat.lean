import NumStability.Algorithms.Summation.Compensated.Alternative.Core
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Source.Higham.Chapter04.Equation10.AbstractModel

open Classical
open scoped BigOperators

namespace NumStability

/-!
# Higham equation (4.10): finite-format realization

Finite binary round-to-even specialization of the alternative compensated-
summation backward-error result.
-/

/-- The running main sum before index `i` of the alternative compensated
summation, computed by the safe-completion model. -/
noncomputable def kahanFF_prefix (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  alternativeCompensatedPrefixSum (kahanFF_model fmt) v i.val
    (Nat.le_of_lt i.isLt)

/-- **Higham equation (4.10)** in the finite binary round-to-even format.

For the alternative compensated-summation variant on printed p. 85 (corrections
accumulated separately by recursive summation, then added back), computed in the
safe-completion finite model `kahanFF_model fmt` with base `beta = 2` and
precision `1 < t`, if the correction formula (4.7) applies at every step
(`kahanFF_stepCondition` on each running sum and term) and `n·u ≤ 1/10`, then the
computed sum has the Kielbasiński/Neumaier backward-error representation

`Ŝₙ = Σᵢ (1 + μᵢ) xᵢ`,  with  `|μᵢ| ≤ 2u + n²u²`,

where `u = fmt.unitRoundoff`.  Reference: Higham, *Accuracy and Stability of
Numerical Algorithms*, 2nd ed., §4.3, equation (4.10), p. 85; Kielbasiński
[731, 1994]; Neumaier [883, 1974]. -/
theorem kahanFF_alternativeCompensatedSum_backward_error
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hstep : ∀ i : Fin n, kahanFF_stepCondition fmt (kahanFF_prefix fmt v i) (v i))
    (hsmall : (n : ℝ) * fmt.unitRoundoff ≤ 1 / 10) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fmt.unitRoundoff + (n : ℝ) ^ 2 * fmt.unitRoundoff ^ 2) ∧
      fl_alternativeCompensatedSum (kahanFF_model fmt) n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  refine
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_higham_cap
      (kahanFF_model fmt) n v (fun i => ?_) hsmall
  exact kahanFF_step_exact fmt hbeta ht (kahanFF_prefix fmt v i) (v i) (hstep i)

end NumStability
