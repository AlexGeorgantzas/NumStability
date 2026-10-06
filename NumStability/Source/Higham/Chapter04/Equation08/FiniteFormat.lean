import NumStability.Algorithms.Summation.Compensated.Kahan.ErrorBounds
import NumStability.Algorithms.Summation.Compensated.Kahan.FiniteFormat

open Classical
open scoped BigOperators

namespace NumStability

/-!
# Higham equation (4.8): finite-format realization

Finite binary round-to-even closure of the ordinary Kahan backward-error
representation.
-/

/-- **Higham equation (4.8)** in the finite binary round-to-even format.

Ordinary Kahan compensated summation (Algorithm 4.2) computed in the
safe-completion finite model, base `beta = 2`, precision `1 < t`.  If the
correction formula (4.7) applies at every step (`hstep`: Dekker order with
normal range, or `temp = 0`) with each `y` representable (`hY`), and
`u ≤ 1/64`, `(3 + 40n)·u ≤ 1`, then

`Ŝₙ = Σᵢ (1 + μᵢ) xᵢ`,  with  `|μᵢ| ≤ 2u + 2(3 + 40n)u²`,

an explicit realization of Knuth/Kahan's `|μᵢ| ≤ 2u + O(nu²)`, where
`u = fmt.unitRoundoff`.  Reference: Higham, 2nd ed., §4.3, equation (4.8),
p. 85 (Knuth [744]; Kahan [688, 689]; Goldberg [496]). -/
theorem kahanFF_kahanSum_backward_error
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
    ∃ μ : Fin n → ℝ,
      (∀ i,
        |μ i| ≤
          2 * fmt.unitRoundoff +
            2 * (3 + 40 * (n : ℝ)) * fmt.unitRoundoff ^ 2) ∧
      fl_kahanSum (kahanFF_model fmt) n v = ∑ i : Fin n, v i * (1 + μ i) :=
  fl_kahanSum_backward_error_source_bound_of_exactSubTrace
    (kahanFF_model fmt) n v
    (kahanFF_kahan_correctionSub_exact fmt hbeta ht n v hY hstep)
    huSmall hBudget

end NumStability
