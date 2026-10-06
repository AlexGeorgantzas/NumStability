import NumStability.Analysis.FloatingPointArithmetic

namespace HighamBenchCandidate

open NumStability
open scoped BigOperators

/-- The finite binary format, extended above its largest exponent solely to
describe rounding before the paper's no-overflow condition is imposed. This
retains subnormal values at the lower end. -/
def roundingRange (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  fmt.finiteSystem x ∨
    ∃ (negative : Bool) (m : ℕ) (e : ℤ),
      fmt.normalizedMantissa m ∧ fmt.emax < e ∧
        x = fmt.normalizedValue negative m e

/-- Algorithm 3.1, starting with the first input. Each addition is rounded to
nearest with arbitrary tie choice; all computed values are finite, expressing
the paper's no-overflow convention. The extended rounding range permits an
exact sum just above the largest finite value to round back to that value. -/
def recursiveTrace (fmt : FloatingPointFormat) (n : ℕ) (hn : 0 < n)
    (p s : Fin n → ℝ) : Prop :=
  s ⟨0, hn⟩ = p ⟨0, hn⟩ ∧
    (∀ i : Fin (n - 1),
      FloatingPointFormat.nearestRoundingIn (roundingRange fmt)
        (s ⟨i.val, by omega⟩ + p ⟨i.val + 1, by omega⟩)
        (s ⟨i.val + 1, by omega⟩)) ∧
    (∀ i : Fin n, fmt.finiteSystem (s i))

/-- Rump, Theorem 3.4, equation (3.5). The library's recursive-sum definition
uses an abstract relative-error model; its concrete finite trace fixes ties to
even. This trace states the paper's nearest-rounding and no-overflow domain. -/
theorem target :
    ∀ (fmt : FloatingPointFormat), fmt.beta = 2 →
      ∀ (n : ℕ) (hn : 0 < n) (p s : Fin n → ℝ),
        (∀ i : Fin n, fmt.finiteSystem (p i)) →
        recursiveTrace fmt n hn p s →
        |s ⟨n - 1, by omega⟩ - ∑ i : Fin n, p i| ≤
          ((n - 1 : ℕ) : ℝ) * fmt.unitRoundoff *
            ∑ i : Fin n, |p i| := by
  sorry

end HighamBenchCandidate
