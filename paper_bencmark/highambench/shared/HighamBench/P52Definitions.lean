import Mathlib

namespace HighamBench

/-- Square complex matrices used in the scaling-and-squaring recurrences of
P52. -/
abbrev P52Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The scaled matrix `2⁻ˢ A` in Section 6. -/
noncomputable def p52DyadicScale {n : ℕ} (s : ℕ) (A : P52Matrix n) :
    P52Matrix n :=
  (((2 : ℂ) ^ s)⁻¹) • A

/-- The coupled squaring recurrence (6.4), started from its scaled values.
The first component is the exponential approximation and the second is its
Fréchet-derivative approximation. -/
noncomputable def p52ScalingSquaring {n : ℕ} :
    ℕ → P52Matrix n → P52Matrix n → P52Matrix n × P52Matrix n
  | 0, X, L => (X, L)
  | k + 1, X, L =>
      let previous := p52ScalingSquaring k X L
      (previous.1 * previous.1,
        previous.1 * previous.2 + previous.2 * previous.1)

end HighamBench
