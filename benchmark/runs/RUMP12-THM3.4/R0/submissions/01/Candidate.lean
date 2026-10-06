import Mathlib

namespace HighamBenchCandidate

/-- A binary floating-point format with unbounded upper exponent (the paper's
no-overflow setting). `minExponent` is the exponent of the least positive
subnormal, and `precision` is the number of significand bits. -/
structure BinaryFormat where
  precision : ℕ
  precision_pos : 0 < precision
  minExponent : ℤ
  one_in_normal_range : minExponent ≤ -(precision : ℤ)

/-- Finite values in the binary format, including zero and subnormals. -/
def BinaryFormat.representable (F : BinaryFormat) (x : ℝ) : Prop :=
  ∃ (m : ℤ) (e : ℤ),
    F.minExponent ≤ e ∧ m.natAbs < 2 ^ F.precision ∧
      x = (m : ℝ) * (2 : ℝ) ^ e

/-- Any choice of a closest representable value is a rounding to nearest;
ties may be resolved either way. -/
def BinaryFormat.roundsToNearest (F : BinaryFormat) (x y : ℝ) : Prop :=
  F.representable y ∧
    ∀ z : ℝ, F.representable z → |y - x| ≤ |z - x|

/-- Relative rounding error unit, the gap from 1 to its predecessor. -/
noncomputable def BinaryFormat.unitRoundoff (F : BinaryFormat) : ℝ :=
  (2 : ℝ) ^ (-(F.precision : ℤ))

/-- The successive computed sums of Algorithm 3.1 for a vector of length
`n + 1`. The first sum is the first input; every later addition is rounded. -/
def BinaryFormat.recursiveSum
    (F : BinaryFormat) {n : ℕ} (p s : Fin (n + 1) → ℝ) : Prop :=
  s 0 = p 0 ∧
    ∀ i : Fin n,
      F.roundsToNearest (s (Fin.castSucc i) + p (Fin.succ i))
        (s (Fin.succ i))

/-- Rump, Theorem 3.4, equation (3.5), with `n + 1` inputs. -/
theorem target :
    ∀ (F : BinaryFormat) (n : ℕ)
      (p s : Fin (n + 1) → ℝ),
      (∀ i, F.representable (p i)) →
      F.recursiveSum p s →
      |s (Fin.last n) - ∑ i, p i| ≤
        (n : ℝ) * F.unitRoundoff * ∑ i, |p i| := by
  sorry

end HighamBenchCandidate
