import Mathlib.Data.Real.Basic

namespace HighamBench

structure P12RadixFormat where
  beta : ℕ
  precision : ℕ
  emin : ℤ
  emax : ℤ
  beta_ge_two : 2 ≤ beta
  precision_pos : 0 < precision
  emin_le_emax : emin ≤ emax

namespace P12RadixFormat

def betaR (fmt : P12RadixFormat) : ℝ :=
  fmt.beta

def minNormalMantissa (fmt : P12RadixFormat) : ℕ :=
  fmt.beta ^ (fmt.precision - 1)

def normalizedMantissa (fmt : P12RadixFormat) (m : ℕ) : Prop :=
  fmt.minNormalMantissa ≤ m ∧ m < fmt.beta ^ fmt.precision

def subnormalMantissa (fmt : P12RadixFormat) (m : ℕ) : Prop :=
  0 < m ∧ m < fmt.minNormalMantissa

def normalEmin (fmt : P12RadixFormat) : ℤ :=
  fmt.emin + (fmt.precision : ℤ)

def normalEmax (fmt : P12RadixFormat) : ℤ :=
  fmt.emax + (fmt.precision : ℤ)

def normalizedExponentInRange (fmt : P12RadixFormat) (e : ℤ) : Prop :=
  fmt.normalEmin ≤ e ∧ e ≤ fmt.normalEmax

def signValue (_fmt : P12RadixFormat) (negative : Bool) : ℝ :=
  if negative then -1 else 1

noncomputable def normalizedValue
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) (e : ℤ) : ℝ :=
  fmt.signValue negative * (m : ℝ) *
    fmt.betaR ^ (e - (fmt.precision : ℤ))

noncomputable def subnormalValue
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) : ℝ :=
  fmt.signValue negative * (m : ℝ) * fmt.betaR ^ fmt.emin

end P12RadixFormat

def P12NormalizedExponentRepresentation
    (fmt : P12RadixFormat) (x : ℝ) (e : ℤ) : Prop :=
  ∃ negative m,
    fmt.normalizedMantissa m ∧
    fmt.normalizedExponentInRange e ∧
    x = fmt.normalizedValue negative m e

def p12FiniteSystem (fmt : P12RadixFormat) (x : ℝ) : Prop :=
  x = 0 ∨
    (∃ negative m e,
      fmt.normalizedMantissa m ∧
      fmt.normalizedExponentInRange e ∧
      x = fmt.normalizedValue negative m e) ∨
    ∃ negative m,
      fmt.subnormalMantissa m ∧
      x = fmt.subnormalValue negative m

def p12Faithful (representable : ℝ → Prop) (exact rounded : ℝ) : Prop :=
  representable rounded ∧
    ∀ candidate, representable candidate →
      ¬ ((rounded < candidate ∧ candidate ≤ exact) ∨
        (exact ≤ candidate ∧ candidate < rounded))

def p12FaithfulInFormat
    (fmt : P12RadixFormat) (exact rounded : ℝ) : Prop :=
  p12Faithful (p12FiniteSystem fmt) exact rounded

end HighamBench
