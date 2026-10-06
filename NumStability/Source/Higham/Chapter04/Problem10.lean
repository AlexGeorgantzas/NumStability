import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

/-!
# Higham Problem 4.10: Priest's six-term example

This source module records the exact-sum and IEEE single-precision facts for
the six-term example attributed to Priest in Higham Problem 4.10. Historical
`problem49...` names are retained alongside source-correct `problem410...`
aliases.
-/

/-! ### Higham Problem 4.10 / Priest six-term example -/

/-- The six-term family from Higham Problem 4.10, due to Priest.  The printed
source is `x₁ = 2^(t+1)`, `x₂ = 2^(t+1)-2`, and
`x₃ = x₄ = x₅ = x₆ = -(2^t-1)`. -/
noncomputable def problem49PriestInput (t : ℕ) : Fin 6 → ℝ :=
  fun i =>
    if i.val = 0 then (2 : ℝ) ^ (t + 1)
    else if i.val = 1 then (2 : ℝ) ^ (t + 1) - 2
    else -((2 : ℝ) ^ t - 1)

/-- Priest's six-term Problem 4.10 family has exact real sum `2`. -/
theorem problem49PriestInput_sum_eq_two (t : ℕ) :
    (∑ i : Fin 6, problem49PriestInput t i) = 2 := by
  norm_num [problem49PriestInput, Fin.sum_univ_succ]
  rw [pow_succ]
  ring_nf
  rfl

/-- The concrete IEEE-single instance in Higham Problem 4.10 uses `t = 24`. -/
theorem problem49PriestInput_t24_sum_eq_two :
    (∑ i : Fin 6, problem49PriestInput 24 i) = 2 := by
  exact problem49PriestInput_sum_eq_two 24

/-- Concrete decimal values of the `t = 24` IEEE-single instance. -/
theorem problem49PriestInput_t24_values :
    problem49PriestInput 24 0 = 33554432 ∧
    problem49PriestInput 24 1 = 33554430 ∧
    problem49PriestInput 24 2 = -16777215 ∧
    problem49PriestInput 24 3 = -16777215 ∧
    problem49PriestInput 24 4 = -16777215 ∧
    problem49PriestInput 24 5 = -16777215 := by
  norm_num [problem49PriestInput]
  rfl

/-- The first value `2^(24+1)` in the concrete Problem 4.10 instance is finite
in IEEE single precision. -/
theorem problem49PriestInput_t24_x1_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem49PriestInput 24 0) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 8388608, (26 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [FloatingPointFormat.exponentInRange,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [problem49PriestInput, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR,
      FloatingPointFormat.ieeeSingleFormat]

/-- The second value `2^(24+1)-2` in the concrete Problem 4.10 instance is
finite in IEEE single precision. -/
theorem problem49PriestInput_t24_x2_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem49PriestInput 24 1) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 16777215, (25 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [FloatingPointFormat.exponentInRange,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [problem49PriestInput, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR,
      FloatingPointFormat.ieeeSingleFormat]
    rfl

/-- The repeated tail value `-(2^24-1)` in the concrete Problem 4.10 instance is
finite in IEEE single precision. -/
theorem problem49PriestInput_t24_tail_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem49PriestInput 24 2) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨true, 16777215, (24 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [FloatingPointFormat.exponentInRange,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [problem49PriestInput, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR,
      FloatingPointFormat.ieeeSingleFormat]

/-- Every displayed input in the concrete Problem 4.10 instance is finite in
IEEE single precision. -/
theorem problem49PriestInput_t24_ieeeSingle_finiteSystem
    (i : Fin 6) :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem49PriestInput 24 i) := by
  fin_cases i
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_x1_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_x2_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_tail_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_tail_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_tail_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_tail_ieeeSingle_finiteSystem

/-- First nontrivial rounding fact in the local IEEE-single finite
round-to-even trace for Problem 4.10: the exact sum of the first two displayed
inputs is the midpoint `67108862`, so the tie-to-even rule selects
`67108864`. -/
theorem problem49PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864 :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
      (problem49PriestInput 24 0) (problem49PriestInput 24 1) =
        (67108864 : ℝ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa (26 : ℤ)
  let b : ℝ := fmt.normalizedValue false fmt.minNormalMantissa (27 : ℤ)
  let x : ℝ := (67108862 : ℝ)
  have hm : fmt.normalizedMantissa fmt.maxNormalMantissa :=
    fmt.maxNormalMantissa_normalized
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    exact ⟨false, (26 : ℤ), Or.inl ⟨rfl, rfl⟩⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_value : a = (67108860 : ℝ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      zpow_neg]
  have hb_value : b = (67108864 : ℝ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.minNormalMantissa,
      zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · norm_num [x, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
      exact Nat.cast_le.mpr (by norm_num)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxrange
  have hleft :
      a = fmt.normalizedValue false fmt.maxNormalMantissa (26 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hodd : ¬ FloatingPointFormat.evenMantissa fmt.maxNormalMantissa := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.maxNormalMantissa, FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd
  change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.add
        (problem49PriestInput 24 0) (problem49PriestInput 24 1)) =
        (67108864 : ℝ)
  have hxop :
      BasicOp.exact BasicOp.add
        (problem49PriestInput 24 0) (problem49PriestInput 24 1) = x := by
    norm_num [BasicOp.exact, problem49PriestInput, x]
    change ((33554432 : ℕ) : ℝ) + ((33554430 : ℕ) : ℝ) =
      ((67108862 : ℕ) : ℝ)
    rw [← Nat.cast_add]
  rw [hxop]
  simpa [fmt, hb_value] using hround

/-! Source-correct Problem 4.10 aliases.

The original declaration names used `problem49` before the current Chapter 4
PDF/source split was refreshed.  These aliases preserve the existing API while
giving ledger and lookup users names that match the printed problem number. -/

/-- Source-correct alias for the Priest six-term family in Problem 4.10. -/
noncomputable def problem410PriestInput (t : ℕ) : Fin 6 → ℝ :=
  problem49PriestInput t

/-- Priest's six-term Problem 4.10 family has exact real sum `2`. -/
theorem problem410PriestInput_sum_eq_two (t : ℕ) :
    (∑ i : Fin 6, problem410PriestInput t i) = 2 := by
  simpa [problem410PriestInput] using problem49PriestInput_sum_eq_two t

/-- The concrete IEEE-single instance in Higham Problem 4.10 uses `t = 24`. -/
theorem problem410PriestInput_t24_sum_eq_two :
    (∑ i : Fin 6, problem410PriestInput 24 i) = 2 := by
  simpa [problem410PriestInput] using problem49PriestInput_t24_sum_eq_two

/-- Concrete decimal values of the `t = 24` Problem 4.10 instance. -/
theorem problem410PriestInput_t24_values :
    problem410PriestInput 24 0 = 33554432 ∧
    problem410PriestInput 24 1 = 33554430 ∧
    problem410PriestInput 24 2 = -16777215 ∧
    problem410PriestInput 24 3 = -16777215 ∧
    problem410PriestInput 24 4 = -16777215 ∧
    problem410PriestInput 24 5 = -16777215 := by
  simpa [problem410PriestInput] using problem49PriestInput_t24_values

/-- The first value in the concrete Problem 4.10 instance is finite in IEEE
single precision. -/
theorem problem410PriestInput_t24_x1_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem410PriestInput 24 0) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_x1_ieeeSingle_finiteSystem

/-- The second value in the concrete Problem 4.10 instance is finite in IEEE
single precision. -/
theorem problem410PriestInput_t24_x2_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem410PriestInput 24 1) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_x2_ieeeSingle_finiteSystem

/-- The repeated tail value in the concrete Problem 4.10 instance is finite in
IEEE single precision. -/
theorem problem410PriestInput_t24_tail_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem410PriestInput 24 2) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_tail_ieeeSingle_finiteSystem

/-- Every displayed input in the concrete Problem 4.10 instance is finite in
IEEE single precision. -/
theorem problem410PriestInput_t24_ieeeSingle_finiteSystem
    (i : Fin 6) :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem410PriestInput 24 i) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_ieeeSingle_finiteSystem i

/-- First nontrivial rounding fact in the local IEEE-single finite
round-to-even trace for Problem 4.10. -/
theorem problem410PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864 :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
      (problem410PriestInput 24 0) (problem410PriestInput 24 1) =
        (67108864 : ℝ) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864

end NumStability
