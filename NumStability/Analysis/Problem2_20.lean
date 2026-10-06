-- Analysis/Problem2_20.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.20.

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Problem2_19
import NumStability.FloatingPoint.Model

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2, Problem 2.20

Problem 2.20 asks whether a rounded evaluation of
`x / sqrt(x^2 + y^2)` can exceed `1`, even though the exact nonnegative
ratio is bounded by `1` when `x` is one component of the Euclidean norm.

This file records both a source-shaped standard-model witness and a concrete
one-digit decimal finite round-to-even selector trace.  The remaining full IEEE
instruction semantics layer, including special values and flags, is separate
from these model-level and finite-selector theorems.
-/

/-- The exact real ratio underlying Problem 2.20. -/
def problem2_20_exactRatio (x y : ℝ) : ℝ :=
  x / Real.sqrt (x ^ 2 + y ^ 2)

/-- The exact real component ratio in Problem 2.20 has magnitude at most one.
The rounded counterexamples below are therefore genuinely rounding artifacts,
not failures of the underlying Euclidean inequality. -/
theorem problem2_20_exactRatio_abs_le_one (x y : ℝ) :
    |problem2_20_exactRatio x y| ≤ 1 := by
  let d : ℝ := Real.sqrt (x ^ 2 + y ^ 2)
  have hs_nonneg : 0 ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hd_nonneg : 0 ≤ d := by
    simp [d]
  have hx_abs_le_d : |x| ≤ d := by
    have hsq : |x| ^ 2 ≤ d ^ 2 := by
      have hd_sq : d ^ 2 = x ^ 2 + y ^ 2 := by
        simpa [d] using Real.sq_sqrt hs_nonneg
      rw [hd_sq]
      have hsqabs : |x| ^ 2 = x ^ 2 := by
        rw [sq_abs]
      rw [hsqabs]
      nlinarith [sq_nonneg y]
    have h := (sq_le_sq).mp hsq
    simpa [abs_of_nonneg hd_nonneg] using h
  by_cases hd_zero : d = 0
  · have hx_abs_zero : |x| = 0 :=
      le_antisymm (by simpa [hd_zero] using hx_abs_le_d) (abs_nonneg x)
    have hx : x = 0 := abs_eq_zero.mp hx_abs_zero
    simp [problem2_20_exactRatio, hx]
  · have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd_zero)
    have hdiv : |x| / d ≤ 1 := by
      rw [div_le_one hd_pos]
      exact hx_abs_le_d
    have habs_div : |x / d| = |x| / d := by
      rw [abs_div, abs_of_pos hd_pos]
    simpa [problem2_20_exactRatio, d, habs_div]

/-- One-sided source form of the exact Euclidean ratio bound. -/
theorem problem2_20_exactRatio_le_one (x y : ℝ) :
    problem2_20_exactRatio x y ≤ 1 :=
  (abs_le.mp (problem2_20_exactRatio_abs_le_one x y)).2

/-- The rounded operation sequence used by the naive computation of
`x / sqrt(x^2 + y^2)`. -/
def problem2_20_computedRatio (fp : FPModel) (x y : ℝ) : ℝ :=
  let xx := fp.fl_mul x x
  let yy := fp.fl_mul y y
  let s := fp.fl_add xx yy
  let r := fp.fl_sqrt s
  fp.fl_div x r

/-- The same naive operation sequence at the concrete finite round-to-even
selector layer. -/
def problem2_20_finiteComputedRatio
    (fmt : FloatingPointFormat) (x y : ℝ) : ℝ :=
  let xx := fmt.finiteRoundToEvenOp BasicOp.mul x x
  let yy := fmt.finiteRoundToEvenOp BasicOp.mul y y
  let s := fmt.finiteRoundToEvenOp BasicOp.add xx yy
  let r := fmt.finiteRoundToEvenSqrt s
  fmt.finiteRoundToEvenOp BasicOp.div x r

private def problem2_20_flMul (x y : ℝ) : ℝ :=
  by
    classical
    exact
      if x = (11 / 10 : ℝ) ∧ y = (11 / 10 : ℝ) then
        1
      else
        x * y

/-- A small abstract standard-model instance with `u = 1/5` that rounds
`(11/10)*(11/10)` downward to `1`. -/
private def problem2_20_fp : FPModel where
  u := (1 / 5 : ℝ)
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := problem2_20_flMul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := by
    intro x
    ring
  model_add := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_sub := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_mul := by
    intro x y
    by_cases h : x = (11 / 10 : ℝ) ∧ y = (11 / 10 : ℝ)
    · rcases h with ⟨rfl, rfl⟩
      refine ⟨-(21 / 121 : ℝ), by norm_num, ?_⟩
      simp [problem2_20_flMul]
      norm_num
    · refine ⟨0, by norm_num, ?_⟩
      simp [problem2_20_flMul, h]
  model_div := by
    intro x y _hy
    exact ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    exact ⟨0, by norm_num, by ring⟩

/-- For the witness inputs, the exact real ratio is exactly `1`. -/
theorem problem2_20_exact_witness_ratio_eq_one :
    problem2_20_exactRatio (11 / 10 : ℝ) 0 = 1 := by
  have hsqrt :
      Real.sqrt ((11 / 10 : ℝ) ^ 2 + 0 ^ 2) = 11 / 10 := by
    have h := Real.sqrt_sq_eq_abs (11 / 10 : ℝ)
    simpa [abs_of_nonneg (by norm_num : 0 ≤ (11 / 10 : ℝ))] using h
  rw [problem2_20_exactRatio, hsqrt]
  norm_num

/-- A concrete finite-selector witness input also has exact real ratio `1`. -/
theorem problem2_20_exact_three_halves_zero_ratio_eq_one :
    problem2_20_exactRatio (3 / 2 : ℝ) 0 = 1 := by
  have hsqrt :
      Real.sqrt ((3 / 2 : ℝ) ^ 2 + 0 ^ 2) = 3 / 2 := by
    have h := Real.sqrt_sq_eq_abs (3 / 2 : ℝ)
    simpa [abs_of_nonneg (by norm_num : 0 ≤ (3 / 2 : ℝ))] using h
  rw [problem2_20_exactRatio, hsqrt]
  norm_num

/-- The concrete one-digit finite-selector trace below is intentionally not a
finite-input trace: `3/2` lies between one-digit decimal values and rounds to
`2`, so it is not itself in that finite system. -/
theorem problem2_20_decimalOneDigitThreeExponent_three_halves_not_finiteSystem :
    ¬ FloatingPointFormat.decimalOneDigitThreeExponentFormat.finiteSystem
        (3 / 2 : ℝ) := by
  intro hfin
  have hfix :
      FloatingPointFormat.decimalOneDigitThreeExponentFormat.finiteRoundToEven
          (3 / 2 : ℝ) =
        (3 / 2 : ℝ) :=
    FloatingPointFormat.finiteRoundToEven_eq_self_of_finiteSystem
      (fmt := FloatingPointFormat.decimalOneDigitThreeExponentFormat) hfin
  have hround :
      FloatingPointFormat.decimalOneDigitThreeExponentFormat.finiteRoundToEven
          (3 / 2 : ℝ) = 2 := by
    have h :=
      FloatingPointFormat.decimalOneDigitThreeExponent_midpoint_one_two_rounds_to_two
    norm_num at h
    exact h
  rw [hround] at hfix
  norm_num at hfix

/-- In the witness model, the rounded naive path computes `11/10`, which is
strictly larger than `1`. -/
theorem problem2_20_computed_witness_ratio_gt_one :
    1 < problem2_20_computedRatio problem2_20_fp (11 / 10 : ℝ) 0 := by
  norm_num [problem2_20_computedRatio, problem2_20_fp, problem2_20_flMul]

/-- Higham Problem 2.20's phenomenon can occur in the standard model: the exact
ratio is `1`, while the rounded naive computation exceeds `1`. -/
theorem problem2_20_standard_model_counterexample :
    ∃ fp : FPModel, ∃ x y : ℝ,
      problem2_20_exactRatio x y = 1 ∧
        1 < problem2_20_computedRatio fp x y := by
  exact
    ⟨problem2_20_fp, (11 / 10 : ℝ), 0,
      problem2_20_exact_witness_ratio_eq_one,
      problem2_20_computed_witness_ratio_gt_one⟩

namespace FloatingPointFormat

/-- A two-digit decimal finite format used only to certify that the
standard-model Problem 2.20 witness uses floating-point input values. -/
def problem2_20_decimalTwoDigitThreeExponentFormat : FloatingPointFormat where
  beta := 10
  t := 2
  emin := 0
  emax := 2
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

/-- The standard-model Problem 2.20 witness input `11/10` is a finite value of
the local two-digit decimal format. -/
theorem problem2_20_decimalTwoDigitThreeExponentFormat_finiteSystem_eleven_tenths :
    problem2_20_decimalTwoDigitThreeExponentFormat.finiteSystem
      (11 / 10 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  have hrepr :
      problem2_20_decimalTwoDigitThreeExponentFormat.normalizedExponentRepresentation
        (11 / 10 : ℝ) 1 := by
    refine ⟨false, 11, ?_, ?_, ?_⟩
    · norm_num [problem2_20_decimalTwoDigitThreeExponentFormat,
        normalizedMantissa, mantissaInRange, minNormalMantissa]
    · norm_num [problem2_20_decimalTwoDigitThreeExponentFormat,
        exponentInRange]
    · norm_num [problem2_20_decimalTwoDigitThreeExponentFormat,
        normalizedValue, signValue, betaR]
  exact
    problem2_20_decimalTwoDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      hrepr

/-- The source no-underflow audit for the two squared inputs in the naive
Problem 2.20 computation.  This is intentionally only the square-stage
underflow condition, not a full hardware exception model for every operation. -/
def problem2_20_noSquareUnderflowInputs
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  ¬ fmt.finiteUnderflowRange (BasicOp.exact BasicOp.mul x x) ∧
    ¬ fmt.finiteUnderflowRange (BasicOp.exact BasicOp.mul y y)

/-- In the repository's range predicate, an exact zero square is always in the
finite-underflow range.  Thus any Problem 2.20 witness satisfying a
no-square-underflow side condition cannot use a zero component. -/
theorem problem2_20_zero_square_finiteUnderflowRange
    (fmt : FloatingPointFormat) :
    fmt.finiteUnderflowRange (BasicOp.exact BasicOp.mul (0 : ℝ) 0) := by
  rw [finiteUnderflowRange]
  simpa [BasicOp.exact] using fmt.minNormalMagnitude_pos

theorem problem2_20_first_square_underflows_of_x_eq_zero
    (fmt : FloatingPointFormat) {x : ℝ} (hx : x = 0) :
    fmt.finiteUnderflowRange (BasicOp.exact BasicOp.mul x x) := by
  subst hx
  simpa using fmt.problem2_20_zero_square_finiteUnderflowRange

theorem problem2_20_second_square_underflows_of_y_eq_zero
    (fmt : FloatingPointFormat) {y : ℝ} (hy : y = 0) :
    fmt.finiteUnderflowRange (BasicOp.exact BasicOp.mul y y) := by
  subst hy
  simpa using fmt.problem2_20_zero_square_finiteUnderflowRange

theorem problem2_20_components_ne_zero_of_no_square_underflow
    (fmt : FloatingPointFormat) {x y : ℝ}
    (hxx : ¬ fmt.finiteUnderflowRange (BasicOp.exact BasicOp.mul x x))
    (hyy : ¬ fmt.finiteUnderflowRange (BasicOp.exact BasicOp.mul y y)) :
    x ≠ 0 ∧ y ≠ 0 := by
  constructor
  · intro hx
    exact hxx (fmt.problem2_20_first_square_underflows_of_x_eq_zero hx)
  · intro hy
    exact hyy (fmt.problem2_20_second_square_underflows_of_y_eq_zero hy)

theorem problem2_20_components_ne_zero_of_noSquareUnderflowInputs
    (fmt : FloatingPointFormat) {x y : ℝ}
    (h : fmt.problem2_20_noSquareUnderflowInputs x y) :
    x ≠ 0 ∧ y ≠ 0 :=
  fmt.problem2_20_components_ne_zero_of_no_square_underflow h.1 h.2

/-- In the one-digit decimal format, `(3/2)*(3/2) = 9/4` rounds down to `2`. -/
theorem problem2_20_decimalOneDigitThreeExponent_mul_three_halves_rounds_to_two :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.mul (3 / 2 : ℝ) (3 / 2) = 2 := by
  let fmt := decimalOneDigitThreeExponentFormat
  let a : ℝ := fmt.normalizedValue false 2 1
  let b : ℝ := fmt.normalizedValue false 3 1
  let x : ℝ := (9 / 4 : ℝ)
  have hm : fmt.normalizedMantissa 2 := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (2 + 1) := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 2, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, fmt, decimalOneDigitThreeExponentFormat,
      normalizedValue, signValue, betaR]
  have hxrange : fmt.finiteNormalRange x := by
    rw [finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, decimalOneDigitThreeExponentFormat,
        minNormalMagnitude, betaR]
    · have hmax : fmt.maxFiniteMagnitude = 90 := by
        norm_num [fmt, decimalOneDigitThreeExponentFormat,
          maxFiniteMagnitude, betaR]
        rfl
      simpa [x, hmax] using (by norm_num : (9 / 4 : ℝ) ≤ 90)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    norm_num [x, a, b, fmt, decimalOneDigitThreeExponentFormat,
      normalizedValue, signValue, betaR]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  have htarget :
      fmt.finiteRoundToEven ((3 / 2 : ℝ) * (3 / 2)) = a := by
    have hxmul : ((3 / 2 : ℝ) * (3 / 2)) = x := by norm_num [x]
    rw [hxmul]
    exact hround
  have ha : a = (2 : ℝ) := by
    norm_num [a, fmt, decimalOneDigitThreeExponentFormat, normalizedValue,
      signValue, betaR]
  simpa [finiteRoundToEvenOp, BasicOp.exact, ha] using htarget

/-- The zero square in the Problem 2.20 finite trace is exact. -/
theorem problem2_20_decimalOneDigitThreeExponent_zero_square_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.mul (0 : ℝ) 0 = 0 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.mul (0 : ℝ) 0) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat.finiteSystem_zero
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (0 : ℝ)) (y := (0 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.mul (0 : ℝ) 0 = (0 : ℝ) * 0 at hround
  norm_num at hround
  exact hround

/-- Adding the rounded zero square to the rounded first square is exact. -/
theorem problem2_20_decimalOneDigitThreeExponent_add_two_zero_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.add (2 : ℝ) 0 = 2 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.add (2 : ℝ) 0) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_two
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := (2 : ℝ)) (y := (0 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.add (2 : ℝ) 0 = (2 : ℝ) + 0 at hround
  norm_num at hround
  exact hround

/-- The final division `(3/2)/1` is a midpoint tie and rounds to `2`. -/
theorem problem2_20_decimalOneDigitThreeExponent_div_three_halves_one_rounds_to_two :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.div (3 / 2 : ℝ) 1 = 2 := by
  change decimalOneDigitThreeExponentFormat.finiteRoundToEven
      ((3 / 2 : ℝ) / 1) = 2
  have harg : ((3 / 2 : ℝ) / 1) = (((1 : ℝ) + 2) / 2) := by
    norm_num
  rw [harg]
  exact decimalOneDigitThreeExponent_midpoint_one_two_rounds_to_two

/-- Range audit for the concrete one-digit Problem 2.20 selector trace.  The
nonzero exact intermediates used by the trace are finite-normal, but the exact
zero square is in the finite underflow range of this source predicate. -/
theorem problem2_20_decimalOneDigitThreeExponent_exact_trace_range_audit :
    decimalOneDigitThreeExponentFormat.finiteNormalRange
        (BasicOp.exact BasicOp.mul (3 / 2 : ℝ) (3 / 2)) ∧
      decimalOneDigitThreeExponentFormat.finiteUnderflowRange
        (BasicOp.exact BasicOp.mul (0 : ℝ) 0) ∧
      decimalOneDigitThreeExponentFormat.finiteNormalRange
        (BasicOp.exact BasicOp.add (2 : ℝ) 0) ∧
      decimalOneDigitThreeExponentFormat.finiteNormalRange (Real.sqrt (2 : ℝ)) ∧
      decimalOneDigitThreeExponentFormat.finiteNormalRange
        (BasicOp.exact BasicOp.div (3 / 2 : ℝ) 1) := by
  let fmt := decimalOneDigitThreeExponentFormat
  have hmul :
      fmt.finiteNormalRange
        (BasicOp.exact BasicOp.mul (3 / 2 : ℝ) (3 / 2)) := by
    rw [finiteNormalRange]
    constructor
    · norm_num [BasicOp.exact, fmt, decimalOneDigitThreeExponentFormat,
        minNormalMagnitude, betaR]
    · have hmax : fmt.maxFiniteMagnitude = (90 : ℝ) := by
        norm_num [fmt, decimalOneDigitThreeExponentFormat,
          maxFiniteMagnitude, betaR]
        rfl
      rw [hmax]
      norm_num [BasicOp.exact]
  have hzero :
      fmt.finiteUnderflowRange (BasicOp.exact BasicOp.mul (0 : ℝ) 0) := by
    rw [finiteUnderflowRange]
    norm_num [BasicOp.exact, fmt, decimalOneDigitThreeExponentFormat,
      minNormalMagnitude, betaR]
  have hadd :
      fmt.finiteNormalRange (BasicOp.exact BasicOp.add (2 : ℝ) 0) := by
    rw [finiteNormalRange]
    constructor
    · norm_num [BasicOp.exact, fmt, decimalOneDigitThreeExponentFormat,
        minNormalMagnitude, betaR]
    · have hmax : fmt.maxFiniteMagnitude = (90 : ℝ) := by
        norm_num [fmt, decimalOneDigitThreeExponentFormat,
          maxFiniteMagnitude, betaR]
        rfl
      rw [hmax]
      norm_num [BasicOp.exact]
  have hsqrt : fmt.finiteNormalRange (Real.sqrt (2 : ℝ)) := by
    rw [finiteNormalRange]
    rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
    constructor
    · have hroot_gt_one : (1 : ℝ) < Real.sqrt 2 := by
        exact Real.lt_sqrt_of_sq_lt (by norm_num : (1 : ℝ) ^ 2 < 2)
      have hmin : fmt.minNormalMagnitude = (1 / 10 : ℝ) := by
        norm_num [fmt, decimalOneDigitThreeExponentFormat,
          minNormalMagnitude, betaR]
      rw [hmin]
      linarith
    · have hroot_lt_two : Real.sqrt (2 : ℝ) < 2 := by
        rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 2)
          (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have hmax : fmt.maxFiniteMagnitude = (90 : ℝ) := by
        norm_num [fmt, decimalOneDigitThreeExponentFormat,
          maxFiniteMagnitude, betaR]
        rfl
      rw [hmax]
      linarith
  have hdiv :
      fmt.finiteNormalRange (BasicOp.exact BasicOp.div (3 / 2 : ℝ) 1) := by
    rw [finiteNormalRange]
    constructor
    · norm_num [BasicOp.exact, fmt, decimalOneDigitThreeExponentFormat,
        minNormalMagnitude, betaR]
    · have hmax : fmt.maxFiniteMagnitude = (90 : ℝ) := by
        norm_num [fmt, decimalOneDigitThreeExponentFormat,
          maxFiniteMagnitude, betaR]
        rfl
      rw [hmax]
      norm_num [BasicOp.exact]
  exact ⟨hmul, hzero, hadd, hsqrt, hdiv⟩

/-- A concrete finite round-to-even trace of the naive Problem 2.20 path:
the exact ratio for `(3/2,0)` is `1`, but the rounded operation sequence
returns `2`. -/
theorem problem2_20_decimalOneDigitThreeExponent_computed_ratio_eq_two :
    problem2_20_finiteComputedRatio decimalOneDigitThreeExponentFormat
        (3 / 2 : ℝ) 0 = 2 := by
  simp [problem2_20_finiteComputedRatio,
    problem2_20_decimalOneDigitThreeExponent_mul_three_halves_rounds_to_two,
    problem2_20_decimalOneDigitThreeExponent_zero_square_exact,
    problem2_20_decimalOneDigitThreeExponent_add_two_zero_exact,
    problem2_19_decimalOneDigitThreeExponent_sqrt_two_rounds_to_one,
    problem2_20_decimalOneDigitThreeExponent_div_three_halves_one_rounds_to_two]

/-- The concrete finite round-to-even Problem 2.20 trace exceeds `1`. -/
theorem problem2_20_decimalOneDigitThreeExponent_computed_ratio_gt_one :
    1 <
      problem2_20_finiteComputedRatio decimalOneDigitThreeExponentFormat
        (3 / 2 : ℝ) 0 := by
  rw [problem2_20_decimalOneDigitThreeExponent_computed_ratio_eq_two]
  norm_num

/-- Higham Problem 2.20's phenomenon occurs for a concrete finite round-to-even
selector operation sequence, not only for an abstract standard-model witness. -/
theorem problem2_20_decimalOneDigitThreeExponent_finite_selector_counterexample :
    ∃ fmt : FloatingPointFormat, ∃ x y : ℝ,
      problem2_20_exactRatio x y = 1 ∧
        1 < problem2_20_finiteComputedRatio fmt x y := by
  exact
    ⟨decimalOneDigitThreeExponentFormat, (3 / 2 : ℝ), 0,
      problem2_20_exact_three_halves_zero_ratio_eq_one,
      problem2_20_decimalOneDigitThreeExponent_computed_ratio_gt_one⟩

theorem problem2_20_decimalOneDigitThreeExponent_trace_not_noSquareUnderflowInputs :
    ¬ problem2_20_noSquareUnderflowInputs
      decimalOneDigitThreeExponentFormat (3 / 2 : ℝ) 0 := by
  intro h
  exact h.2
    (decimalOneDigitThreeExponentFormat.problem2_20_second_square_underflows_of_y_eq_zero
      rfl)

theorem problem2_20_decimalOneDigitThreeExponent_trace_exceeds_one_but_fails_source_audit :
    problem2_20_exactRatio (3 / 2 : ℝ) 0 = 1 ∧
      1 < problem2_20_finiteComputedRatio decimalOneDigitThreeExponentFormat
        (3 / 2 : ℝ) 0 ∧
      ¬ decimalOneDigitThreeExponentFormat.finiteSystem (3 / 2 : ℝ) ∧
      ¬ problem2_20_noSquareUnderflowInputs
        decimalOneDigitThreeExponentFormat (3 / 2 : ℝ) 0 := by
  exact ⟨problem2_20_exact_three_halves_zero_ratio_eq_one,
    problem2_20_decimalOneDigitThreeExponent_computed_ratio_gt_one,
    problem2_20_decimalOneDigitThreeExponent_three_halves_not_finiteSystem,
    problem2_20_decimalOneDigitThreeExponent_trace_not_noSquareUnderflowInputs⟩

end FloatingPointFormat

/-- The standard-model Problem 2.20 witness can be chosen with inputs that are
floating-point values of a concrete finite format.  The rounded operations are
still supplied by the abstract `FPModel`; a concrete finite-operation or IEEE
instruction trace with the source's no-overflow/no-underflow side condition
remains a separate target. -/
theorem problem2_20_standard_model_counterexample_with_decimal_finite_inputs :
    ∃ fmt : FloatingPointFormat, ∃ fp : FPModel, ∃ x y : ℝ,
      fmt.finiteSystem x ∧ fmt.finiteSystem y ∧
        problem2_20_exactRatio x y = 1 ∧
          1 < problem2_20_computedRatio fp x y := by
  refine
    ⟨FloatingPointFormat.problem2_20_decimalTwoDigitThreeExponentFormat,
      problem2_20_fp, (11 / 10 : ℝ), 0, ?_, ?_,
      problem2_20_exact_witness_ratio_eq_one,
      problem2_20_computed_witness_ratio_gt_one⟩
  · exact
      FloatingPointFormat.problem2_20_decimalTwoDigitThreeExponentFormat_finiteSystem_eleven_tenths
  · exact
      FloatingPointFormat.problem2_20_decimalTwoDigitThreeExponentFormat.finiteSystem_zero

end

end NumStability
