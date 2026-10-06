-- NumStability/Source/Higham/Chapter03/Problem11/KahanAbsoluteValue/IeeeDoubleTrace/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.KahanAbsolute`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Tactic
import NumStability.Source.Higham.Chapter01.Section12.InstabilityWithoutCancellation.PivotingExample
import NumStability.Source.Higham.Chapter02.Problem20.SquareRootIdentities.Basic
import NumStability.Source.Higham.Chapter03.Problem11.KahanAbsoluteValue.Basic

/-!
# Results

Relocated from `NumStability.Algorithms.KahanAbsolute` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# KahanAbsolute (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.KahanAbsolute`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

private theorem kahanAbsoluteIeeeDouble_finiteSystem_one_sixteenth :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (1 / 16 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (-3 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem kahanAbsoluteIeeeDouble_finiteSystem_one :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (1 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
    rfl

private theorem kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half :
    FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤ (1 / 2 : ℝ) := by
  norm_num [FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR, zpow_neg]
  have hden : (2 : ℝ) ≤ (2 : ℝ) ^ (1022 : ℕ) := by
    exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1022 : ℕ) ≠ 0)
  simpa [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden

private theorem kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude :
    (1 : ℝ) ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude := by
  rw [FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.betaR]
  change (1 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℤ) *
    (1 - (2 : ℝ) ^ (-53 : ℤ))
  have hfactor : (1 / 2 : ℝ) ≤ 1 - (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [zpow_neg]
  have hpow_nat : (2 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℕ) := by
    exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1024 : ℕ) ≠ 0)
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℤ) := by
    simpa [zpow_natCast] using hpow_nat
  have hmul := mul_le_mul hpow hfactor
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℤ))
  simpa using hmul

private theorem kahanAbsoluteIeeeDouble_finiteSystem_one_fourth :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (1 / 4 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (-1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem kahanAbsoluteIeeeDouble_finiteSystem_one_half :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (1 / 2 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (0 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem kahanAbsoluteIeeeDouble_finiteSystem_three_fourths :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (3 / 4 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 6755399441055744, (0 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem kahanAbsoluteIeeeDouble_finiteSystem_five_fourths :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (5 / 4 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 5629499534213120, (1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem kahanAbsoluteIeeeDouble_finiteSystem_three_halves :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (3 / 2 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 6755399441055744, (1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem kahanAbsoluteIeeeDouble_finiteSystem_two :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (2 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (2 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
    rfl

private theorem kahanAbsoluteIeeeDouble_finiteSystem_nine_sixteenths :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (9 / 16 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 5066549580791808, (0 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem kahanAbsoluteIeeeDouble_finiteSystem_twentyfive_sixteenths :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (25 / 16 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 7036874417766400, (1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem kahanAbsoluteIeeeDouble_finiteSystem_nine_fourths :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (9 / 4 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 5066549580791808, (2 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem kahanAbsoluteIeeeDouble_finiteSystem_four :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (4 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (3 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
    rfl

/-- The initial MATLAB line `y = x.^2` is exact in IEEE double for all six
Problem 3.11 inputs.  The remaining open work is the long rounded square-root
and squaring phase, not the first squaring operation. -/
theorem kahanAbsoluteProblem311IeeeDouble_initialSquare_exact :
    ∀ i : Fin 6,
      FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul
          (kahanAbsoluteProblem311Inputs i)
          (kahanAbsoluteProblem311Inputs i) =
        (kahanAbsoluteProblem311Inputs i) ^ 2 := by
  intro i
  fin_cases i <;> simp [kahanAbsoluteProblem311Inputs]
  · have hfin :
        FloatingPointFormat.ieeeDoubleFormat.finiteSystem
          (BasicOp.exact BasicOp.mul (1 / 4 : ℝ) (1 / 4)) := by
      norm_num [BasicOp.exact]
      exact kahanAbsoluteIeeeDouble_finiteSystem_one_sixteenth
    have hround :=
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.mul) (x := (1 / 4 : ℝ)) (y := (1 / 4 : ℝ)) hfin)
    norm_num [BasicOp.exact, pow_two] at hround ⊢
    exact hround
  · have hfin :
        FloatingPointFormat.ieeeDoubleFormat.finiteSystem
          (BasicOp.exact BasicOp.mul (1 / 2 : ℝ) (1 / 2)) := by
      norm_num [BasicOp.exact]
      exact kahanAbsoluteIeeeDouble_finiteSystem_one_fourth
    have hround :=
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.mul) (x := (1 / 2 : ℝ)) (y := (1 / 2 : ℝ)) hfin)
    norm_num [BasicOp.exact, pow_two] at hround ⊢
    exact hround
  · have hfin :
        FloatingPointFormat.ieeeDoubleFormat.finiteSystem
          (BasicOp.exact BasicOp.mul (3 / 4 : ℝ) (3 / 4)) := by
      norm_num [BasicOp.exact]
      exact kahanAbsoluteIeeeDouble_finiteSystem_nine_sixteenths
    have hround :=
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.mul) (x := (3 / 4 : ℝ)) (y := (3 / 4 : ℝ)) hfin)
    norm_num [BasicOp.exact, pow_two] at hround ⊢
    exact hround
  · have hfin :
        FloatingPointFormat.ieeeDoubleFormat.finiteSystem
          (BasicOp.exact BasicOp.mul (5 / 4 : ℝ) (5 / 4)) := by
      norm_num [BasicOp.exact]
      exact kahanAbsoluteIeeeDouble_finiteSystem_twentyfive_sixteenths
    have hround :=
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.mul) (x := (5 / 4 : ℝ)) (y := (5 / 4 : ℝ)) hfin)
    norm_num [BasicOp.exact, pow_two] at hround ⊢
    exact hround
  · have hfin :
        FloatingPointFormat.ieeeDoubleFormat.finiteSystem
          (BasicOp.exact BasicOp.mul (3 / 2 : ℝ) (3 / 2)) := by
      norm_num [BasicOp.exact]
      exact kahanAbsoluteIeeeDouble_finiteSystem_nine_fourths
    have hround :=
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.mul) (x := (3 / 2 : ℝ)) (y := (3 / 2 : ℝ)) hfin)
    norm_num [BasicOp.exact, pow_two] at hround ⊢
    exact hround
  · have hfin :
        FloatingPointFormat.ieeeDoubleFormat.finiteSystem
          (BasicOp.exact BasicOp.mul (2 : ℝ) (2 : ℝ)) := by
      norm_num [BasicOp.exact]
      exact kahanAbsoluteIeeeDouble_finiteSystem_four
    have hround :=
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.mul) (x := (2 : ℝ)) (y := (2 : ℝ)) hfin)
    norm_num [BasicOp.exact, pow_two] at hround ⊢
    exact hround

/-- The IEEE-double value `1` is a fixed point of the rounded square-root
wrapper. -/
theorem kahanAbsoluteIeeeDouble_sqrt_one :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenSqrt (1 : ℝ) = 1 := by
  have hsqrt :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem (Real.sqrt (1 : ℝ)) := by
    simpa using kahanAbsoluteIeeeDouble_finiteSystem_one
  have h :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenSqrt_eq_exact_of_finiteSystem
      (x := (1 : ℝ)) hsqrt
  simpa using h

/-- Once the IEEE-double root phase reaches `1`, every further rounded
square-root step stays at `1`. -/
theorem kahanAbsoluteFiniteSqrtSteps_ieeeDouble_one (k : ℕ) :
    kahanAbsoluteFiniteSqrtSteps FloatingPointFormat.ieeeDoubleFormat k
        (1 : ℝ) =
      1 := by
  induction k with
  | zero =>
      simp [kahanAbsoluteFiniteSqrtSteps]
  | succ k ih =>
      simp [kahanAbsoluteFiniteSqrtSteps, ih, kahanAbsoluteIeeeDouble_sqrt_one]

/-- Squaring `1` in the finite IEEE-double operation wrapper returns `1`. -/
theorem kahanAbsoluteIeeeDouble_square_one :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul (1 : ℝ) 1 =
      1 := by
  have hfin :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.mul (1 : ℝ) 1) := by
    norm_num [BasicOp.exact]
    exact kahanAbsoluteIeeeDouble_finiteSystem_one
  have h :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (1 : ℝ)) (y := (1 : ℝ)) hfin
  simpa [BasicOp.exact] using h

/-- Once the IEEE-double square phase reaches `1`, every further rounded square
step stays at `1`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_one (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat k
        (1 : ℝ) =
      1 := by
  induction k with
  | zero =>
      simp [kahanAbsoluteFiniteSquareSteps]
  | succ k ih =>
      simp [kahanAbsoluteFiniteSquareSteps, kahanAbsoluteIeeeDouble_square_one, ih]

/-- The first rounded IEEE-double square after the below-one root phase reaches
the predecessor of `1` is the next lower representable value.  This closes the
first concrete step of the remaining predecessor-square cascade. -/
theorem kahanAbsoluteIeeeDouble_square_predOne_eq_twoUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoublePredOne kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteIeeeDoubleTwoUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 1) 0
  let b : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoublePredOne kahanAbsoluteIeeeDoublePredOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 1) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 1, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-52 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoublePredOne, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleTwoUlpsBelowOne, ha_value] using hround

/-- Peeling the first rounded square step from the predecessor of `1` rewrites
the remaining IEEE-double square cascade to the cascade from
`1 - 2^-52`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_predOne_eq_twoUlpsBelowOne]

/-- The second rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-52)^2)` to the fourth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_twoUlpsBelowOne_eq_fourUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleTwoUlpsBelowOne
          kahanAbsoluteIeeeDoubleTwoUlpsBelowOne =
      kahanAbsoluteIeeeDoubleFourUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 3) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 2) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleTwoUlpsBelowOne kahanAbsoluteIeeeDoubleTwoUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 3) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 3) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 3, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-51 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 3 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-52 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleTwoUlpsBelowOne, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-52 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-52 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleFourUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-52` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-51`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoUlpsBelowOne_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleTwoUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFourUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_twoUlpsBelowOne_eq_fourUlpsBelowOne]

/-- Peeling the first two rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-51`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_two_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 2) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFourUlpsBelowOne := by
  rw [show k + 2 = (k + 1) + 1 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoUlpsBelowOne_succ k]

/-- The third rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-51)^2)` to the eighth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_fourUlpsBelowOne_eq_eightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleFourUlpsBelowOne
          kahanAbsoluteIeeeDoubleFourUlpsBelowOne =
      kahanAbsoluteIeeeDoubleEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 7) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 6) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleFourUlpsBelowOne kahanAbsoluteIeeeDoubleFourUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 7) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 7) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 7, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-50 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 7 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-51 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleFourUlpsBelowOne, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-51 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-51 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleEightUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-51` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-50`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourUlpsBelowOne_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleFourUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_fourUlpsBelowOne_eq_eightUlpsBelowOne]

/-- Peeling the first three rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-50`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_three_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 3) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleEightUlpsBelowOne := by
  rw [show k + 3 = (k + 1) + 2 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_two_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourUlpsBelowOne_succ k]

/-- The fourth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-50)^2)` to the sixteenth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_eightUlpsBelowOne_eq_sixteenUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleEightUlpsBelowOne
          kahanAbsoluteIeeeDoubleEightUlpsBelowOne =
      kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 15) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 14) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleEightUlpsBelowOne kahanAbsoluteIeeeDoubleEightUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 15) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 15) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 15, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-49 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 15 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-50 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleEightUlpsBelowOne, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-50 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-50 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-50` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-49`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightUlpsBelowOne_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleEightUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_eightUlpsBelowOne_eq_sixteenUlpsBelowOne]

/-- Peeling the first four rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-49`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_four_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 4) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne := by
  rw [show k + 4 = (k + 1) + 3 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_three_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightUlpsBelowOne_succ k]

/-- The fifth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-49)^2)` to the thirty-second ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_sixteenUlpsBelowOne_eq_thirtyTwoUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne
          kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne =
      kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 31) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 30) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 31) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 31) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 31, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-48 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 31 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-49 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-49 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-49 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-49` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-48`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixteenUlpsBelowOne_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_sixteenUlpsBelowOne_eq_thirtyTwoUlpsBelowOne]

/-- Peeling the first five rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-48`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_five_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 5) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne := by
  rw [show k + 5 = (k + 1) + 4 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_four_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixteenUlpsBelowOne_succ k]

/-- The sixth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-48)^2)` to the sixty-fourth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_thirtyTwoUlpsBelowOne_eq_sixtyFourUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne
          kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne =
      kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 63) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 62) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 63) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 63) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 63, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-47 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 63 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-48 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-48 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-48 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-48` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-47`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_thirtyTwoUlpsBelowOne_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_thirtyTwoUlpsBelowOne_eq_sixtyFourUlpsBelowOne]

/-- Peeling the first six rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-47`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_six_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 6) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne := by
  rw [show k + 6 = (k + 1) + 5 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_five_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_thirtyTwoUlpsBelowOne_succ k]

/-- The seventh rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-47)^2)` to the one-hundred-twenty-eighth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_sixtyFourUlpsBelowOne_eq_oneHundredTwentyEightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne
          kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne =
      kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 127) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 126) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne
      kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 127) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 127) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 127, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-46 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 127 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-47 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-47 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-47 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-47` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-46`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixtyFourUlpsBelowOne_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_sixtyFourUlpsBelowOne_eq_oneHundredTwentyEightUlpsBelowOne]

/-- Peeling the first seven rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-46`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_seven_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 7) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne := by
  rw [show k + 7 = (k + 1) + 6 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_six_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixtyFourUlpsBelowOne_succ k]

/-- The eighth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-46)^2)` to the two-hundred-fifty-sixth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_oneHundredTwentyEightUlpsBelowOne_eq_twoHundredFiftySixUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne
          kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne =
      kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 255) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 254) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne
      kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 255) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 255) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 255, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-45 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 255 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-46 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-46 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-46 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-46` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-45`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredTwentyEightUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_oneHundredTwentyEightUlpsBelowOne_eq_twoHundredFiftySixUlpsBelowOne]

/-- Peeling the first eight rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-45`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_eight_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 8) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne := by
  rw [show k + 8 = (k + 1) + 7 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_seven_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredTwentyEightUlpsBelowOne_succ k]

/-- The ninth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-45)^2)` to the five-hundred-twelfth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_twoHundredFiftySixUlpsBelowOne_eq_fiveHundredTwelveUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne
          kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne =
      kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 511) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 510) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne
      kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 511) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 511) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 511, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-44 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 511 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-45 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-45 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-45 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-45` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-44`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredFiftySixUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_twoHundredFiftySixUlpsBelowOne_eq_fiveHundredTwelveUlpsBelowOne]

/-- Peeling the first nine rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-44`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_nine_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 9) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne := by
  rw [show k + 9 = (k + 1) + 8 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_eight_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredFiftySixUlpsBelowOne_succ k]

/-- The tenth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-44)^2)` to the one-thousand-twenty-fourth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_fiveHundredTwelveUlpsBelowOne_eq_oneThousandTwentyFourUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne
          kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne =
      kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 1023) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 1022) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne
      kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 1023) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 1023) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 1023, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-43 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 1023 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-44 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-44 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-44 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-44` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-43`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredTwelveUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_fiveHundredTwelveUlpsBelowOne_eq_oneThousandTwentyFourUlpsBelowOne]

/-- Peeling the first ten rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-43`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_ten_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 10) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne := by
  rw [show k + 10 = (k + 1) + 9 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_nine_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredTwelveUlpsBelowOne_succ k]

/-- The eleventh rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-43)^2)` to the two-thousand-forty-eighth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_oneThousandTwentyFourUlpsBelowOne_eq_twoThousandFortyEightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne
          kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne =
      kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 2047) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 2046) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne
      kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 2047) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 2047) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 2047, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-42 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 2047 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-43 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-43 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-43 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-43` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-42`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneThousandTwentyFourUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_oneThousandTwentyFourUlpsBelowOne_eq_twoThousandFortyEightUlpsBelowOne]

/-- Peeling the first eleven rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-42`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_eleven_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 11) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne := by
  rw [show k + 11 = (k + 1) + 10 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_ten_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneThousandTwentyFourUlpsBelowOne_succ k]

/-- The twelfth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-42)^2)` to the four-thousand-ninety-sixth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_twoThousandFortyEightUlpsBelowOne_eq_fourThousandNinetySixUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne
          kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne =
      kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 4095) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 4094) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne
      kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 4095) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 4095) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 4095, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-41 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 4095 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-42 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact, kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-42 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-42 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-42` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-41`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoThousandFortyEightUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_twoThousandFortyEightUlpsBelowOne_eq_fourThousandNinetySixUlpsBelowOne]

/-- Peeling the first twelve rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-41`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twelve_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 12) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne := by
  rw [show k + 12 = (k + 1) + 11 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_eleven_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoThousandFortyEightUlpsBelowOne_succ k]

/-- The thirteenth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-41)^2)` to the eight-thousand-one-hundred-ninety-second ulp
below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_fourThousandNinetySixUlpsBelowOne_eq_eightThousandOneHundredNinetyTwoUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne
          kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne =
      kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 8191) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 8190) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne
      kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 8191) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 8191) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 8191, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-40 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 8191 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-41 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-41 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-41 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne, ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-41` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-40`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourThousandNinetySixUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_fourThousandNinetySixUlpsBelowOne_eq_eightThousandOneHundredNinetyTwoUlpsBelowOne]

/-- Peeling the first thirteen rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-40`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirteen_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 13) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne := by
  rw [show k + 13 = (k + 1) + 12 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twelve_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourThousandNinetySixUlpsBelowOne_succ k]

/-- The fourteenth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-40)^2)` to the
sixteen-thousand-three-hundred-eighty-fourth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_eightThousandOneHundredNinetyTwoUlpsBelowOne_eq_sixteenThousandThreeHundredEightyFourUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne
          kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne =
      kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 16383) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 16382) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne
      kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 16383) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 16383) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 16383, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-39 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 16383 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-40 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-40 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-40 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-40` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-39`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightThousandOneHundredNinetyTwoUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_eightThousandOneHundredNinetyTwoUlpsBelowOne_eq_sixteenThousandThreeHundredEightyFourUlpsBelowOne]

/-- Peeling the first fourteen rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-39`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_fourteen_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 14) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne := by
  rw [show k + 14 = (k + 1) + 13 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirteen_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightThousandOneHundredNinetyTwoUlpsBelowOne_succ k]

/-- The fifteenth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-39)^2)` to the
thirty-two-thousand-seven-hundred-sixty-eighth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_sixteenThousandThreeHundredEightyFourUlpsBelowOne_eq_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne
          kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne =
      kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 32767) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 32766) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne
      kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 32767) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 32767) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 32767, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-38 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 32767 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-39 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-39 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-39 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-39` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-38`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixteenThousandThreeHundredEightyFourUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_sixteenThousandThreeHundredEightyFourUlpsBelowOne_eq_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne]

/-- Peeling the first fifteen rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-38`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_fifteen_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 15) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne := by
  rw [show k + 15 = (k + 1) + 14 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_fourteen_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixteenThousandThreeHundredEightyFourUlpsBelowOne_succ k]

/-- The sixteenth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-38)^2)` to the
sixty-five-thousand-five-hundred-thirty-sixth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne_eq_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne
          kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne =
      kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 65535) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 65534) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne
      kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 65535) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 65535) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 65535, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-37 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 65535 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-38 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-38 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-38 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-38` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-37`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne_eq_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne]

/-- Peeling the first sixteen rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-37`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_sixteen_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 16) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne := by
  rw [show k + 16 = (k + 1) + 15 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_fifteen_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne_succ k]

/-- The seventeenth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-37)^2)` to the
one-hundred-thirty-one-thousand-seventy-second ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne_eq_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne
          kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne =
      kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 131071) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 131070) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne
      kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 131071) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 131071) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 131071, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-36 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 131071 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-37 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-37 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-37 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-37` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-36`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne_eq_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne]

/-- Peeling the first seventeen rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-36`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_seventeen_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 17) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne := by
  rw [show k + 17 = (k + 1) + 16 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_sixteen_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne_succ k]

/-- The eighteenth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-36)^2)` to the
two-hundred-sixty-two-thousand-one-hundred-forty-fourth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne_eq_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne
          kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne =
      kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 262143) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 262142) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne
      kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 262143) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 262143) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 262143, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-35 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 262143 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-36 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-36 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-36 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-36` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-35`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne_eq_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne]

/-- Peeling the first eighteen rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-35`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_eighteen_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 18) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne := by
  rw [show k + 18 = (k + 1) + 17 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_seventeen_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne_succ k]

/-- The nineteenth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-35)^2)` to the
five-hundred-twenty-four-thousand-two-hundred-eighty-eighth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne_eq_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne
          kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne =
      kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 524287) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 524286) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne
      kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 524287) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 524287) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 524287, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-34 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 524287 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-35 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-35 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-35 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-35` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-34`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne_eq_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne]

/-- Peeling the first nineteen rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-34`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_nineteen_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 19) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne := by
  rw [show k + 19 = (k + 1) + 18 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_eighteen_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne_succ k]

/-- The twentieth rounded IEEE-double square in the predecessor-square cascade
rounds `fl((1 - 2^-34)^2)` to the
one-million-forty-eight-thousand-five-hundred-seventy-sixth ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne_eq_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne
          kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne =
      kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 1048575) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 1048574) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne
      kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 1048575) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 1048575) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 1048575, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-33 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 1048575 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-34 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-34 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-34 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-34` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-33`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne_eq_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne]

/-- Peeling the first twenty rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-33`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twenty_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 20) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne := by
  rw [show k + 20 = (k + 1) + 19 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_nineteen_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne_succ k]

/-- The twenty-first rounded IEEE-double square in the predecessor-square
cascade rounds `fl((1 - 2^-33)^2)` to the
two-million-ninety-seven-thousand-one-hundred-fifty-second ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne_eq_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne
          kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne =
      kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 2097151) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 2097150) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne
      kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 2097151) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 2097151) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 2097151, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-32 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 2097151 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-33 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-33 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-33 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-33` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-32`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne_eq_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne]

/-- Peeling the first twenty-one rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-32`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyOne_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 21) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne := by
  rw [show k + 21 = (k + 1) + 20 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twenty_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne_succ k]

/-- The twenty-second rounded IEEE-double square in the predecessor-square
cascade rounds `fl((1 - 2^-32)^2)` to the
four-million-one-hundred-ninety-four-thousand-three-hundred-fourth ulp below
`1`. -/
theorem kahanAbsoluteIeeeDouble_square_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne_eq_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne
          kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne =
      kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 4194303) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 4194302) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne
      kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 4194303) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 4194303) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 4194303, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-31 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 4194303 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-32 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-32 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-32 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-32` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-31`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne_eq_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne]

/-- Peeling the first twenty-two rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-31`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyTwo_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 22) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne := by
  rw [show k + 22 = (k + 1) + 21 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyOne_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne_succ k]

/-- The twenty-third rounded IEEE-double square in the predecessor-square
cascade rounds `fl((1 - 2^-31)^2)` to the
eight-million-three-hundred-eighty-eight-thousand-six-hundred-eighth ulp below
`1`. -/
theorem kahanAbsoluteIeeeDouble_square_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne_eq_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne
          kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne =
      kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 8388607) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 8388606) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne
      kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 8388607) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 8388607) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 8388607, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-30 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 8388607 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-31 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-31 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-31 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-31` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-30`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne_eq_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne]

/-- Peeling the first twenty-three rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-30`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyThree_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 23) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne := by
  rw [show k + 23 = (k + 1) + 22 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyTwo_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne_succ k]

/-- The twenty-fourth rounded IEEE-double square in the predecessor-square
cascade rounds `fl((1 - 2^-30)^2)` to the
sixteen-million-seven-hundred-seventy-seven-thousand-two-hundred-sixteenth ulp
below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne_eq_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne
          kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne =
      kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 16777215) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 16777214) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne
      kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 16777215) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 16777215) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 16777215, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-29 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 16777215 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-30 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-30 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-30 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-30` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-29`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne_eq_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne]

/-- Peeling the first twenty-four rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-29`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyFour_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 24) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne := by
  rw [show k + 24 = (k + 1) + 23 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyThree_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne_succ k]

/-- The twenty-fifth rounded IEEE-double square in the predecessor-square
cascade rounds `fl((1 - 2^-29)^2)` to the
thirty-three-million-five-hundred-fifty-four-thousand-four-hundred-thirty-second
ulp below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne_eq_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne
          kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne =
      kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 33554431) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 33554430) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne
      kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 33554431) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 33554431) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 33554431, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-28 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 33554431 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-29 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-29 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-29 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-29` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-28`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne_eq_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne]

/-- Peeling the first twenty-five rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-28`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyFive_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 25) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne := by
  rw [show k + 25 = (k + 1) + 24 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyFour_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne_succ k]

/-- The twenty-sixth rounded IEEE-double square in the predecessor-square
cascade rounds `fl((1 - 2^-28)^2)` to the
sixty-seven-million-one-hundred-eight-thousand-eight-hundred-sixty-fourth ulp
below `1`. -/
theorem kahanAbsoluteIeeeDouble_square_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne_eq_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne
          kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne =
      kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 67108863) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 67108862) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne
      kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 67108863) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 67108863) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 67108863, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-27 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 67108863 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-28 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-28 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-28 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-28` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-27`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne_eq_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne]

/-- Peeling the first twenty-six rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-27`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentySix_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 26) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne := by
  rw [show k + 26 = (k + 1) + 25 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyFive_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne_succ k]

/-- The twenty-seventh rounded IEEE-double square in the predecessor-square
cascade rounds the exact midpoint `fl((1 - 2^-27)^2)` to the even endpoint
`1 - 2^-26`. -/
theorem kahanAbsoluteIeeeDouble_square_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne_eq_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne
          kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne =
      kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 134217727) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 134217726) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne
      kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 134217727) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 134217727) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 134217727, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-26 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) - 134217727 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hx_value :
      x = ((1 : ℝ) - (2 : ℝ) ^ (-27 : ℤ)) ^ 2 := by
    simp [x, BasicOp.exact,
      kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne,
      pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤ ((1 : ℝ) - (2 : ℝ) ^ (-27 : ℤ)) ^ 2 := by
        norm_num [zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          ((1 : ℝ) - (2 : ℝ) ^ (-27 : ℤ)) ^ 2 ≤ 1 := by
        norm_num [zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft :
      a = fmt.normalizedValue false (fmt.maxNormalMantissa - 134217727) (0 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [zpow_neg]
  have heven :
      FloatingPointFormat.evenMantissa (fmt.maxNormalMantissa - 134217727) := by
    norm_num [FloatingPointFormat.evenMantissa, fmt,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.maxNormalMantissa]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt,
    kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne,
    ha_value] using hround

/-- Peeling one rounded square step from `1 - 2^-27` rewrites the remaining
IEEE-double square cascade to the cascade from `1 - 2^-26`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne_eq_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne]

/-- Peeling the first twenty-seven rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2^-26`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentySeven_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 27) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne := by
  rw [show k + 27 = (k + 1) + 26 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentySix_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne_succ k]

/-- Peeling the first twenty-eight rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from the
exact state `1 - 134217727 * 2^-52`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyEight_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 28) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne := by
  rw [show k + 28 = (k + 1) + 27 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentySeven_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne_succ k]

/-- The twenty-ninth rounded IEEE-double square in the predecessor-square
cascade rounds the exact square of `1 - 134217727 * 2^-52` to
`1 - 536870900 * 2^-53`. -/
theorem kahanAbsoluteIeeeDouble_square_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne_eq_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne
          kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne =
      kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 536870900) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 536870899) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne
      kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 536870900) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 536870900) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 536870900, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - 536870901 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b =
      kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne,
      zpow_neg]
  have hx_value :
      x = kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne ^ 2 := by
    simp [x, BasicOp.exact, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne,
      kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤
            kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne ^ 2 := by
        norm_num [kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne,
          zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne ^ 2 ≤
            1 := by
        norm_num [kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne,
          zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne,
      kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne,
      zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt, hb_value] using hround

/-- Peeling one rounded square step from `1 - 134217727 * 2^-52` rewrites the
remaining IEEE-double square cascade to the cascade from
`1 - 536870900 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne_eq_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne]

/-- Peeling the first twenty-nine rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 536870900 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyNine_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 29) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne := by
  rw [show k + 29 = (k + 1) + 28 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyEight_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne_succ k]

/-- The thirtieth rounded IEEE-double square in the predecessor-square cascade
rounds the exact square of `1 - 536870900 * 2^-53` to
`1 - 1073741768 * 2^-53`. -/
theorem kahanAbsoluteIeeeDouble_square_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_eq_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne
          kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne =
      kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 1073741768) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 1073741767) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne
      kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 1073741768) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 1073741768) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 1073741768, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - 1073741769 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b =
      kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne,
      zpow_neg]
  have hx_value :
      x = kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne ^ 2 := by
    simp [x, BasicOp.exact, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne,
      kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤
            kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne ^ 2 := by
        norm_num [kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne,
          zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne ^ 2 ≤
            1 := by
        norm_num [kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne,
          zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne,
      kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne,
      zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt, hb_value] using hround

/-- Peeling one rounded square step from `1 - 536870900 * 2^-53` rewrites the
remaining IEEE-double square cascade to the cascade from
`1 - 1073741768 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_eq_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne]

/-- Peeling the first thirty rounded square steps from the predecessor of `1`
rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 1073741768 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirty_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 30) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne := by
  rw [show k + 30 = (k + 1) + 29 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyNine_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_succ k]

/-- The thirty-first rounded IEEE-double square in the predecessor-square cascade
rounds the exact square of `1 - 1073741768 * 2^-53` to
`1 - 2147483408 * 2^-53`. -/
theorem kahanAbsoluteIeeeDouble_square_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne_eq_twoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne
          kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne =
      kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 2147483408) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 2147483407) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne
      kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 2147483408) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 2147483408) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 2147483408, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - 2147483409 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b =
      kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne,
      zpow_neg]
  have hx_value :
      x = kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne ^ 2 := by
    simp [x, BasicOp.exact, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne,
      kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤
            kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne ^ 2 := by
        norm_num [kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne,
          zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne ^ 2 ≤
            1 := by
        norm_num [kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne,
          zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne,
      kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne,
      zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt, hb_value] using hround

/-- Peeling one rounded square step from `1 - 1073741768 * 2^-53` rewrites the
remaining IEEE-double square cascade to the cascade from
`1 - 2147483408 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne_eq_twoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne]

/-- Peeling the first thirty-one rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 2147483408 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyOne_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 31) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne := by
  rw [show k + 31 = (k + 1) + 30 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirty_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne_succ k]

/-- The thirty-second rounded IEEE-double square in the predecessor-square
cascade rounds the exact square of `1 - 2147483408 * 2^-53` to
`1 - 4294966304 * 2^-53`. -/
theorem kahanAbsoluteIeeeDouble_square_twoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne_eq_fourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne
          kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne =
      kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 4294966304) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 4294966303) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne
      kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 4294966304) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 4294966304) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 4294966304, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - 4294966305 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b =
      kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne,
      zpow_neg]
  have hx_value :
      x = kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne ^ 2 := by
    simp [x, BasicOp.exact, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne,
      kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤
            kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne ^ 2 := by
        norm_num [kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne,
          zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne ^ 2 ≤
            1 := by
        norm_num [kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne,
          zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne,
      kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne,
      zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt, hb_value] using hround

/-- Peeling one rounded square step from `1 - 2147483408 * 2^-53` rewrites the
remaining IEEE-double square cascade to the cascade from
`1 - 4294966304 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_twoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne_eq_fourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne]

/-- Peeling the first thirty-two rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 4294966304 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyTwo_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 32) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne := by
  rw [show k + 32 = (k + 1) + 31 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyOne_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne_succ k]

/-- The thirty-third rounded IEEE-double square in the predecessor-square
cascade rounds the exact square of `1 - 4294966304 * 2^-53` to
`1 - 8589930560 * 2^-53`. -/
theorem kahanAbsoluteIeeeDouble_square_fourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne_eq_eightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne
          kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne =
      kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 8589930560) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 8589930559) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne
      kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 8589930560) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 8589930560) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 8589930560, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - 8589930561 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b =
      kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne,
      zpow_neg]
  have hx_value :
      x = kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne ^ 2 := by
    simp [x, BasicOp.exact, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne,
      kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤
            kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne ^ 2 := by
        norm_num [kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne,
          zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne ^ 2 ≤
            1 := by
        norm_num [kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne,
          zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne,
      kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne,
      zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt, hb_value] using hround

/-- Peeling one rounded square step from `1 - 4294966304 * 2^-53` rewrites the
remaining IEEE-double square cascade to the cascade from
`1 - 8589930560 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_fourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne_eq_eightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne]

/-- Peeling the first thirty-three rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 8589930560 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyThree_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 33) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne := by
  rw [show k + 33 = (k + 1) + 32 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyTwo_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne_succ k]

/-- The thirty-fourth rounded IEEE-double square in the predecessor-square
cascade rounds the exact square of `1 - 8589930560 * 2^-53` to
`1 - 17179852928 * 2^-53`. -/
theorem kahanAbsoluteIeeeDouble_square_eightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne_eq_seventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp
        BasicOp.mul kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne
          kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne =
      kahanAbsoluteIeeeDoubleSeventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 17179852928) 0
  let b : ℝ := fmt.normalizedValue false (fmt.maxNormalMantissa - 17179852927) 0
  let x : ℝ := BasicOp.exact BasicOp.mul
    kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne
      kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne
  have hm : fmt.normalizedMantissa (fmt.maxNormalMantissa - 17179852928) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hmnext : fmt.normalizedMantissa ((fmt.maxNormalMantissa - 17179852928) + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.maxNormalMantissa]
  have hsame : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, fmt.maxNormalMantissa - 17179852928, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.maxNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
  have ha_value : a = (1 : ℝ) - 17179852929 * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa, zpow_neg]
  have hb_value : b =
      kahanAbsoluteIeeeDoubleSeventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      kahanAbsoluteIeeeDoubleSeventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne,
      zpow_neg]
  have hx_value :
      x = kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne ^ 2 := by
    simp [x, BasicOp.exact, pow_two]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne,
      kahanAbsoluteIeeeDoubleSeventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      rw [hx_value]
      exact sq_nonneg _
    rw [abs_of_nonneg hxnonneg]
    constructor
    · rw [hx_value]
      have hhalf :
          (1 / 2 : ℝ) ≤
            kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne ^ 2 := by
        norm_num [kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne,
          zpow_neg]
      exact le_trans kahanAbsoluteIeeeDouble_minNormalMagnitude_le_half hhalf
    · rw [hx_value]
      have hle_one :
          kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne ^ 2 ≤
            1 := by
        norm_num [kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne,
          zpow_neg]
      exact le_trans hle_one kahanAbsoluteIeeeDouble_one_le_maxFiniteMagnitude
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num [kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne,
      kahanAbsoluteIeeeDoubleSeventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne,
      zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [FloatingPointFormat.finiteRoundToEvenOp, x, fmt, hb_value] using hround

/-- Peeling one rounded square step from `1 - 8589930560 * 2^-53` rewrites the
remaining IEEE-double square cascade to the cascade from
`1 - 17179852928 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne_succ
    (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 1) kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSeventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne := by
  simp [kahanAbsoluteFiniteSquareSteps,
    kahanAbsoluteIeeeDouble_square_eightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne_eq_seventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne]

/-- Peeling the first thirty-four rounded square steps from the predecessor of
`1` rewrites the remaining IEEE-double square cascade to the cascade from
`1 - 17179852928 * 2^-53`. -/
theorem kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyFour_succ (k : ℕ) :
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        (k + 34) kahanAbsoluteIeeeDoublePredOne =
      kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat
        k kahanAbsoluteIeeeDoubleSeventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne := by
  rw [show k + 34 = (k + 1) + 33 by omega]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyThree_succ (k + 1)]
  rw [kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne_succ k]

/-- Every displayed Problem 3.11 source input is an IEEE-double finite value. -/
theorem kahanAbsoluteProblem311Inputs_ieeeDouble_finiteSystem :
    ∀ i : Fin 6,
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (kahanAbsoluteProblem311Inputs i) := by
  intro i
  fin_cases i <;> simp [kahanAbsoluteProblem311Inputs]
  · simpa using kahanAbsoluteIeeeDouble_finiteSystem_one_fourth
  · simpa using kahanAbsoluteIeeeDouble_finiteSystem_one_half
  · exact kahanAbsoluteIeeeDouble_finiteSystem_three_fourths
  · exact kahanAbsoluteIeeeDouble_finiteSystem_five_fourths
  · exact kahanAbsoluteIeeeDouble_finiteSystem_three_halves
  · exact kahanAbsoluteIeeeDouble_finiteSystem_two

/-- After the exact initial `x.^2` line, the first rounded IEEE-double
square-root step returns the original positive source input exactly. -/
theorem kahanAbsoluteProblem311IeeeDouble_initialSquare_firstSqrt_exact :
    ∀ i : Fin 6,
      FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenSqrt
          (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul
            (kahanAbsoluteProblem311Inputs i)
            (kahanAbsoluteProblem311Inputs i)) =
        kahanAbsoluteProblem311Inputs i := by
  intro i
  have hsquare := kahanAbsoluteProblem311IeeeDouble_initialSquare_exact i
  have hsqrt :=
    FloatingPointFormat.problem2_19_sqrt_square_eq_abs_of_finiteSystem
      (fmt := FloatingPointFormat.ieeeDoubleFormat)
      (x := kahanAbsoluteProblem311Inputs i)
      (kahanAbsoluteProblem311Inputs_ieeeDouble_finiteSystem i)
  have hnonneg : 0 ≤ kahanAbsoluteProblem311Inputs i := by
    fin_cases i <;> norm_num [kahanAbsoluteProblem311Inputs]
  rw [hsquare]
  simpa [abs_of_nonneg hnonneg] using hsqrt

/-- The original concrete IEEE-double `m = 75` trace equals the reduced trace
that starts from the six source inputs and performs only the remaining
seventy-four square roots and seventy-four squares. -/
theorem kahanAbsoluteProblem311FiniteTraceVector_ieeeDouble_m75_eq_reduced :
    kahanAbsoluteProblem311FiniteTraceVector
      FloatingPointFormat.ieeeDoubleFormat 75 =
        kahanAbsoluteProblem311IeeeDoubleReducedM75TraceVector := by
  funext i
  change
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat 74
      (kahanAbsoluteFiniteSqrtSteps FloatingPointFormat.ieeeDoubleFormat 75
        (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul
          (kahanAbsoluteProblem311Inputs i)
          (kahanAbsoluteProblem311Inputs i))) =
    kahanAbsoluteFiniteSquareSteps FloatingPointFormat.ieeeDoubleFormat 74
      (kahanAbsoluteFiniteSqrtSteps FloatingPointFormat.ieeeDoubleFormat 74
        (kahanAbsoluteProblem311Inputs i))
  rw [kahanAbsoluteFiniteSqrtSteps_succ_eq_steps_after_one
    (fmt := FloatingPointFormat.ieeeDoubleFormat) (k := 74)]
  rw [kahanAbsoluteProblem311IeeeDouble_initialSquare_firstSqrt_exact]

/-- The named Sun `m = 75` concrete IEEE-double target is equivalent to the
reduced target that starts after the exact initial square and first square
root. -/
theorem kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget_iff_reduced :
    kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget ↔
      kahanAbsoluteProblem311SunM75IeeeDoubleReducedTraceTarget := by
  unfold kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget
    kahanAbsoluteProblem311SunM75IeeeDoubleReducedTraceTarget
  rw [kahanAbsoluteProblem311FiniteTraceVector_ieeeDouble_m75_eq_reduced]

/-- The reduced Sun `m = 75` IEEE-double trace target also implies the
reported four-decimal display row for the original concrete trace. -/
theorem kahanAbsoluteProblem311_sunM75_display4_of_ieeeDouble_reduced_trace_target
    (htrace : kahanAbsoluteProblem311SunM75IeeeDoubleReducedTraceTarget) :
    vectorDecimal4DisplaysAs
      (kahanAbsoluteProblem311FiniteTraceVector
        FloatingPointFormat.ieeeDoubleFormat 75)
      kahanAbsoluteProblem311SunM75Outputs :=
  kahanAbsoluteProblem311_sunM75_display4_of_ieeeDouble_trace_target
    ((kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget_iff_reduced).2 htrace)

end NumStability
