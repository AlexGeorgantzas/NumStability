import Mathlib.Tactic.NormNum
import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

/-!
# Higham equation (4.7): failed strict-Sterbenz proof routes

Source-facing counterexamples showing why the printed magnitude hypothesis
does not by itself supply the strict signed-Sterbenz certificates attempted in
intermediate proofs of Higham equation (4.7).
-/

/-- The source magnitude condition `|b| < |a|` does not by itself imply the
signed Sterbenz certificate between `a` and the exact sum `a+b`.

The cancellation pair `a = 1`, `b = -3/4` has `|b| < |a|` and positive exact
sum `1/4`, but neither the positive nor sign-flipped Sterbenz ratio condition
holds between `a` and `a+b`.  Thus the full base-2 proof of Higham equation
(4.7) needs a real FastTwoSum/Dekker-Knuth split, not just the source
magnitude hypothesis plus the existing Sterbenz bridge. -/
theorem correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum
    (fmt : FloatingPointFormat) :
    ∃ a b : ℝ,
      |b| < |a| ∧ 0 < a + b ∧
        ¬ (fmt.sterbenzRatioCondition a (a + b) ∨
          fmt.sterbenzRatioCondition (-a) (-(a + b))) := by
  refine ⟨1, (-3 / 4 : ℝ), ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · unfold FloatingPointFormat.sterbenzRatioCondition
    norm_num

/-- A tiny binary format used to test the endpoint of the strict Sterbenz
route for the C4.4/FastTwoSum proof.

With base `2` and precision `t = 2`, the exact value `1 + 3/4 = 7/4` is the
tie between `3/2` and `2`; round-to-even selects `2` because the left endpoint
has odd mantissa `3`. -/
def correctionFormulaStrictSterbenzEndpointFormat : FloatingPointFormat where
  beta := 2
  t := 2
  emin := 0
  emax := 2
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

/-- Endpoint computation for the strict-Sterbenz route counterexample.

In the two-digit binary format above, `fl(1 + 3/4) = 2`.  This is an inexact
first addition satisfying the printed `|b| < |a|` order, but the rounded sum is
exactly `2*a`, so the local strict Sterbenz predicate between `a` and `s`
cannot hold. -/
theorem correctionFormulaStrictSterbenzEndpoint_round_one_add_three_quarters :
    correctionFormulaStrictSterbenzEndpointFormat.finiteRoundToEvenOp
      BasicOp.add (1 : ℝ) (3 / 4 : ℝ) = (2 : ℝ) := by
  let fmt := correctionFormulaStrictSterbenzEndpointFormat
  let left : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa (1 : ℤ)
  let right : ℝ := fmt.normalizedValue false fmt.minNormalMantissa (2 : ℤ)
  let x : ℝ := (7 / 4 : ℝ)
  have hm : fmt.normalizedMantissa fmt.maxNormalMantissa :=
    fmt.maxNormalMantissa_normalized
  have hboundary : fmt.boundaryAdjacentNormalized left right := by
    exact ⟨false, (1 : ℤ), Or.inl ⟨rfl, rfl⟩⟩
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hleft_value : left = (3 / 2 : ℝ) := by
    norm_num [left, fmt, correctionFormulaStrictSterbenzEndpointFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.minNormalMantissa, zpow_neg]
  have hright_value : right = (2 : ℝ) := by
    norm_num [right, fmt, correctionFormulaStrictSterbenzEndpointFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.minNormalMantissa, zpow_neg]
  have hstrict : left < x ∧ x < right := by
    rw [hleft_value, hright_value]
    norm_num [x]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, correctionFormulaStrictSterbenzEndpointFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · norm_num [x, fmt, correctionFormulaStrictSterbenzEndpointFormat,
        FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
      exact (le_of_not_gt (by norm_num : ¬ (3 : ℝ) < 7 / 4))
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxrange
  have hleft_repr :
      left = fmt.normalizedValue false fmt.maxNormalMantissa (1 : ℤ) := rfl
  have htie : |x - left| = |x - right| := by
    rw [hleft_value, hright_value]
    norm_num [x]
  have hodd : ¬ FloatingPointFormat.evenMantissa fmt.maxNormalMantissa := by
    norm_num [fmt, correctionFormulaStrictSterbenzEndpointFormat,
      FloatingPointFormat.maxNormalMantissa, FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = right :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft_repr htie hodd
  change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.add (1 : ℝ) (3 / 4 : ℝ)) =
    (2 : ℝ)
  have hxop : BasicOp.exact BasicOp.add (1 : ℝ) (3 / 4 : ℝ) = x := by
    norm_num [BasicOp.exact, x]
  rw [hxop]
  simpa [fmt, hright_value] using hround

/-- The strict signed-Sterbenz line-2 condition is not implied by the printed
base-2 FastTwoSum hypotheses plus an inexact first addition.

This rules out the previous C4.4 bottleneck subtarget as stated.  The endpoint
case has finite binary operands, `|b| < |a|`, finite-normal exact sum, and an
inexact rounded first add, but `fl(a+b) = 2*a`, so the local strict
`sterbenzRatioCondition` fails in both sign orientations.  A complete
FastTwoSum proof must therefore use a corrected line-2 dependency, for example
an inclusive Sterbenz endpoint branch or a direct representability theorem for
`a - fl(a+b)`. -/
theorem correctionFormula_base2_abs_gt_inexact_not_imply_signed_sterbenz :
    ∃ fmt : FloatingPointFormat, ∃ a b : ℝ,
      fmt.beta = 2 ∧ 1 < fmt.t ∧
        fmt.finiteSystem a ∧ fmt.finiteSystem b ∧
        |b| < |a| ∧ fmt.finiteNormalRange (a + b) ∧
        fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b ∧
        ¬ (fmt.sterbenzRatioCondition a
              (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
            fmt.sterbenzRatioCondition (-a)
              (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) := by
  refine
    ⟨correctionFormulaStrictSterbenzEndpointFormat,
      (1 : ℝ), (3 / 4 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [correctionFormulaStrictSterbenzEndpointFormat]
  · norm_num [correctionFormulaStrictSterbenzEndpointFormat]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 2, (1 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        correctionFormulaStrictSterbenzEndpointFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        correctionFormulaStrictSterbenzEndpointFormat]
    · norm_num [FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue, FloatingPointFormat.betaR,
        correctionFormulaStrictSterbenzEndpointFormat, zpow_neg]
      rfl
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 3, (0 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        correctionFormulaStrictSterbenzEndpointFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        correctionFormulaStrictSterbenzEndpointFormat]
    · norm_num [FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue, FloatingPointFormat.betaR,
        correctionFormulaStrictSterbenzEndpointFormat, zpow_neg]
  · norm_num
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
      correctionFormulaStrictSterbenzEndpointFormat, zpow_neg]
    exact (le_of_not_gt (by norm_num : ¬ (3 : ℝ) < 7 / 4))
  · rw [correctionFormulaStrictSterbenzEndpoint_round_one_add_three_quarters]
    norm_num
  · rw [correctionFormulaStrictSterbenzEndpoint_round_one_add_three_quarters]
    unfold FloatingPointFormat.sterbenzRatioCondition
    norm_num

end NumStability
