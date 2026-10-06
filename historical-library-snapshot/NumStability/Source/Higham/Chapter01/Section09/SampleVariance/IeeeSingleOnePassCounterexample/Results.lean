-- NumStability/Source/Higham/Chapter01/Section09/SampleVariance/IeeeSingleOnePassCounterexample/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Analysis.SampleVariance`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Statistics.SampleVariance.Core
import NumStability.Analysis.Statistics.SampleVariance.TwoPass
import NumStability.Analysis.Statistics.SampleVariance.Updating
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Source.Higham.Chapter01.Problem07.SampleVarianceConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter01.Problem10.TwoPassSampleVariance.Bounds
import NumStability.Source.Higham.Chapter01.Section09.SampleVariance.Examples

/-!
# Results

Relocated from `NumStability.Analysis.SampleVariance` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


-- Analysis/SampleVariance.lean
--
-- Exact sample-variance algebra for Higham Chapter 1, Section 1.9.
















namespace NumStability

open scoped BigOperators Topology

/-!
# Sample-Variance Algebra

Higham Chapter 1, Section 1.9 contrasts mathematically equivalent formulae
for the sample variance.  This file records the exact real-arithmetic
identities behind formulas (1.4) and (1.5), plus the shifted one-pass identity.
The floating-point stability bounds for the corresponding algorithms are
separate obligations.
-/




















































































































































-- ============================================================
-- Concrete binary32 one-pass trace for Higham §1.9
-- ============================================================

private abbrev sampleVarianceIeeeSingleFormat : FloatingPointFormat :=
  FloatingPointFormat.ieeeSingleFormat


private theorem ieeeSingleFiniteSystem_of_normalizedExponentRepresentation
    {x : ℝ} {e : ℤ}
    (h : sampleVarianceIeeeSingleFormat.normalizedExponentRepresentation x e) :
    sampleVarianceIeeeSingleFormat.finiteSystem x :=
  Or.inr (Or.inl
    (FloatingPointFormat.normalizedExponentRepresentation_normalizedSystem h))


private theorem ieeeSingle_finiteSystem_zero :
    sampleVarianceIeeeSingleFormat.finiteSystem (0 : ℝ) :=
  Or.inl rfl


private theorem ieeeSingle_finiteSystem_10000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (10000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 14)
  refine ⟨false, 10240000, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_10001 :
    sampleVarianceIeeeSingleFormat.finiteSystem (10001 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 14)
  refine ⟨false, 10241024, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_10002 :
    sampleVarianceIeeeSingleFormat.finiteSystem (10002 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 14)
  refine ⟨false, 10242048, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_20001 :
    sampleVarianceIeeeSingleFormat.finiteSystem (20001 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 15)
  refine ⟨false, 10240512, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_30003 :
    sampleVarianceIeeeSingleFormat.finiteSystem (30003 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 15)
  refine ⟨false, 15361536, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_100000000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (100000000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 27)
  refine ⟨false, 12500000, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_200020000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (200020000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 28)
  refine ⟨false, 12501250, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_300060000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (300060000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 29)
  refine ⟨false, 9376875, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_300059968 :
    sampleVarianceIeeeSingleFormat.finiteSystem (300059968 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 29)
  refine ⟨false, 9376874, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_neg32 :
    sampleVarianceIeeeSingleFormat.finiteSystem (-32 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 6)
  refine ⟨true, 8388608, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl


private theorem ieeeSingle_finiteSystem_neg16 :
    sampleVarianceIeeeSingleFormat.finiteSystem (-16 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 5)
  refine ⟨true, 8388608, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl














/-- Rounded binary32 square of `10000` in the one-pass sample-variance path. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sq0 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_x0
    sampleVarianceOnePassIeeeSingle_x0


/-- Rounded binary32 square of `10001` in the one-pass sample-variance path. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sq1 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
    sampleVarianceOnePassIeeeSingle_x1


/-- Rounded binary32 square of `10002` in the one-pass sample-variance path. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sq2 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
    sampleVarianceOnePassIeeeSingle_x2


/-- First rounded binary32 sum in the one-pass sum-of-squares accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sumSq01 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_sq0
    sampleVarianceOnePassIeeeSingle_sq1


/-- Final rounded binary32 sum-of-squares accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sumSq : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_sumSq01
    sampleVarianceOnePassIeeeSingle_sq2


/-- First rounded binary32 ordinary sum accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sum01 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_x0
    sampleVarianceOnePassIeeeSingle_x1


/-- Final rounded binary32 ordinary sum accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sum : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_sum01
    sampleVarianceOnePassIeeeSingle_x2


/-- Rounded binary32 square of the rounded ordinary sum. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sumSquare : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_sum
    sampleVarianceOnePassIeeeSingle_sum


/-- Rounded binary32 quotient `(rounded sum)^2 / 3`. -/
noncomputable def sampleVarianceOnePassIeeeSingle_meanSquareTerm : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.div sampleVarianceOnePassIeeeSingle_sumSquare 3


/-- Rounded binary32 cancellation numerator in the one-pass variance formula. -/
noncomputable def sampleVarianceOnePassIeeeSingle_numerator : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.sub sampleVarianceOnePassIeeeSingle_sumSq
    sampleVarianceOnePassIeeeSingle_meanSquareTerm


/-- Rounded binary32 one-pass sample-variance trace for Higham §1.9's data. -/
noncomputable def sampleVarianceOnePassIeeeSingleTrace : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.div sampleVarianceOnePassIeeeSingle_numerator 2


/-- The four nontrivial binary32 nearest/even primitive values in the concrete
one-pass sample-variance trace.  Exact grid-point operations in the same trace
are proved below from `finiteSystem` facts; later theorems prove these four
selector equalities outright and close the full concrete operation trace. -/
def sampleVarianceOnePassIeeeSingleRoundingCertificate : Prop :=
  sampleVarianceOnePassIeeeSingle_sq1 = 100020000 ∧
    sampleVarianceOnePassIeeeSingle_sq2 = 100040000 ∧
      sampleVarianceOnePassIeeeSingle_sumSquare = 900180032 ∧
        sampleVarianceOnePassIeeeSingle_meanSquareTerm = 300060000


/-- Source round-to-even evidence for the non-grid binary32 primitive
`10001^2 -> 100020000` in Higham §1.9's one-pass example. -/
theorem sampleVarianceOnePassIeeeSingle_sq1_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
        sampleVarianceOnePassIeeeSingle_x1) (100020000 : ℝ) := by
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x1]
  change sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
    (100020001 : ℝ) (100020000 : ℝ)
  refine Or.inl ⟨27, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨100020000, 100020008, 12502500, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 12502500, 27, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 27, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_left_closer]
      norm_num


private theorem sampleVarianceOnePassIeeeSingle_sq1_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange (100020001 : ℝ) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change (100020001 : ℝ) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : (100020001 : ℝ) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge


/-- The total binary32 round-to-even selector sends `10001^2 = 100020001` to
`100020000`; the left endpoint of the adjacent binary32 bracket is strictly
nearer than the right endpoint. -/
theorem sampleVarianceOnePassIeeeSingle_sq1_eq :
    sampleVarianceOnePassIeeeSingle_sq1 = 100020000 := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (100020001 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (100020001 : ℝ)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_sq1_finiteNormalRange
  have hround :
      sampleVarianceIeeeSingleFormat.nearestRoundingToUnbounded
        (100020001 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (100020001 : ℝ)) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (100020000 : ℝ) (100020008 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 12502500, 27, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  have hrounded :
      sampleVarianceIeeeSingleFormat.finiteRoundToEven (100020001 : ℝ) =
        (100020000 : ℝ) :=
    FloatingPointFormat.nearestRoundingToUnbounded_eq_left_of_realOrderAdjacent_ordered_between_of_left_closer
      hround hadj (by norm_num) (by norm_num)
  unfold sampleVarianceOnePassIeeeSingle_sq1
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
        sampleVarianceOnePassIeeeSingle_x1) = (100020000 : ℝ)
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x1]
  exact hrounded


/-- Source round-to-even evidence for the halfway binary32 primitive
`10002^2 -> 100040000`: the endpoints are equally near and the left mantissa
is even. -/
theorem sampleVarianceOnePassIeeeSingle_sq2_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
        sampleVarianceOnePassIeeeSingle_x2) (100040000 : ℝ) := by
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]
  change sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
    (100040004 : ℝ) (100040000 : ℝ)
  refine Or.inl ⟨27, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨100040000, 100040008, 12505000, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 12505000, 27, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 27, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_tie_even]
      · norm_num
      · norm_num [FloatingPointFormat.evenMantissa]


private theorem sampleVarianceOnePassIeeeSingle_sq2_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange (100040004 : ℝ) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change (100040004 : ℝ) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : (100040004 : ℝ) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge


/-- The total binary32 round-to-even selector sends the exact halfway square
`10002^2 = 100040004` to the even-left endpoint `100040000`. -/
theorem sampleVarianceOnePassIeeeSingle_sq2_eq :
    sampleVarianceOnePassIeeeSingle_sq2 = 100040000 := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (100040004 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (100040004 : ℝ)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_sq2_finiteNormalRange
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (100040000 : ℝ) (100040008 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 12505000, 27, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  have hleftMantissa :
      sampleVarianceIeeeSingleFormat.normalizedMantissa 12505000 := by
    norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hleft :
      (100040000 : ℝ) =
        sampleVarianceIeeeSingleFormat.normalizedValue false 12505000 27 := by
    norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR]
    try rfl
  have hrounded :
      sampleVarianceIeeeSingleFormat.finiteRoundToEven (100040004 : ℝ) =
        (100040000 : ℝ) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj (by norm_num) hleftMantissa hleft
      (by norm_num) (by norm_num [FloatingPointFormat.evenMantissa])
  unfold sampleVarianceOnePassIeeeSingle_sq2
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
        sampleVarianceOnePassIeeeSingle_x2) = (100040000 : ℝ)
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]
  exact hrounded


/-- Source round-to-even evidence for the exact binary32 primitive value
`30003^2 -> 900180032` in the one-pass trace. -/
theorem sampleVarianceOnePassIeeeSingle_sumSquare_exact_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (900180009 : ℝ) (900180032 : ℝ) := by
  refine Or.inl ⟨30, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨900179968, 900180032, 14065312, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 14065312, 30, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 30, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_of_right_closer]
      norm_num


private theorem sampleVarianceOnePassIeeeSingle_sumSquare_exact_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange (900180009 : ℝ) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change (900180009 : ℝ) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : (900180009 : ℝ) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge


private theorem sampleVarianceOnePassIeeeSingle_sumSquare_exact_round_eq :
    sampleVarianceIeeeSingleFormat.finiteRoundToEven (900180009 : ℝ) =
      (900180032 : ℝ) := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (900180009 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (900180009 : ℝ)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_sumSquare_exact_finiteNormalRange
  have hround :
      sampleVarianceIeeeSingleFormat.nearestRoundingToUnbounded
        (900180009 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (900180009 : ℝ)) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (900179968 : ℝ) (900180032 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 14065312, 30, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  exact
    FloatingPointFormat.nearestRoundingToUnbounded_eq_right_of_realOrderAdjacent_ordered_between_of_right_closer
      hround hadj (by norm_num) (by norm_num)


/-- Source round-to-even evidence for the exact binary32 primitive
`900180032 / 3 -> 300060000` in the one-pass trace. -/
theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      ((900180032 : ℝ) / 3) (300060000 : ℝ) := by
  refine Or.inl ⟨29, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨300060000, 300060032, 9376875, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 9376875, 29, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 29, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_left_closer]
      norm_num


private theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange ((900180032 : ℝ) / 3) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · have hpos : 0 ≤ ((900180032 : ℝ) / 3) := by
      norm_num
    rw [abs_of_nonneg hpos]
    simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change ((900180032 : ℝ) / 3) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : ((900180032 : ℝ) / 3) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge


private theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_round_eq :
    sampleVarianceIeeeSingleFormat.finiteRoundToEven ((900180032 : ℝ) / 3) =
      (300060000 : ℝ) := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        ((900180032 : ℝ) / 3)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven ((900180032 : ℝ) / 3)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_finiteNormalRange
  have hround :
      sampleVarianceIeeeSingleFormat.nearestRoundingToUnbounded
        ((900180032 : ℝ) / 3)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven ((900180032 : ℝ) / 3)) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (300060000 : ℝ) (300060032 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 9376875, 29, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  exact
    FloatingPointFormat.nearestRoundingToUnbounded_eq_left_of_realOrderAdjacent_ordered_between_of_left_closer
      hround hadj (by norm_num) (by norm_num)


/-- Source round-to-even evidence for the binary32 division primitive once the
rounded sum square is known to be `900180032`. -/
theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_sourceRoundToEvenEvidence_of_sumSquare
    (hsumSquare : sampleVarianceOnePassIeeeSingle_sumSquare = 900180032) :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.div sampleVarianceOnePassIeeeSingle_sumSquare 3)
      (300060000 : ℝ) := by
  rw [hsumSquare]
  exact sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence


/-- The first square in the concrete binary32 one-pass trace is exact. -/
theorem sampleVarianceOnePassIeeeSingle_sq0_eq :
    sampleVarianceOnePassIeeeSingle_sq0 = 100000000 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x0
          sampleVarianceOnePassIeeeSingle_x0) := by
    norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0]
    exact ieeeSingle_finiteSystem_100000000
  unfold sampleVarianceOnePassIeeeSingle_sq0
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0]


/-- The first ordinary sum in the concrete binary32 one-pass trace is exact. -/
theorem sampleVarianceOnePassIeeeSingle_sum01_eq :
    sampleVarianceOnePassIeeeSingle_sum01 = 20001 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_x0
          sampleVarianceOnePassIeeeSingle_x1) := by
    norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0,
      sampleVarianceOnePassIeeeSingle_x1]
    exact ieeeSingle_finiteSystem_20001
  unfold sampleVarianceOnePassIeeeSingle_sum01
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0,
    sampleVarianceOnePassIeeeSingle_x1]


/-- The ordinary sum accumulator in the concrete binary32 one-pass trace is
exact. -/
theorem sampleVarianceOnePassIeeeSingle_sum_eq :
    sampleVarianceOnePassIeeeSingle_sum = 30003 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_sum01
          sampleVarianceOnePassIeeeSingle_x2) := by
    rw [sampleVarianceOnePassIeeeSingle_sum01_eq]
    norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]
    exact ieeeSingle_finiteSystem_30003
  unfold sampleVarianceOnePassIeeeSingle_sum
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    sampleVarianceOnePassIeeeSingle_sum01_eq]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]


/-- Source round-to-even evidence for the binary32 primitive
`sampleVarianceOnePassIeeeSingle_sum^2 -> 900180032`, after the ordinary sum
accumulator has been proved exact. -/
theorem sampleVarianceOnePassIeeeSingle_sumSquare_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_sum
        sampleVarianceOnePassIeeeSingle_sum) (900180032 : ℝ) := by
  rw [sampleVarianceOnePassIeeeSingle_sum_eq]
  have hmul : BasicOp.exact BasicOp.mul (30003 : ℝ) (30003 : ℝ) =
      (900180009 : ℝ) := by
    norm_num [BasicOp.exact]
  simpa [hmul] using
    sampleVarianceOnePassIeeeSingle_sumSquare_exact_sourceRoundToEvenEvidence


/-- The rounded binary32 square of the exact ordinary sum is the displayed
single-precision value `900180032`. -/
theorem sampleVarianceOnePassIeeeSingle_sumSquare_eq :
    sampleVarianceOnePassIeeeSingle_sumSquare = 900180032 := by
  unfold sampleVarianceOnePassIeeeSingle_sumSquare
  rw [sampleVarianceOnePassIeeeSingle_sum_eq]
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.mul (30003 : ℝ) (30003 : ℝ)) = (900180032 : ℝ)
  norm_num [BasicOp.exact]
  exact sampleVarianceOnePassIeeeSingle_sumSquare_exact_round_eq


/-- The rounded binary32 quotient `(rounded sum)^2 / 3` is the displayed
single-precision value `300060000`. -/
theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_eq :
    sampleVarianceOnePassIeeeSingle_meanSquareTerm = 300060000 := by
  unfold sampleVarianceOnePassIeeeSingle_meanSquareTerm
  rw [sampleVarianceOnePassIeeeSingle_sumSquare_eq]
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.div (900180032 : ℝ) 3) = (300060000 : ℝ)
  norm_num [BasicOp.exact]
  exact sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_round_eq


/-- Closed source-level evidence for the four non-grid binary32 primitive
roundings used by the one-pass trace.  This proves the intended grid endpoints
and tie choices.  Later total-selector equalities turn this source evidence into
the closed concrete operation trace. -/
theorem sampleVarianceOnePassIeeeSingle_sourceRoundingEvidenceCertificate :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
          sampleVarianceOnePassIeeeSingle_x1) (100020000 : ℝ) ∧
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
          sampleVarianceOnePassIeeeSingle_x2) (100040000 : ℝ) ∧
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_sum
          sampleVarianceOnePassIeeeSingle_sum) (900180032 : ℝ) ∧
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        ((900180032 : ℝ) / 3) (300060000 : ℝ) := by
  exact ⟨sampleVarianceOnePassIeeeSingle_sq1_sourceRoundToEvenEvidence,
    sampleVarianceOnePassIeeeSingle_sq2_sourceRoundToEvenEvidence,
    sampleVarianceOnePassIeeeSingle_sumSquare_sourceRoundToEvenEvidence,
    sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence⟩


/-- The closed square, sum-square, and mean-square primitive equalities imply
the full concrete binary32 rounding certificate. -/
theorem sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingleRoundingCertificate := by
  exact ⟨sampleVarianceOnePassIeeeSingle_sq1_eq, hsq2,
    sampleVarianceOnePassIeeeSingle_sumSquare_eq,
    sampleVarianceOnePassIeeeSingle_meanSquareTerm_eq⟩


/-- The concrete binary32 one-pass operation trace has all four non-grid
nearest/even primitive roundings closed. -/
theorem sampleVarianceOnePassIeeeSingleRoundingCertificate_closed :
    sampleVarianceOnePassIeeeSingleRoundingCertificate :=
  sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq
    sampleVarianceOnePassIeeeSingle_sq2_eq


private theorem sampleVarianceOnePassIeeeSingle_sumSq01_eq_of_sq1
    (hsq1 : sampleVarianceOnePassIeeeSingle_sq1 = 100020000) :
    sampleVarianceOnePassIeeeSingle_sumSq01 = 200020000 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_sq0
          sampleVarianceOnePassIeeeSingle_sq1) := by
    rw [sampleVarianceOnePassIeeeSingle_sq0_eq, hsq1]
    norm_num [BasicOp.exact]
    exact ieeeSingle_finiteSystem_200020000
  unfold sampleVarianceOnePassIeeeSingle_sumSq01
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    sampleVarianceOnePassIeeeSingle_sq0_eq, hsq1]
  norm_num [BasicOp.exact]


/-- Under the two non-grid square-rounding facts, the sum-of-squares accumulator
in the concrete binary32 one-pass trace is exactly `300060000`. -/
theorem sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2
    (hsq1 : sampleVarianceOnePassIeeeSingle_sq1 = 100020000)
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingle_sumSq = 300060000 := by
  have hsumSq01 := sampleVarianceOnePassIeeeSingle_sumSq01_eq_of_sq1 hsq1
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_sumSq01
          sampleVarianceOnePassIeeeSingle_sq2) := by
    rw [hsumSq01, hsq2]
    norm_num [BasicOp.exact]
    exact ieeeSingle_finiteSystem_300060000
  unfold sampleVarianceOnePassIeeeSingle_sumSq
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    hsumSq01, hsq2]
  norm_num [BasicOp.exact]


/-- With the first square unconditional, the final sum-of-squares accumulator
can be reduced to the `10002^2` primitive equality. -/
theorem sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq2
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingle_sumSq = 300060000 :=
  sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2
    sampleVarianceOnePassIeeeSingle_sq1_eq hsq2


/-- The final sum-of-squares accumulator in the concrete binary32 one-pass trace
is exactly `300060000`. -/
theorem sampleVarianceOnePassIeeeSingle_sumSq_eq :
    sampleVarianceOnePassIeeeSingle_sumSq = 300060000 :=
  sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq2
    sampleVarianceOnePassIeeeSingle_sq2_eq


private theorem sampleVarianceOnePassIeeeSingle_numerator_eq_zero_of_roundingCertificate
    (hcert : sampleVarianceOnePassIeeeSingleRoundingCertificate) :
    sampleVarianceOnePassIeeeSingle_numerator = 0 := by
  rcases hcert with ⟨hsq1, hsq2, _hsumSquare, hmeanSquare⟩
  have hsumSq := sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2 hsq1 hsq2
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub sampleVarianceOnePassIeeeSingle_sumSq
          sampleVarianceOnePassIeeeSingle_meanSquareTerm) := by
    rw [hsumSq, hmeanSquare]
    simpa [BasicOp.exact] using ieeeSingle_finiteSystem_zero
  unfold sampleVarianceOnePassIeeeSingle_numerator
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    hsumSq, hmeanSquare]
  norm_num [BasicOp.exact]
  rfl


/-- If the four non-grid binary32 primitive roundings in the §1.9 one-pass
trace have the displayed nearest/even values, then the actual rounded operation
trace returns `0.0`. -/
theorem sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate
    (hcert : sampleVarianceOnePassIeeeSingleRoundingCertificate) :
    sampleVarianceOnePassIeeeSingleTrace = 0 := by
  have hnumer :=
    sampleVarianceOnePassIeeeSingle_numerator_eq_zero_of_roundingCertificate
      hcert
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.div sampleVarianceOnePassIeeeSingle_numerator 2) := by
    rw [hnumer]
    simpa [BasicOp.exact] using ieeeSingle_finiteSystem_zero
  unfold sampleVarianceOnePassIeeeSingleTrace
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    hnumer]
  norm_num [BasicOp.exact]
  rfl


/-- Under the same concrete binary32 rounding certificate, the one-pass trace
has relative error `1` against the exact sample variance, matching Higham
§1.9's displayed single-precision result. -/
theorem sampleVarianceOnePassIeeeSingleTrace_relError_one_of_roundingCertificate
    (hcert : sampleVarianceOnePassIeeeSingleRoundingCertificate) :
    relError sampleVarianceOnePassIeeeSingleTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 := by
  rw [sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate hcert,
    sampleVarianceTwoPass_example_10000_10001_10002]
  norm_num [relError]
  rfl


/-- The concrete binary32 one-pass trace returns `0.0` as soon as the
`10002^2 -> 100040000` primitive equality is supplied. -/
theorem sampleVarianceOnePassIeeeSingleTrace_zero_of_sq2_eq
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingleTrace = 0 :=
  sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate
    (sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq hsq2)


/-- The concrete binary32 one-pass trace returns `0.0`. -/
theorem sampleVarianceOnePassIeeeSingleTrace_zero :
    sampleVarianceOnePassIeeeSingleTrace = 0 :=
  sampleVarianceOnePassIeeeSingleTrace_zero_of_sq2_eq
    sampleVarianceOnePassIeeeSingle_sq2_eq


/-- The `10002^2 -> 100040000` primitive equality also suffices for the
relative-error-`1` statement against the exact two-pass sample variance. -/
theorem sampleVarianceOnePassIeeeSingleTrace_relError_one_of_sq2_eq
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    relError sampleVarianceOnePassIeeeSingleTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 :=
  sampleVarianceOnePassIeeeSingleTrace_relError_one_of_roundingCertificate
    (sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq hsq2)


/-- The concrete binary32 one-pass trace has relative error `1` against the
exact two-pass sample variance. -/
theorem sampleVarianceOnePassIeeeSingleTrace_relError_one :
    relError sampleVarianceOnePassIeeeSingleTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 :=
  sampleVarianceOnePassIeeeSingleTrace_relError_one_of_sq2_eq
    sampleVarianceOnePassIeeeSingle_sq2_eq


-- ============================================================
-- Supplied rounded-aggregate negative final-operation trace
-- ============================================================















/-- Rounded binary32 final numerator from the supplied negative aggregate
diagnostic. -/
noncomputable def sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator :
    ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.sub sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq
    sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm


/-- Rounded binary32 final variance quotient from the supplied negative
aggregate diagnostic. -/
noncomputable def sampleVarianceOnePassIeeeSingleNegativeAggregateTrace : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.div sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator 2


/-- The supplied rounded aggregates are binary32 finite-system values. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregate_inputs_finiteSystem :
    sampleVarianceIeeeSingleFormat.finiteSystem
        sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq ∧
      sampleVarianceIeeeSingleFormat.finiteSystem
        sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm := by
  exact ⟨by
      simpa [sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq] using
        ieeeSingle_finiteSystem_300059968,
    by
      simpa [sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm] using
        ieeeSingle_finiteSystem_300060000⟩


/-- The final rounded subtraction in the supplied negative aggregate diagnostic
is exact and gives `-32`. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq :
    sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator = -32 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub
          sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq
          sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm) := by
    have hcalc :
        BasicOp.exact BasicOp.sub
            sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq
            sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm =
          (-32 : ℝ) := by
      norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq,
        sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm]
    simpa [hcalc] using ieeeSingle_finiteSystem_neg32
  unfold sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq,
    sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm]


/-- The supplied rounded-aggregate final operation trace returns the concrete
negative binary32 value `-16`. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen :
    sampleVarianceOnePassIeeeSingleNegativeAggregateTrace = -16 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.div
          sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator 2) := by
    have hcalc :
        BasicOp.exact BasicOp.div
            sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator 2 =
          (-16 : ℝ) := by
      rw [sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq]
      norm_num [BasicOp.exact]
    simpa [hcalc] using ieeeSingle_finiteSystem_neg16
  unfold sampleVarianceOnePassIeeeSingleNegativeAggregateTrace
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq]
  norm_num [BasicOp.exact]


/-- The supplied rounded-aggregate final operation trace is strictly negative. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_lt_zero :
    sampleVarianceOnePassIeeeSingleNegativeAggregateTrace < 0 := by
  rw [sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen]
  norm_num


/-- Against the exact sample variance `1` for `[10000,10001,10002]`, the
supplied rounded-aggregate negative final trace has relative error `17`. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_relError :
    relError sampleVarianceOnePassIeeeSingleNegativeAggregateTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 17 := by
  rw [sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen,
    sampleVarianceTwoPass_example_10000_10001_10002]
  norm_num [relError]
  rfl

end NumStability
