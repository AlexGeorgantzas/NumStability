import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError
import NumStability.Analysis.FloatingPointArithmetic.Rounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.ProblemDependentStability.HessenbergDeterminant
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter01.Section16.ProblemDependentStability.ExactExample

-- Analysis/ProblemDependentStability.lean
--
-- Exact examples from Higham Chapter 1, Section 1.16.











namespace NumStability

open scoped BigOperators

/-!
# Stability Depends on the Problem

This file records exact algebra from the upper-Hessenberg example in Higham
Chapter 1, Section 1.16. The floating-point stability and instability claims are
not closed here; the theorems below expose the exact matrix shape, right-hand
side, no-pivot diagonal product, and large first multiplier used by the example.
-/









































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-! ## Table 1.3 displayed single-precision data -/

/-- The finite binary32 format used for the Table 1.3 primitive-input storage
audit.  It records Higham's finite-format parameters, not infinities, NaNs, or
exception flags. -/
abbrev hessenbergDetExampleTable13IeeeSingleFormat : FloatingPointFormat :=
  FloatingPointFormat.ieeeSingleFormat

/-- Source decimal parameter in the Table 1.3 example. -/
noncomputable def hessenbergDetExampleTable13SourceAlpha : ℝ :=
  1 / (10 : ℝ) ^ 7

/-- The binary32 stored value of the source decimal `alpha = 10^-7`.  This is
kept distinct from the source real number so later primitive traces do not
silently assume exact storage of `10^-7`. -/
noncomputable def hessenbergDetExampleTable13StoredAlpha : ℝ :=
  hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
    hessenbergDetExampleTable13SourceAlpha

/-- The Table 1.3 input matrix after binary32 storage of each source entry. -/
noncomputable def hessenbergDetExampleTable13StoredMatrix :
    Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
      (hessenbergDetExampleMatrix hessenbergDetExampleTable13SourceAlpha i j)

/-- The Table 1.3 right-hand side after binary32 storage of each source entry. -/
noncomputable def hessenbergDetExampleTable13StoredRhs : Fin 4 → ℝ :=
  fun i =>
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
      (hessenbergDetExampleRhs hessenbergDetExampleTable13SourceAlpha i)

/-- The exact real number `1` is representable in the Table 1.3 binary32
format. -/
theorem hessenbergDetExampleTable13IeeeSingle_one_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem (1 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have he : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, fmt.minNormalMantissa, (1 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.minNormalMantissa,
    FloatingPointFormat.betaR, zpow_neg]
  rfl

/-- The exact real number `2` is representable in the Table 1.3 binary32
format. -/
theorem hessenbergDetExampleTable13IeeeSingle_two_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem (2 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have he : fmt.exponentInRange (2 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, fmt.minNormalMantissa, (2 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.minNormalMantissa,
    FloatingPointFormat.betaR, zpow_neg]
  rfl

@[simp] theorem hessenbergDetExampleTable13IeeeSingle_round_zero :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven (0 : ℝ) =
      0 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  simpa [fmt] using
    (fmt.finiteRoundToEven_eq_self_of_finiteSystem
      (x := (0 : ℝ)) fmt.finiteSystem_zero)

@[simp] theorem hessenbergDetExampleTable13IeeeSingle_round_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven (1 : ℝ) =
      1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  simpa [fmt] using
    (fmt.finiteRoundToEven_eq_self_of_finiteSystem
      hessenbergDetExampleTable13IeeeSingle_one_finiteSystem)

@[simp] theorem hessenbergDetExampleTable13IeeeSingle_round_neg_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven (-1 : ℝ) =
      -1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfinite :
      fmt.finiteSystem (-(1 : ℝ)) :=
    fmt.finiteSystem_neg
      hessenbergDetExampleTable13IeeeSingle_one_finiteSystem
  simpa [fmt] using
    (fmt.finiteRoundToEven_eq_self_of_finiteSystem hfinite)

@[simp] theorem hessenbergDetExampleTable13IeeeSingle_round_two :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven (2 : ℝ) =
      2 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  simpa [fmt] using
    (fmt.finiteRoundToEven_eq_self_of_finiteSystem
      hessenbergDetExampleTable13IeeeSingle_two_finiteSystem)

/-- The stored source decimal `alpha` is a finite binary32 value by construction. -/
theorem hessenbergDetExampleTable13StoredAlpha_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      hessenbergDetExampleTable13StoredAlpha := by
  exact hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven_finiteSystem
    hessenbergDetExampleTable13SourceAlpha

/-- The source decimal `10^-7` rounds to the concrete binary32 normalized value
with mantissa `14073749` and exponent `-23`. -/
theorem hessenbergDetExampleTable13StoredAlpha_eq_normalizedValue :
    hessenbergDetExampleTable13StoredAlpha =
      hessenbergDetExampleTable13IeeeSingleFormat.normalizedValue
        false 14073749 (-23 : ℤ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 14073748 (-23 : ℤ)
  let b : ℝ := fmt.normalizedValue false 14073749 (-23 : ℤ)
  let x : ℝ := hessenbergDetExampleTable13SourceAlpha
  have hm : fmt.normalizedMantissa 14073748 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (14073748 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 14073748, (-23 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (14073748 : ℝ) * (2 : ℝ) ^ (-47 : ℤ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (14073749 : ℝ) * (2 : ℝ) ^ (-47 : ℤ) := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange,
      abs_of_pos (by
        norm_num [x, hessenbergDetExampleTable13SourceAlpha])]
    constructor
    · norm_num [x, hessenbergDetExampleTable13SourceAlpha, fmt,
        hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        x = (1 / (10 : ℝ) ^ 7) := by
          rfl
        _ ≤ 1 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (1 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, hessenbergDetExampleTable13SourceAlpha, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, hessenbergDetExampleTable13SourceAlpha, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [hessenbergDetExampleTable13StoredAlpha, x, b, fmt] using hround

/-- Closed rational form of the binary32 stored value of `10^-7`. -/
theorem hessenbergDetExampleTable13StoredAlpha_eq :
    hessenbergDetExampleTable13StoredAlpha =
      14073749 / (2 : ℝ) ^ 47 := by
  rw [hessenbergDetExampleTable13StoredAlpha_eq_normalizedValue]
  norm_num [hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The stored Table 1.3 `alpha` is positive. -/
theorem hessenbergDetExampleTable13StoredAlpha_pos :
    0 < hessenbergDetExampleTable13StoredAlpha := by
  rw [hessenbergDetExampleTable13StoredAlpha_eq]
  norm_num

/-- The stored Table 1.3 `alpha` is nonzero, so the first no-pivot division has
a nonzero denominator. -/
theorem hessenbergDetExampleTable13StoredAlpha_ne_zero :
    hessenbergDetExampleTable13StoredAlpha ≠ 0 :=
  ne_of_gt hessenbergDetExampleTable13StoredAlpha_pos

/-- Every entry of the stored Table 1.3 matrix is a finite binary32 value. -/
theorem hessenbergDetExampleTable13StoredMatrix_finiteSystem
    (i j : Fin 4) :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (hessenbergDetExampleTable13StoredMatrix i j) := by
  exact hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven_finiteSystem
    (hessenbergDetExampleMatrix hessenbergDetExampleTable13SourceAlpha i j)

/-- Every entry of the stored Table 1.3 right-hand side is a finite binary32
value. -/
theorem hessenbergDetExampleTable13StoredRhs_finiteSystem (i : Fin 4) :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (hessenbergDetExampleTable13StoredRhs i) := by
  exact hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven_finiteSystem
    (hessenbergDetExampleRhs hessenbergDetExampleTable13SourceAlpha i)

/-- Binary32 storage of the Table 1.3 matrix changes only the non-representable
source decimal `alpha`; the `0`, `1`, and `-1` entries are stored exactly. -/
theorem hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix :
    hessenbergDetExampleTable13StoredMatrix =
      hessenbergDetExampleMatrix hessenbergDetExampleTable13StoredAlpha := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [hessenbergDetExampleTable13StoredMatrix,
      hessenbergDetExampleTable13StoredAlpha,
      hessenbergDetExampleTable13SourceAlpha,
      hessenbergDetExampleMatrix]

/-- The stored Table 1.3 matrix remains upper Hessenberg. -/
theorem hessenbergDetExampleTable13StoredMatrix_isUpperHessenberg :
    IsUpperHessenbergMatrix 4 hessenbergDetExampleTable13StoredMatrix := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  exact hessenbergDetExample_isUpperHessenberg
    hessenbergDetExampleTable13StoredAlpha

/-- The first stored no-pivot Table 1.3 matrix pivot is nonzero. -/
theorem hessenbergDetExampleTable13StoredMatrix_pivot0_ne_zero :
    hessenbergDetExampleTable13StoredMatrix 0 0 ≠ 0 := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simpa [hessenbergDetExampleMatrix] using
    hessenbergDetExampleTable13StoredAlpha_ne_zero

/-- Exact determinant of the stored-input Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_det_eq :
    Matrix.det
        (hessenbergDetExampleTable13StoredMatrix :
          Matrix (Fin 4) (Fin 4) ℝ) =
      2 * (hessenbergDetExampleTable13StoredAlpha + 1) := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  exact hessenbergDetExampleMatrix_det_eq
    hessenbergDetExampleTable13StoredAlpha
    hessenbergDetExampleTable13StoredAlpha_ne_zero
    (ne_of_gt (add_pos hessenbergDetExampleTable13StoredAlpha_pos zero_lt_one))

/-- The exact no-pivot determinant product theorem specialized to the stored
Table 1.3 input matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_det_eq_noPivotUDiag_prod :
    Matrix.det
        (hessenbergDetExampleTable13StoredMatrix :
          Matrix (Fin 4) (Fin 4) ℝ) =
      ∏ i : Fin 4,
        hessenbergDetExampleNoPivotUDiag
          hessenbergDetExampleTable13StoredAlpha i := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  exact hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod
    hessenbergDetExampleTable13StoredAlpha
    hessenbergDetExampleTable13StoredAlpha_ne_zero
    (ne_of_gt (add_pos hessenbergDetExampleTable13StoredAlpha_pos zero_lt_one))

/-- The first primitive no-pivot GE division for the stored Table 1.3 input:
nearest/even binary32 rounds `1 / fl32(alpha)` to exactly `10^7`. -/
theorem hessenbergDetExampleTable13_round_one_div_storedAlpha :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) hessenbergDetExampleTable13StoredAlpha =
      (10 : ℝ) ^ 7 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 9999999 (24 : ℤ)
  let b : ℝ := fmt.normalizedValue false 10000000 (24 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.div (1 : ℝ)
    hessenbergDetExampleTable13StoredAlpha
  have hm : fmt.normalizedMantissa 9999999 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (9999999 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 9999999, (24 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (9999999 : ℝ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (10000000 : ℝ) := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (2 : ℝ) ^ 47 / 14073749 := by
    simp [x, BasicOp.exact, hessenbergDetExampleTable13StoredAlpha_eq]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (2 : ℝ) ^ 47 / 14073749 ≤ (10000000 : ℝ) := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (10000000 : ℝ) ≤
            340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change fmt.finiteRoundToEven x = (10 : ℝ) ^ 7
  norm_num
  simpa [x, fmt, hb_value] using hround

/-- The first no-pivot multiplier division from the stored Table 1.3 matrix is
the concrete binary32 value `10^7`. -/
theorem hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (hessenbergDetExampleTable13StoredMatrix 1 0)
        (hessenbergDetExampleTable13StoredMatrix 0 0) =
      (10 : ℝ) ^ 7 := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simpa [hessenbergDetExampleMatrix] using
    hessenbergDetExampleTable13_round_one_div_storedAlpha

/-- The first Table 1.3 multiplier value `10^7` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_ten_pow_seven_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      ((10 : ℝ) ^ 7) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 10000000 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (24 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 10000000, (24 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The negated first Table 1.3 multiplier value is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_neg_ten_pow_seven_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-((10 : ℝ) ^ 7)) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  simpa [fmt] using
    (fmt.finiteSystem_neg
      hessenbergDetExampleTable13IeeeSingle_ten_pow_seven_finiteSystem)

/-- The first updated diagonal value `10000001` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_firstStageDiag_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (10000001 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 10000001 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (24 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 10000001, (24 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The first updated superdiagonal value `9999999` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_firstStageSuper_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (9999999 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 9999999 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (24 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 9999999, (24 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The first-stage product `fl32(10^7*(-1))` is exact. -/
theorem hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        ((10 : ℝ) ^ 7) (-1) =
      -((10 : ℝ) ^ 7) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul ((10 : ℝ) ^ 7) (-1)) := by
    convert hessenbergDetExampleTable13IeeeSingle_neg_ten_pow_seven_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := ((10 : ℝ) ^ 7)) (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The first-stage diagonal subtraction `fl32(1 - (-10^7))` is exact. -/
theorem hessenbergDetExampleTable13_round_one_sub_neg_ten_pow_seven :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (1 : ℝ) (-((10 : ℝ) ^ 7)) =
      (10000001 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (1 : ℝ) (-((10 : ℝ) ^ 7))) := by
    convert hessenbergDetExampleTable13IeeeSingle_firstStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (1 : ℝ)) (y := (-((10 : ℝ) ^ 7))) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The first-stage superdiagonal subtraction `fl32((-1) - (-10^7))` is exact. -/
theorem hessenbergDetExampleTable13_round_neg_one_sub_neg_ten_pow_seven :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1 : ℝ) (-((10 : ℝ) ^ 7)) =
      (9999999 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-1 : ℝ) (-((10 : ℝ) ^ 7))) := by
    convert hessenbergDetExampleTable13IeeeSingle_firstStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-1 : ℝ)) (y := (-((10 : ℝ) ^ 7))) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- Fully nested primitive binary32 operation trace for the first stage diagonal
update `(1,1)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_firstStage_diag11_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 1 1)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 1 0)
            (hessenbergDetExampleTable13StoredMatrix 0 0))
          (hessenbergDetExampleTable13StoredMatrix 0 1)) =
      (10000001 : ℝ) := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one,
    hessenbergDetExampleTable13_round_one_sub_neg_ten_pow_seven]

/-- Fully nested primitive binary32 operation trace for the first stage
superdiagonal update `(1,2)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_firstStage_super12_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 1 2)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 1 0)
            (hessenbergDetExampleTable13StoredMatrix 0 0))
          (hessenbergDetExampleTable13StoredMatrix 0 2)) =
      (9999999 : ℝ) := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one,
    hessenbergDetExampleTable13_round_neg_one_sub_neg_ten_pow_seven]

/-- Fully nested primitive binary32 operation trace for the first stage
superdiagonal update `(1,3)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_firstStage_super13_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 1 3)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 1 0)
            (hessenbergDetExampleTable13StoredMatrix 0 0))
          (hessenbergDetExampleTable13StoredMatrix 0 3)) =
      (9999999 : ℝ) := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one,
    hessenbergDetExampleTable13_round_neg_one_sub_neg_ten_pow_seven]

/-- The second primitive no-pivot GE division for the stored Table 1.3 trace:
nearest/even binary32 rounds `1 / 10000001` to the lower adjacent value with
mantissa `14073747` and exponent `-23`. -/
theorem hessenbergDetExampleTable13_round_one_div_firstStageDiag_eq_normalizedValue :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (10000001 : ℝ) =
      hessenbergDetExampleTable13IeeeSingleFormat.normalizedValue
        false 14073747 (-23 : ℤ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 14073747 (-23 : ℤ)
  let b : ℝ := fmt.normalizedValue false 14073748 (-23 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.div (1 : ℝ) (10000001 : ℝ)
  have hm : fmt.normalizedMantissa 14073747 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (14073747 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 14073747, (-23 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (14073747 : ℝ) * (2 : ℝ) ^ (-47 : ℤ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (14073748 : ℝ) * (2 : ℝ) ^ (-47 : ℤ) := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (1 : ℝ) / 10000001 := by
    norm_num [x, BasicOp.exact]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (1 : ℝ) / 10000001 ≤ 1 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (1 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven x =
    fmt.normalizedValue false 14073747 (-23 : ℤ)
  simpa [x, a, fmt] using hround

/-- Closed rational form of the second no-pivot multiplier division. -/
theorem hessenbergDetExampleTable13_round_one_div_firstStageDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (10000001 : ℝ) =
      14073747 / (2 : ℝ) ^ 47 := by
  rw [hessenbergDetExampleTable13_round_one_div_firstStageDiag_eq_normalizedValue]
  norm_num [hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- Fully nested primitive binary32 trace for the second no-pivot multiplier
division from the stored Table 1.3 matrix after the first-row update. -/
theorem hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (hessenbergDetExampleTable13StoredMatrix 2 1)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
          (hessenbergDetExampleTable13StoredMatrix 1 1)
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
              (hessenbergDetExampleTable13StoredMatrix 1 0)
              (hessenbergDetExampleTable13StoredMatrix 0 0))
            (hessenbergDetExampleTable13StoredMatrix 0 1))) =
      14073747 / (2 : ℝ) ^ 47 := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstStage_diag11_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simpa [hessenbergDetExampleMatrix] using
    hessenbergDetExampleTable13_round_one_div_firstStageDiag

/-- The second-stage product value `4194303/4194304` is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondStageProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (4194303 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (0 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 16777212, (0 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second-stage diagonal update value `2^-22` is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondStageDiag_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (1 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388608 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-21 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388608, (-21 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second-stage superdiagonal update value `-8388607/4194304` is
representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondStageSuper_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-8388607 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777214 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777214, (1 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second-stage product in the stored Table 1.3 trace:
`fl32((14073747/2^47)*9999999)` rounds down to `4194303/4194304`. -/
theorem hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (14073747 / (2 : ℝ) ^ 47) (9999999 : ℝ) =
      4194303 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 16777212 (0 : ℤ)
  let b : ℝ := fmt.normalizedValue false 16777213 (0 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.mul
    (14073747 / (2 : ℝ) ^ 47) (9999999 : ℝ)
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (16777212 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 16777212, (0 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (4194303 : ℝ) / 4194304 := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (16777213 : ℝ) / 16777216 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (140737455926253 : ℝ) / 140737488355328 := by
    norm_num [x, BasicOp.exact]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (140737455926253 : ℝ) / 140737488355328 ≤ 1 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (1 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven x = (4194303 : ℝ) / 4194304
  simpa [x, fmt, ha_value] using hround

/-- The second-stage diagonal subtraction `fl32(1 - 4194303/4194304)` is exact. -/
theorem hessenbergDetExampleTable13_round_one_sub_secondStageProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (1 : ℝ) (4194303 / 4194304 : ℝ) =
      1 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (1 : ℝ) (4194303 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (1 : ℝ)) (y := (4194303 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The second-stage superdiagonal subtraction
`fl32((-1) - 4194303/4194304)` is exact. -/
theorem hessenbergDetExampleTable13_round_neg_one_sub_secondStageProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1 : ℝ) (4194303 / 4194304 : ℝ) =
      -8388607 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-1 : ℝ) (4194303 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-1 : ℝ)) (y := (4194303 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- Fully nested primitive binary32 trace for the second-stage diagonal update
`(2,2)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_secondStage_diag22_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 2 2)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 2 1)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 1 1)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 1 0)
                  (hessenbergDetExampleTable13StoredMatrix 0 0))
                (hessenbergDetExampleTable13StoredMatrix 0 1))))
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
            (hessenbergDetExampleTable13StoredMatrix 1 2)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                (hessenbergDetExampleTable13StoredMatrix 1 0)
                (hessenbergDetExampleTable13StoredMatrix 0 0))
              (hessenbergDetExampleTable13StoredMatrix 0 2)))) =
      1 / 4194304 := by
  rw [hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredMatrix_firstStage_super12_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper,
    hessenbergDetExampleTable13_round_one_sub_secondStageProduct]

/-- Fully nested primitive binary32 trace for the second-stage superdiagonal
update `(2,3)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_secondStage_super23_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 2 3)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 2 1)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 1 1)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 1 0)
                  (hessenbergDetExampleTable13StoredMatrix 0 0))
                (hessenbergDetExampleTable13StoredMatrix 0 1))))
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
            (hessenbergDetExampleTable13StoredMatrix 1 3)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                (hessenbergDetExampleTable13StoredMatrix 1 0)
                (hessenbergDetExampleTable13StoredMatrix 0 0))
              (hessenbergDetExampleTable13StoredMatrix 0 3)))) =
      -8388607 / 4194304 := by
  rw [hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredMatrix_firstStage_super13_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper,
    hessenbergDetExampleTable13_round_neg_one_sub_secondStageProduct]

/-- The final multiplier value `4194304 = 2^22` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_thirdMultiplier_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388608 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (23 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388608, (23 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  rfl

/-- The final-stage product value `-8388607` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_thirdStageProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-8388607 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777214 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (23 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777214, (23 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The final diagonal value `8388608 = 2^23` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_finalDiag_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (8388608 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388608 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (24 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388608, (24 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The final no-pivot multiplier division is exact:
`fl32(1/(1/4194304)) = 4194304`. -/
theorem hessenbergDetExampleTable13_round_one_div_secondStageDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (1 / 4194304 : ℝ) =
      4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (1 : ℝ) (1 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_thirdMultiplier_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (1 : ℝ)) (y := (1 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The final-stage product `fl32(4194304*(-8388607/4194304))` is exact. -/
theorem hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageSuper :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (4194304 : ℝ) (-8388607 / 4194304 : ℝ) =
      -8388607 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (4194304 : ℝ) (-8388607 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_thirdStageProduct_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (4194304 : ℝ)) (y := (-8388607 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The final diagonal subtraction `fl32(1 - (-8388607))` is exact. -/
theorem hessenbergDetExampleTable13_round_one_sub_thirdStageProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (1 : ℝ) (-8388607 : ℝ) =
      8388608 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (1 : ℝ) (-8388607 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_finalDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (1 : ℝ)) (y := (-8388607 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- Fully nested primitive binary32 trace for the final no-pivot multiplier
division from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_thirdMultiplier_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (hessenbergDetExampleTable13StoredMatrix 3 2)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
          (hessenbergDetExampleTable13StoredMatrix 2 2)
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
              (hessenbergDetExampleTable13StoredMatrix 2 1)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                (hessenbergDetExampleTable13StoredMatrix 1 1)
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                    (hessenbergDetExampleTable13StoredMatrix 1 0)
                    (hessenbergDetExampleTable13StoredMatrix 0 0))
                  (hessenbergDetExampleTable13StoredMatrix 0 1))))
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 1 2)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 1 0)
                  (hessenbergDetExampleTable13StoredMatrix 0 0))
                (hessenbergDetExampleTable13StoredMatrix 0 2))))) =
      4194304 := by
  rw [hessenbergDetExampleTable13StoredMatrix_secondStage_diag22_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simpa [hessenbergDetExampleMatrix] using
    hessenbergDetExampleTable13_round_one_div_secondStageDiag

/-- Fully nested primitive binary32 trace for the final diagonal update `(3,3)`
from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_finalDiag_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 3 3)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 3 2)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 2 2)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 2 1)
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                    (hessenbergDetExampleTable13StoredMatrix 1 1)
                    (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                      (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                        (hessenbergDetExampleTable13StoredMatrix 1 0)
                        (hessenbergDetExampleTable13StoredMatrix 0 0))
                      (hessenbergDetExampleTable13StoredMatrix 0 1))))
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                  (hessenbergDetExampleTable13StoredMatrix 1 2)
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                    (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                      (hessenbergDetExampleTable13StoredMatrix 1 0)
                      (hessenbergDetExampleTable13StoredMatrix 0 0))
                    (hessenbergDetExampleTable13StoredMatrix 0 2))))))
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
            (hessenbergDetExampleTable13StoredMatrix 2 3)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                (hessenbergDetExampleTable13StoredMatrix 2 1)
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                  (hessenbergDetExampleTable13StoredMatrix 1 1)
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                    (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                      (hessenbergDetExampleTable13StoredMatrix 1 0)
                      (hessenbergDetExampleTable13StoredMatrix 0 0))
                    (hessenbergDetExampleTable13StoredMatrix 0 1))))
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                (hessenbergDetExampleTable13StoredMatrix 1 3)
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                    (hessenbergDetExampleTable13StoredMatrix 1 0)
                    (hessenbergDetExampleTable13StoredMatrix 0 0))
                  (hessenbergDetExampleTable13StoredMatrix 0 3)))))) =
      8388608 := by
  rw [hessenbergDetExampleTable13StoredMatrix_thirdMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredMatrix_secondStage_super23_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageSuper,
    hessenbergDetExampleTable13_round_one_sub_thirdStageProduct]

/-- The first left-to-right determinant product prefix is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_detProduct01_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (8388609 / 8388608 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388609 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388609, (1 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second left-to-right determinant product prefix is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_detProduct012_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (8388609 / (2 : ℝ) ^ 45) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388609 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-21 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388609, (-21 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The final left-to-right determinant product value is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_detProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (8388609 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388609 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (2 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388609, (2 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- First left-to-right determinant product from the closed Table 1.3 no-pivot
diagonal trace: `fl32(fl32(alpha)*10000001)=8388609/8388608`. -/
theorem hessenbergDetExampleTable13_round_storedAlpha_mul_firstStageDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        hessenbergDetExampleTable13StoredAlpha (10000001 : ℝ) =
      8388609 / 8388608 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 8388608 (1 : ℤ)
  let b : ℝ := fmt.normalizedValue false 8388609 (1 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.mul
    hessenbergDetExampleTable13StoredAlpha (10000001 : ℝ)
  have hm : fmt.normalizedMantissa 8388608 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (8388608 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 8388608, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 : ℝ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
    rfl
  have hb_value : b = (8388609 : ℝ) / 8388608 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (140737504073749 : ℝ) / 140737488355328 := by
    norm_num [x, BasicOp.exact, hessenbergDetExampleTable13StoredAlpha_eq]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (140737504073749 : ℝ) / 140737488355328 ≤ 2 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (2 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change fmt.finiteRoundToEven x = (8388609 : ℝ) / 8388608
  simpa [x, fmt, hb_value] using hround

/-- The second left-to-right determinant product is exact after the first
rounded product prefix. -/
theorem hessenbergDetExampleTable13_round_detProduct01_mul_secondStageDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (8388609 / 8388608 : ℝ) (1 / 4194304 : ℝ) =
      8388609 / (2 : ℝ) ^ 45 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (8388609 / 8388608 : ℝ)
          (1 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_detProduct012_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (8388609 / 8388608 : ℝ))
      (y := (1 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The final left-to-right determinant product is exact after the second
product prefix. -/
theorem hessenbergDetExampleTable13_round_detProduct012_mul_finalDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (8388609 / (2 : ℝ) ^ 45) (8388608 : ℝ) =
      8388609 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (8388609 / (2 : ℝ) ^ 45) (8388608 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_detProduct_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (8388609 / (2 : ℝ) ^ 45))
      (y := (8388608 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The left-to-right product of the closed Table 1.3 computed diagonal trace
gives the concrete primitive computed determinant value. -/
theorem hessenbergDetExampleTable13_detProduct_leftToRight_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
            hessenbergDetExampleTable13StoredAlpha (10000001 : ℝ))
          (1 / 4194304 : ℝ))
        (8388608 : ℝ) =
      8388609 / 4194304 := by
  rw [hessenbergDetExampleTable13_round_storedAlpha_mul_firstStageDiag]
  rw [hessenbergDetExampleTable13_round_detProduct01_mul_secondStageDiag]
  exact hessenbergDetExampleTable13_round_detProduct012_mul_finalDiag

/-- Exact relative determinant error of the primitive left-to-right Table 1.3
determinant product against the source-value determinant. -/
theorem hessenbergDetExampleTable13_detProduct_relError_eq :
    relError (8388609 / 4194304 : ℝ)
        (Matrix.det
          (hessenbergDetExampleMatrix (1 / 10000000 : ℝ) :
            Matrix (Fin 4) (Fin 4) ℝ)) =
      12589 / 655360065536 := by
  rw [hessenbergDetExampleMatrix_alpha_ten_pow_det_eq]
  norm_num [relError]

/-- Binary32 storage of the Table 1.3 right-hand side keeps the exactly
representable `0`, `1`, and `2` entries fixed while exposing the rounded
`alpha - 3` source entry. -/
theorem hessenbergDetExampleTable13_storedRhs_rows :
    hessenbergDetExampleTable13StoredRhs 0 =
        hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
          (hessenbergDetExampleTable13SourceAlpha - 3) ∧
      hessenbergDetExampleTable13StoredRhs 1 = 0 ∧
      hessenbergDetExampleTable13StoredRhs 2 = 1 ∧
      hessenbergDetExampleTable13StoredRhs 3 = 2 := by
  constructor
  · rfl
  constructor
  · simp [hessenbergDetExampleTable13StoredRhs, hessenbergDetExampleRhs]
  constructor
  · simp [hessenbergDetExampleTable13StoredRhs, hessenbergDetExampleRhs]
  · simp [hessenbergDetExampleTable13StoredRhs, hessenbergDetExampleRhs]

/-- The stored first right-hand-side entry `fl32(alpha-3)` rounds to `-3` in
the Table 1.3 binary32 model. -/
theorem hessenbergDetExampleTable13_round_sourceAlpha_sub_three :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
        (hessenbergDetExampleTable13SourceAlpha - 3) =
      -3 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue true 12582912 (2 : ℤ)
  let b : ℝ := fmt.normalizedValue true 12582911 (2 : ℤ)
  let x : ℝ := hessenbergDetExampleTable13SourceAlpha - 3
  have hm : fmt.normalizedMantissa 12582911 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (12582911 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨true, 12582911, (2 : ℤ), hm, hmnext, Or.inr ⟨rfl, rfl⟩⟩
  have ha_value : a = (-3 : ℝ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = -(12582911 : ℝ) / 4194304 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = -(29999999 : ℝ) / 10000000 := by
    norm_num [x, hessenbergDetExampleTable13SourceAlpha]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_neg (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        -(-(29999999 : ℝ) / 10000000) ≤ 3 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (3 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven x = (-3 : ℝ)
  simpa [x, fmt, ha_value] using hround

/-- The first stored right-hand-side entry is the concrete binary32 value `-3`. -/
theorem hessenbergDetExampleTable13StoredRhs0_eq_neg_three :
    hessenbergDetExampleTable13StoredRhs 0 = -3 := by
  have hrows := hessenbergDetExampleTable13_storedRhs_rows
  rw [hrows.1]
  exact hessenbergDetExampleTable13_round_sourceAlpha_sub_three

/-- The first RHS product `fl32(10^7*(-3))` is exact. -/
theorem hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_three :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        ((10 : ℝ) ^ 7) (-3) =
      -30000000 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul ((10 : ℝ) ^ 7) (-3 : ℝ)) := by
    have hm : fmt.normalizedMantissa 15000000 := by
      norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa]
    have he : fmt.exponentInRange (25 : ℤ) := by
      norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    refine Or.inr (Or.inl ⟨true, 15000000, (25 : ℤ), hm, he, ?_⟩)
    norm_num [BasicOp.exact, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := ((10 : ℝ) ^ 7)) (y := (-3 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The first RHS subtraction `fl32(0 - (-30000000))` is exact. -/
theorem hessenbergDetExampleTable13_round_zero_sub_neg_thirty_million :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (0 : ℝ) (-30000000 : ℝ) =
      30000000 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (0 : ℝ) (-30000000 : ℝ)) := by
    have hm : fmt.normalizedMantissa 15000000 := by
      norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa]
    have he : fmt.exponentInRange (25 : ℤ) := by
      norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    refine Or.inr (Or.inl ⟨false, 15000000, (25 : ℤ), hm, he, ?_⟩)
    norm_num [BasicOp.exact, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (0 : ℝ)) (y := (-30000000 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- Fully nested primitive binary32 trace for the first RHS elimination update
from the stored Table 1.3 system. -/
theorem hessenbergDetExampleTable13StoredRhs_firstStage_rhs1_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredRhs 1)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 1 0)
            (hessenbergDetExampleTable13StoredMatrix 0 0))
          (hessenbergDetExampleTable13StoredRhs 0)) =
      30000000 := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven]
  rw [hessenbergDetExampleTable13StoredRhs0_eq_neg_three]
  have hrows := hessenbergDetExampleTable13_storedRhs_rows
  rw [hrows.2.1]
  simp [hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_three,
    hessenbergDetExampleTable13_round_zero_sub_neg_thirty_million]

/-- The second RHS product value `6291455/2097152` is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondRhsProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (6291455 / 2097152 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 12582910 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (2 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 12582910, (2 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second updated RHS value `-4194303/2097152` is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondStageRhs_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-4194303 / 2097152 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777212, (1 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The final RHS product value `-8388606` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_thirdRhsProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-8388606 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (23 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777212, (23 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second RHS product in the stored Table 1.3 trace:
`fl32((14073747/2^47)*30000000)` rounds to `6291455/2097152`. -/
theorem hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageRhs :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (14073747 / (2 : ℝ) ^ 47) (30000000 : ℝ) =
      6291455 / 2097152 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 12582910 (2 : ℤ)
  let b : ℝ := fmt.normalizedValue false 12582911 (2 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.mul
    (14073747 / (2 : ℝ) ^ 47) (30000000 : ℝ)
  have hm : fmt.normalizedMantissa 12582910 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (12582910 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 12582910, (2 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (6291455 : ℝ) / 2097152 := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (12582911 : ℝ) / 4194304 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (3298534453125 : ℝ) / 1099511627776 := by
    norm_num [x, BasicOp.exact]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (3298534453125 : ℝ) / 1099511627776 ≤ 3 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (3 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven x = (6291455 : ℝ) / 2097152
  simpa [x, fmt, ha_value] using hround

/-- The second RHS subtraction `fl32(1 - 6291455/2097152)` is exact. -/
theorem hessenbergDetExampleTable13_round_one_sub_secondRhsProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (1 : ℝ) (6291455 / 2097152 : ℝ) =
      -4194303 / 2097152 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (1 : ℝ) (6291455 / 2097152 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageRhs_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (1 : ℝ))
      (y := (6291455 / 2097152 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- Fully nested primitive binary32 trace for the second RHS elimination update
from the stored Table 1.3 system. -/
theorem hessenbergDetExampleTable13StoredRhs_secondStage_rhs2_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredRhs 2)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 2 1)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 1 1)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 1 0)
                  (hessenbergDetExampleTable13StoredMatrix 0 0))
                (hessenbergDetExampleTable13StoredMatrix 0 1))))
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
            (hessenbergDetExampleTable13StoredRhs 1)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                (hessenbergDetExampleTable13StoredMatrix 1 0)
                (hessenbergDetExampleTable13StoredMatrix 0 0))
              (hessenbergDetExampleTable13StoredRhs 0)))) =
      -4194303 / 2097152 := by
  rw [hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredRhs_firstStage_rhs1_rounds_to]
  have hrows := hessenbergDetExampleTable13_storedRhs_rows
  rw [hrows.2.2.1]
  simp [hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageRhs,
    hessenbergDetExampleTable13_round_one_sub_secondRhsProduct]

/-- The final RHS product `fl32(4194304*(-4194303/2097152))` is exact. -/
theorem hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageRhs :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (4194304 : ℝ) (-4194303 / 2097152 : ℝ) =
      -8388606 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (4194304 : ℝ)
          (-4194303 / 2097152 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_thirdRhsProduct_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (4194304 : ℝ))
      (y := (-4194303 / 2097152 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The final RHS subtraction `fl32(2 - (-8388606))` is exact. -/
theorem hessenbergDetExampleTable13_round_two_sub_thirdRhsProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (2 : ℝ) (-8388606 : ℝ) =
      8388608 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (2 : ℝ) (-8388606 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_finalDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (2 : ℝ)) (y := (-8388606 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- Fully nested primitive binary32 trace for the final RHS elimination update
from the stored Table 1.3 system. -/
theorem hessenbergDetExampleTable13StoredRhs_finalStage_rhs3_rounds_to :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let d1 := fmt.finiteRoundToEvenOp BasicOp.sub
      (hessenbergDetExampleTable13StoredMatrix 1 1)
      (fmt.finiteRoundToEvenOp BasicOp.mul
        (fmt.finiteRoundToEvenOp BasicOp.div
          (hessenbergDetExampleTable13StoredMatrix 1 0)
          (hessenbergDetExampleTable13StoredMatrix 0 0))
        (hessenbergDetExampleTable13StoredMatrix 0 1))
    let m2 := fmt.finiteRoundToEvenOp BasicOp.div
      (hessenbergDetExampleTable13StoredMatrix 2 1) d1
    let u22 := fmt.finiteRoundToEvenOp BasicOp.sub
      (hessenbergDetExampleTable13StoredMatrix 2 2)
      (fmt.finiteRoundToEvenOp BasicOp.mul m2
        (fmt.finiteRoundToEvenOp BasicOp.sub
          (hessenbergDetExampleTable13StoredMatrix 1 2)
          (fmt.finiteRoundToEvenOp BasicOp.mul
            (fmt.finiteRoundToEvenOp BasicOp.div
              (hessenbergDetExampleTable13StoredMatrix 1 0)
              (hessenbergDetExampleTable13StoredMatrix 0 0))
            (hessenbergDetExampleTable13StoredMatrix 0 2))))
    let m3 := fmt.finiteRoundToEvenOp BasicOp.div
      (hessenbergDetExampleTable13StoredMatrix 3 2) u22
    let rhs1 := fmt.finiteRoundToEvenOp BasicOp.sub
      (hessenbergDetExampleTable13StoredRhs 1)
      (fmt.finiteRoundToEvenOp BasicOp.mul
        (fmt.finiteRoundToEvenOp BasicOp.div
          (hessenbergDetExampleTable13StoredMatrix 1 0)
          (hessenbergDetExampleTable13StoredMatrix 0 0))
        (hessenbergDetExampleTable13StoredRhs 0))
    let rhs2 := fmt.finiteRoundToEvenOp BasicOp.sub
      (hessenbergDetExampleTable13StoredRhs 2)
      (fmt.finiteRoundToEvenOp BasicOp.mul m2 rhs1)
    fmt.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredRhs 3)
        (fmt.finiteRoundToEvenOp BasicOp.mul m3 rhs2) =
      8388608 := by
  dsimp only
  rw [hessenbergDetExampleTable13StoredMatrix_thirdMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredRhs_secondStage_rhs2_rounds_to]
  have hrows := hessenbergDetExampleTable13_storedRhs_rows
  rw [hrows.2.2.2]
  simp [hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageRhs,
    hessenbergDetExampleTable13_round_two_sub_thirdRhsProduct]

/-- The row-3 back-substitution division is exact:
`fl32(8388608/8388608)=1`. -/
theorem hessenbergDetExampleTable13_backSub_x3_rounds_to_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (8388608 : ℝ) (8388608 : ℝ) =
      1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (8388608 : ℝ) (8388608 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_one_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (8388608 : ℝ)) (y := (8388608 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The row-2 back-substitution product by the computed `x_3=1` is exact. -/
theorem hessenbergDetExampleTable13_backSub_row2_product_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (-8388607 / 4194304 : ℝ) 1 =
      -8388607 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (-8388607 / 4194304 : ℝ) (1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (-8388607 / 4194304 : ℝ)) (y := (1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The row-2 back-substitution subtraction recovers the tiny pivot
`1/4194304`. -/
theorem hessenbergDetExampleTable13_backSub_row2_sub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-4194303 / 2097152 : ℝ) (-8388607 / 4194304 : ℝ) =
      1 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-4194303 / 2097152 : ℝ)
          (-8388607 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-4194303 / 2097152 : ℝ))
      (y := (-8388607 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The row-2 back-substitution division gives `x_2=1`. -/
theorem hessenbergDetExampleTable13_backSub_x2_rounds_to_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
          (-4194303 / 2097152 : ℝ)
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
            (-8388607 / 4194304 : ℝ)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
              (8388608 : ℝ) (8388608 : ℝ))))
        (1 / 4194304 : ℝ) =
      1 := by
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_row2_product_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row2_sub_rounds_to]
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (1 / 4194304 : ℝ) (1 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_one_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (1 / 4194304 : ℝ)) (y := (1 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The row-1 first back-substitution product `fl32(9999999*1)` is exact. -/
theorem hessenbergDetExampleTable13_backSub_row1_product_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (9999999 : ℝ) 1 =
      9999999 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (9999999 : ℝ) (1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_firstStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (9999999 : ℝ)) (y := (1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The row-1 first back-substitution subtraction is a tie and nearest/even
rounds `30000000 - 9999999 = 20000001` to `20000000`. -/
theorem hessenbergDetExampleTable13_backSub_row1_firstSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (30000000 : ℝ) (9999999 : ℝ) =
      20000000 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 10000000 (25 : ℤ)
  let b : ℝ := fmt.normalizedValue false 10000001 (25 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.sub (30000000 : ℝ) (9999999 : ℝ)
  have hm : fmt.normalizedMantissa 10000000 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (10000000 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 10000000, (25 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (20000000 : ℝ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (20000002 : ℝ) := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (20000001 : ℝ) := by
    norm_num [x, BasicOp.exact]
    rfl
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (20000001 : ℝ) ≤ 30000000 := by norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (30000000 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 10000000 (25 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have heven : FloatingPointFormat.evenMantissa 10000000 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  change fmt.finiteRoundToEven x = (20000000 : ℝ)
  simpa [x, fmt, ha_value] using hround

/-- The row-1 second back-substitution subtraction is exact after the
tie-to-even first subtraction. -/
theorem hessenbergDetExampleTable13_backSub_row1_secondSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (20000000 : ℝ) (9999999 : ℝ) =
      10000001 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (20000000 : ℝ) (9999999 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_firstStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (20000000 : ℝ)) (y := (9999999 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The row-1 back-substitution division gives `x_1=1`. -/
theorem hessenbergDetExampleTable13_backSub_x1_rounds_to_one :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ) =
      1 := by
  dsimp only
  rw [hessenbergDetExampleTable13_backSub_x2_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_row1_product_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row1_firstSub_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row1_secondSub_rounds_to]
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (10000001 : ℝ) (10000001 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_one_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (10000001 : ℝ)) (y := (10000001 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The row-0 product `fl32((-1)*1)` used in back substitution is exact. -/
theorem hessenbergDetExampleTable13_backSub_row0_product_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (-1 : ℝ) 1 =
      -1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (-1 : ℝ) (1 : ℝ)) := by
    have hneg :
        fmt.finiteSystem (-(1 : ℝ)) :=
      fmt.finiteSystem_neg hessenbergDetExampleTable13IeeeSingle_one_finiteSystem
    convert hneg using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (-1 : ℝ)) (y := (1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The first row-0 back-substitution subtraction gives `-2`. -/
theorem hessenbergDetExampleTable13_backSub_row0_firstSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-3 : ℝ) (-1 : ℝ) =
      -2 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-3 : ℝ) (-1 : ℝ)) := by
    have hneg :
        fmt.finiteSystem (-(2 : ℝ)) :=
      fmt.finiteSystem_neg hessenbergDetExampleTable13IeeeSingle_two_finiteSystem
    convert hneg using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-3 : ℝ)) (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The second row-0 back-substitution subtraction gives `-1`. -/
theorem hessenbergDetExampleTable13_backSub_row0_secondSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-2 : ℝ) (-1 : ℝ) =
      -1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-2 : ℝ) (-1 : ℝ)) := by
    have hneg :
        fmt.finiteSystem (-(1 : ℝ)) :=
      fmt.finiteSystem_neg hessenbergDetExampleTable13IeeeSingle_one_finiteSystem
    convert hneg using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-2 : ℝ)) (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The third row-0 back-substitution subtraction gives zero. -/
theorem hessenbergDetExampleTable13_backSub_row0_thirdSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1 : ℝ) (-1 : ℝ) =
      0 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-1 : ℝ) (-1 : ℝ)) := by
    convert fmt.finiteSystem_zero using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-1 : ℝ)) (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The final row-0 back-substitution division gives `x_0=0` under the explicit
binary32 trace. -/
theorem hessenbergDetExampleTable13_backSub_x0_rounds_to_zero :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    let x1 := fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ)
    let r1 := fmt.finiteRoundToEvenOp BasicOp.sub (-3 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x1)
    let r2 := fmt.finiteRoundToEvenOp BasicOp.sub r1
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x2)
    let r3 := fmt.finiteRoundToEvenOp BasicOp.sub r2
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x3)
    fmt.finiteRoundToEvenOp BasicOp.div r3 hessenbergDetExampleTable13StoredAlpha =
      0 := by
  dsimp only
  rw [hessenbergDetExampleTable13_backSub_x1_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x2_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_row0_product_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row0_firstSub_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row0_secondSub_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row0_thirdSub_rounds_to]
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (0 : ℝ) hessenbergDetExampleTable13StoredAlpha) := by
    convert fmt.finiteSystem_zero using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (0 : ℝ))
      (y := hessenbergDetExampleTable13StoredAlpha) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The standard nearest/even binary32 back-substitution trace for the stored
Table 1.3 triangular system gives `[0,1,1,1]^T`. -/
theorem hessenbergDetExampleTable13_standardBackSubSolution_rows :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    let x1 := fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ)
    let r1 := fmt.finiteRoundToEvenOp BasicOp.sub (-3 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x1)
    let r2 := fmt.finiteRoundToEvenOp BasicOp.sub r1
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x2)
    let r3 := fmt.finiteRoundToEvenOp BasicOp.sub r2
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x3)
    let x0 := fmt.finiteRoundToEvenOp BasicOp.div r3 hessenbergDetExampleTable13StoredAlpha
    x0 = 0 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 := by
  dsimp only
  rw [hessenbergDetExampleTable13_backSub_x0_rounds_to_zero]
  rw [hessenbergDetExampleTable13_backSub_x1_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x2_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  simp

/-- The displayed computed solution vector in Higham Table 1.3, encoded as
exact rationals.  This records the printed table entries; it is not yet a
primitive-operation reconstruction of the hidden single-precision GE trace. -/
noncomputable def hessenbergDetExampleTable13ComputedSolution :
    Fin 4 → ℝ
  | ⟨0, _⟩ => 23842 / (10 : ℝ) ^ 4
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1

/-- The displayed relative solution error in Higham Table 1.3. -/
noncomputable def hessenbergDetExampleTable13SolutionRelativeError : ℝ :=
  13842 / (10 : ℝ) ^ 4

/-- The five-significant-figure exact determinant display in Higham Table 1.3. -/
noncomputable def hessenbergDetExampleTable13ExactDetDisplay : ℝ :=
  2

/-- The five-significant-figure computed determinant display in Higham Table 1.3. -/
noncomputable def hessenbergDetExampleTable13ComputedDetDisplay : ℝ :=
  2

/-- The displayed determinant relative error in Higham Table 1.3.  The exact
and computed determinant entries are printed only to five significant figures,
so this is a table datum rather than the relative error of the rounded display
`2.0000` against the exact rational determinant. -/
noncomputable def hessenbergDetExampleTable13DetRelativeError : ℝ :=
  19209 / (10 : ℝ) ^ 12

/-- The standard nearest/even binary32 back-substitution trace cannot be the
printed Table 1.3 solution row, whose first component is `2.3842`. -/
theorem hessenbergDetExampleTable13_standardBackSub_first_component_ne_printed :
    (0 : ℝ) ≠ hessenbergDetExampleTable13ComputedSolution 0 := by
  norm_num [hessenbergDetExampleTable13ComputedSolution]

/-- The adjacent binary32 value immediately above `-3` that would be obtained
by rounding the first RHS entry toward zero rather than by nearest/even storage
of the exact source value `alpha - 3`. -/
noncomputable def hessenbergDetExampleTable13AltStoredRhs0 : ℝ :=
  -12582911 / 4194304

/-- The alternate first RHS value is a finite binary32 number. -/
theorem hessenbergDetExampleTable13AltStoredRhs0_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      hessenbergDetExampleTable13AltStoredRhs0 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 12582911 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (2 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 12582911, (2 : ℤ), hm, he, ?_⟩)
  norm_num [hessenbergDetExampleTable13AltStoredRhs0, fmt,
    hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The alternate first RHS value is strictly above `-3`, matching the
one-step-toward-zero binary32 neighbor. -/
theorem hessenbergDetExampleTable13AltStoredRhs0_gt_neg_three :
    (-3 : ℝ) < hessenbergDetExampleTable13AltStoredRhs0 := by
  norm_num [hessenbergDetExampleTable13AltStoredRhs0]

/-- The alternate first RHS value is exactly the normalized binary32 neighbor
with mantissa `12582911` and exponent `2`. -/
theorem hessenbergDetExampleTable13AltStoredRhs0_eq_normalizedValue :
    hessenbergDetExampleTable13AltStoredRhs0 =
      hessenbergDetExampleTable13IeeeSingleFormat.normalizedValue
        true 12582911 (2 : ℤ) := by
  norm_num [hessenbergDetExampleTable13AltStoredRhs0,
    hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The alternate first RHS value is the immediate binary32 neighbor above
`-3`; this isolates the hidden one-step-toward-zero convention needed to obtain
the printed Table 1.3 first component by the standard back-substitution path. -/
theorem hessenbergDetExampleTable13_neg_three_altStoredRhs0_adjacent :
    hessenbergDetExampleTable13IeeeSingleFormat.realOrderAdjacentNormalized
      (-3 : ℝ) hessenbergDetExampleTable13AltStoredRhs0 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 12582911 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (12582911 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized
      (fmt.normalizedValue true 12582912 (2 : ℤ))
      (fmt.normalizedValue true 12582911 (2 : ℤ)) :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨true, 12582911, (2 : ℤ), hm, hmnext, Or.inr ⟨rfl, rfl⟩⟩
  have hleft : fmt.normalizedValue true 12582912 (2 : ℤ) = (-3 : ℝ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hright : fmt.normalizedValue true 12582911 (2 : ℤ) =
      hessenbergDetExampleTable13AltStoredRhs0 := by
    rw [hessenbergDetExampleTable13AltStoredRhs0_eq_normalizedValue]
  simpa [fmt, hleft, hright] using hadj

/-- The actual nearest/even stored first RHS entry is strictly below the
alternate adjacent value that reproduces the printed Table 1.3 first component. -/
theorem hessenbergDetExampleTable13StoredRhs0_lt_altStoredRhs0 :
    hessenbergDetExampleTable13StoredRhs 0 <
      hessenbergDetExampleTable13AltStoredRhs0 := by
  rw [hessenbergDetExampleTable13StoredRhs0_eq_neg_three]
  exact hessenbergDetExampleTable13AltStoredRhs0_gt_neg_three

/-- Consequently the alternate-RHS diagnostic is not the same as ordinary
nearest/even storage of the source right-hand side. -/
theorem hessenbergDetExampleTable13StoredRhs0_ne_altStoredRhs0 :
    hessenbergDetExampleTable13StoredRhs 0 ≠
      hessenbergDetExampleTable13AltStoredRhs0 :=
  ne_of_lt hessenbergDetExampleTable13StoredRhs0_lt_altStoredRhs0

/-- The intermediate alternate row-0 value `-4194303/4194304` is representable
in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_altRow0SecondSub_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-4194303 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (0 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777212, (0 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- With the alternate first RHS value, the first row-0 subtraction gives the
binary32 neighbor `-8388607/4194304` exactly. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_row0_firstSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        hessenbergDetExampleTable13AltStoredRhs0 (-1 : ℝ) =
      -8388607 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub hessenbergDetExampleTable13AltStoredRhs0
          (-1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact, hessenbergDetExampleTable13AltStoredRhs0]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := hessenbergDetExampleTable13AltStoredRhs0)
      (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact, hessenbergDetExampleTable13AltStoredRhs0]

/-- With the alternate first RHS value, the second row-0 subtraction gives
`-4194303/4194304` exactly. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_row0_secondSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-8388607 / 4194304 : ℝ) (-1 : ℝ) =
      -4194303 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-8388607 / 4194304 : ℝ) (-1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_altRow0SecondSub_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-8388607 / 4194304 : ℝ))
      (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- With the alternate first RHS value, the third row-0 subtraction leaves the
small binary32 value `1/4194304`. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_row0_thirdSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-4194303 / 4194304 : ℝ) (-1 : ℝ) =
      1 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-4194303 / 4194304 : ℝ) (-1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-4194303 / 4194304 : ℝ))
      (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The alternate row-0 numerator divided by the stored first pivot rounds to
the binary32 value whose decimal display is `2.3842`. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_row0_div_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 / 4194304 : ℝ) hessenbergDetExampleTable13StoredAlpha =
      78125 / 32768 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 9999999 (2 : ℤ)
  let b : ℝ := fmt.normalizedValue false 10000000 (2 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.div (1 / 4194304 : ℝ)
    hessenbergDetExampleTable13StoredAlpha
  have hm : fmt.normalizedMantissa 9999999 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (9999999 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 9999999, (2 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (9999999 : ℝ) / 4194304 := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (78125 : ℝ) / 32768 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (33554432 : ℝ) / 14073749 := by
    norm_num [x, BasicOp.exact, hessenbergDetExampleTable13StoredAlpha_eq]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.betaR, zpow_neg]
    · calc
        (33554432 : ℝ) / 14073749 ≤ 3 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (3 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change fmt.finiteRoundToEven x = (78125 : ℝ) / 32768
  simpa [x, fmt, hb_value] using hround

/-- If only the first stored RHS entry is replaced by the adjacent binary32
value above `-3`, the same standard back-substitution trace returns the
binary32 first component that prints as the Table 1.3 value. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_x0_rounds_to_printed_float :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    let x1 := fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ)
    let r1 := fmt.finiteRoundToEvenOp BasicOp.sub
      hessenbergDetExampleTable13AltStoredRhs0
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x1)
    let r2 := fmt.finiteRoundToEvenOp BasicOp.sub r1
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x2)
    let r3 := fmt.finiteRoundToEvenOp BasicOp.sub r2
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x3)
    fmt.finiteRoundToEvenOp BasicOp.div r3 hessenbergDetExampleTable13StoredAlpha =
      78125 / 32768 := by
  dsimp only
  rw [hessenbergDetExampleTable13_backSub_x1_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x2_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_row0_product_rounds_to]
  rw [hessenbergDetExampleTable13_altRhsBackSub_row0_firstSub_rounds_to]
  rw [hessenbergDetExampleTable13_altRhsBackSub_row0_secondSub_rounds_to]
  rw [hessenbergDetExampleTable13_altRhsBackSub_row0_thirdSub_rounds_to]
  exact hessenbergDetExampleTable13_altRhsBackSub_row0_div_rounds_to

/-- The alternate-RHS back-substitution first component is within half a unit in
the fifth displayed decimal place of the printed Table 1.3 value `2.3842`. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_first_component_matches_printed :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    let x1 := fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ)
    let r1 := fmt.finiteRoundToEvenOp BasicOp.sub
      hessenbergDetExampleTable13AltStoredRhs0
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x1)
    let r2 := fmt.finiteRoundToEvenOp BasicOp.sub r1
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x2)
    let r3 := fmt.finiteRoundToEvenOp BasicOp.sub r2
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x3)
    |fmt.finiteRoundToEvenOp BasicOp.div r3 hessenbergDetExampleTable13StoredAlpha -
        hessenbergDetExampleTable13ComputedSolution 0| <
      1 / (2 * (10 : ℝ) ^ 4) := by
  dsimp only
  rw [hessenbergDetExampleTable13_altRhsBackSub_x0_rounds_to_printed_float]
  norm_num [hessenbergDetExampleTable13ComputedSolution]

/-- Exact rational transcription of the displayed computed solution vector in
Table 1.3. -/
theorem hessenbergDetExampleTable13_computedSolution_rows :
    hessenbergDetExampleTable13ComputedSolution 0 =
        23842 / (10 : ℝ) ^ 4 ∧
    hessenbergDetExampleTable13ComputedSolution 1 = 1 ∧
    hessenbergDetExampleTable13ComputedSolution 2 = 1 ∧
    hessenbergDetExampleTable13ComputedSolution 3 = 1 := by
  norm_num [hessenbergDetExampleTable13ComputedSolution]

/-- Exact rational transcription of the displayed exact solution vector in
Table 1.3. -/
theorem hessenbergDetExampleTable13_exactSolution_rows :
    hessenbergDetExampleOnes 0 = 1 ∧
    hessenbergDetExampleOnes 1 = 1 ∧
    hessenbergDetExampleOnes 2 = 1 ∧
    hessenbergDetExampleOnes 3 = 1 := by
  norm_num [hessenbergDetExampleOnes]

/-- Exact rational transcription of the determinant row in Table 1.3. -/
theorem hessenbergDetExampleTable13_det_rows :
    hessenbergDetExampleTable13ExactDetDisplay = 2 ∧
    hessenbergDetExampleTable13ComputedDetDisplay = 2 ∧
    hessenbergDetExampleTable13DetRelativeError =
      19209 / (10 : ℝ) ^ 12 := by
  norm_num [hessenbergDetExampleTable13ExactDetDisplay,
    hessenbergDetExampleTable13ComputedDetDisplay,
    hessenbergDetExampleTable13DetRelativeError]

/-- The primitive determinant product is close enough to the printed computed
determinant entry `2.0000` in Table 1.3. -/
theorem hessenbergDetExampleTable13_detProduct_computedDisplay_near :
    |(8388609 / 4194304 : ℝ) -
        hessenbergDetExampleTable13ComputedDetDisplay| <
      1 / (2 * (10 : ℝ) ^ 4) := by
  norm_num [hessenbergDetExampleTable13ComputedDetDisplay]

/-- The exact relative error of the primitive determinant product agrees with
the displayed Table 1.3 determinant-relative-error row to the printed decimal
precision. -/
theorem hessenbergDetExampleTable13_detProduct_relError_matches_display :
    |relError (8388609 / 4194304 : ℝ)
        (Matrix.det
          (hessenbergDetExampleMatrix (1 / 10000000 : ℝ) :
            Matrix (Fin 4) (Fin 4) ℝ)) -
        hessenbergDetExampleTable13DetRelativeError| <
      1 / (2 * (10 : ℝ) ^ 12) := by
  rw [hessenbergDetExampleTable13_detProduct_relError_eq]
  norm_num [hessenbergDetExampleTable13DetRelativeError]

/-- The exact solution vector in the Table 1.3 row has infinity norm one. -/
theorem hessenbergDetExampleTable13_exactSolution_infNorm_eq :
    infNormVec hessenbergDetExampleOnes = 1 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;> norm_num [hessenbergDetExampleOnes]
    · norm_num
  · have h := abs_le_infNormVec hessenbergDetExampleOnes (0 : Fin 4)
    norm_num [hessenbergDetExampleOnes] at h
    exact h

/-- The infinity norm of the displayed solution error vector in Table 1.3 is
the first-component error `1.3842`. -/
theorem hessenbergDetExampleTable13_solutionError_infNorm_eq :
    infNormVec
        (fun i => hessenbergDetExampleTable13ComputedSolution i -
          hessenbergDetExampleOnes i) =
      13842 / (10 : ℝ) ^ 4 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;>
        norm_num [hessenbergDetExampleTable13ComputedSolution,
          hessenbergDetExampleOnes]
    · norm_num
  · have h :=
      abs_le_infNormVec
        (fun i => hessenbergDetExampleTable13ComputedSolution i -
          hessenbergDetExampleOnes i) (0 : Fin 4)
    norm_num [hessenbergDetExampleTable13ComputedSolution,
      hessenbergDetExampleOnes] at h ⊢
    exact h

/-- The displayed computed solution has the Table 1.3 relative infinity-norm
error `1.3842` against the exact solution vector. -/
theorem hessenbergDetExampleTable13_solution_relative_error_eq :
    infNormVec
        (fun i => hessenbergDetExampleTable13ComputedSolution i -
          hessenbergDetExampleOnes i) /
        infNormVec hessenbergDetExampleOnes =
      hessenbergDetExampleTable13SolutionRelativeError := by
  rw [hessenbergDetExampleTable13_solutionError_infNorm_eq,
    hessenbergDetExampleTable13_exactSolution_infNorm_eq]
  norm_num [hessenbergDetExampleTable13SolutionRelativeError]

/-- Table 1.3's displayed computed solution has first-component absolute error
larger than one, formalizing the source's "no correct figures" observation at
the printed-data level. -/
theorem hessenbergDetExampleTable13_first_component_abs_error_gt_one :
    1 <
      |hessenbergDetExampleTable13ComputedSolution 0 -
        hessenbergDetExampleOnes 0| := by
  norm_num [hessenbergDetExampleTable13ComputedSolution,
    hessenbergDetExampleOnes]

/-- The displayed solution relative error in Table 1.3 is larger than one. -/
theorem hessenbergDetExampleTable13_solution_relative_error_gt_one :
    1 < hessenbergDetExampleTable13SolutionRelativeError := by
  norm_num [hessenbergDetExampleTable13SolutionRelativeError]

/-- The displayed determinant relative error in Table 1.3 is below `2e-8`,
capturing the table's "very accurate determinant" contrast. -/
theorem hessenbergDetExampleTable13_det_relative_error_lt_two_eight :
    hessenbergDetExampleTable13DetRelativeError < 2 / (10 : ℝ) ^ 8 := by
  norm_num [hessenbergDetExampleTable13DetRelativeError]

/-- The residual `b - A*xhat` obtained by inserting the displayed Table 1.3
computed solution into the exact source system.  This is a printed-data
consequence, not a primitive-operation reconstruction of the GE solve. -/
noncomputable def hessenbergDetExampleTable13Residual : Fin 4 → ℝ :=
  fun i =>
    hessenbergDetExampleRhs (1 / 10000000 : ℝ) i -
      matMulVec 4
        (hessenbergDetExampleMatrix (1 / 10000000 : ℝ))
        hessenbergDetExampleTable13ComputedSolution i

/-- Exact rows of `b - A*xhat` for the displayed Table 1.3 computed solution. -/
theorem hessenbergDetExampleTable13_residual_rows :
    hessenbergDetExampleTable13Residual 0 =
        -(13842 / (10 : ℝ) ^ 11) ∧
    hessenbergDetExampleTable13Residual 1 =
        -(13842 / (10 : ℝ) ^ 4) ∧
    hessenbergDetExampleTable13Residual 2 = 0 ∧
    hessenbergDetExampleTable13Residual 3 = 0 := by
  constructor
  · unfold hessenbergDetExampleTable13Residual matMulVec
    rw [Fin.sum_univ_four]
    norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution]
  constructor
  · unfold hessenbergDetExampleTable13Residual matMulVec
    rw [Fin.sum_univ_four]
    norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution]
  constructor
  · unfold hessenbergDetExampleTable13Residual matMulVec
    rw [Fin.sum_univ_four]
    norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution]
    exact sub_self (1 : ℝ)
  · unfold hessenbergDetExampleTable13Residual matMulVec
    rw [Fin.sum_univ_four]
    norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution]

/-- The displayed computed solution vector has infinity norm `2.3842`. -/
theorem hessenbergDetExampleTable13_computedSolution_infNorm_eq :
    infNormVec hessenbergDetExampleTable13ComputedSolution =
      23842 / (10 : ℝ) ^ 4 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;>
        norm_num [hessenbergDetExampleTable13ComputedSolution]
    · norm_num
  · have h :=
      abs_le_infNormVec hessenbergDetExampleTable13ComputedSolution (0 : Fin 4)
    norm_num [hessenbergDetExampleTable13ComputedSolution] at h ⊢
    exact h

/-- The exact residual of the displayed computed solution has infinity norm
`1.3842`, the same visible magnitude as the forward error. -/
theorem hessenbergDetExampleTable13_residual_infNorm_eq :
    infNormVec hessenbergDetExampleTable13Residual =
      13842 / (10 : ℝ) ^ 4 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      rcases hessenbergDetExampleTable13_residual_rows with
        ⟨h0, h1, h2, h3⟩
      fin_cases i <;> simp [h0, h1, h2, h3] <;> norm_num
    · norm_num
  · have h := abs_le_infNormVec hessenbergDetExampleTable13Residual (1 : Fin 4)
    norm_num [hessenbergDetExampleTable13Residual, matMulVec,
      hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution, Fin.sum_univ_four] at h ⊢
    exact h

/-- The source-scaled residual of the displayed computed solution is exactly
`6921/47684` when scaled by `||A||∞ * ||xhat||∞`. -/
theorem hessenbergDetExampleTable13_scaled_residual_eq :
    infNormVec hessenbergDetExampleTable13Residual /
        (infNorm (hessenbergDetExampleMatrix (1 / 10000000 : ℝ)) *
          infNormVec hessenbergDetExampleTable13ComputedSolution) =
      6921 / 47684 := by
  rw [hessenbergDetExampleTable13_residual_infNorm_eq,
    hessenbergDetExampleMatrix_alpha_ten_pow_infNorm_eq,
    hessenbergDetExampleTable13_computedSolution_infNorm_eq]
  norm_num

/-- The source-scaled residual of the displayed computed solution is already
larger than `0.1`, another printed-data indication that this solve path is not
backward stable on the example. -/
theorem hessenbergDetExampleTable13_scaled_residual_gt_one_tenth :
    1 / (10 : ℝ) <
      infNormVec hessenbergDetExampleTable13Residual /
        (infNorm (hessenbergDetExampleMatrix (1 / 10000000 : ℝ)) *
          infNormVec hessenbergDetExampleTable13ComputedSolution) := by
  rw [hessenbergDetExampleTable13_scaled_residual_eq]
  norm_num

/-- Source-value specialization of the §1.16 mixed-stability determinant
bridge: for `alpha = 10^-7`, the final rounded determinant product is within
`gamma_4` of the exact determinant `10000001/5000000`. -/
theorem hessenbergDetExample_alpha_ten_pow_roundedProduct_relError_le_gamma
    (fp : FPModel) (eta : Fin 4 → ℝ)
    (heta : ∀ i : Fin 4, |eta i| ≤ fp.u)
    (hgamma : gammaValid fp 4) :
    relError
        (hessenbergDetRoundedProduct 4
          (hessenbergDetExampleNoPivotUDiag (1 / 10000000 : ℝ)) eta)
        (10000001 / 5000000 : ℝ) ≤ gamma fp 4 := by
  have hbase :=
    hessenbergDetExampleRoundedProduct_relError_le_gamma
      fp (1 / 10000000 : ℝ) eta
      (by norm_num) (by norm_num) heta hgamma
  have hdet :
      Matrix.det
          (hessenbergDetExampleMatrix (1 / 10000000 : ℝ) :
            Matrix (Fin 4) (Fin 4) ℝ) =
        (10000001 / 5000000 : ℝ) :=
    hessenbergDetExampleMatrix_alpha_ten_pow_det_eq
  rw [hdet] at hbase
  exact hbase

/-- The first no-pivot multiplier is `a21/a11 = 1/alpha`. -/
noncomputable def hessenbergDetExampleFirstMultiplier (alpha : ℝ) : ℝ :=
  hessenbergDetExampleMatrix alpha 1 0 / hessenbergDetExampleMatrix alpha 0 0

theorem hessenbergDetExampleFirstMultiplier_eq (alpha : ℝ) :
    hessenbergDetExampleFirstMultiplier alpha = 1 / alpha := by
  norm_num [hessenbergDetExampleFirstMultiplier, hessenbergDetExampleMatrix]

/-- For the displayed `alpha = 10^-7`, the first multiplier is `10^7`. -/
theorem hessenbergDetExampleFirstMultiplier_alpha_ten_pow :
    hessenbergDetExampleFirstMultiplier (1 / (10 : ℝ) ^ 7) =
      (10 : ℝ) ^ 7 := by
  rw [hessenbergDetExampleFirstMultiplier_eq]
  norm_num

end NumStability
