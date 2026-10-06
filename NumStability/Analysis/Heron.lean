-- Analysis/Heron.lean
--
-- Exact algebra and first finite-format bridges for Higham Chapter 2,
-- equation (2.7), Kahan's parenthesized Heron formula.

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.Rounding

namespace NumStability

/-!
# Kahan's Parenthesized Heron Formula

Higham Chapter 2, equation (2.7), rewrites Heron's formula for ordered triangle
sides `a > b > c` as

`(1/4) * sqrt ((a + (b + c)) * (c - (a - b)) *
  (c + (a - b)) * (a + (b - c)))`.

The first results below record the exact algebraic identity and the first
guard-digit bridge used by the formula: under the source ordering and triangle
inequality, the inner subtraction `a - b` satisfies Sterbenz's ratio condition,
so the finite round-to-even subtraction wrapper computes it exactly whenever
`a` and `b` are finite-system numbers.
-/

noncomputable section

/-- Heron's semiperimeter `s = (a+b+c)/2`. -/
def heronSemiperimeter (a b c : ℝ) : ℝ :=
  (a + b + c) / 2

/-- Heron's radicand `s*(s-a)*(s-b)*(s-c)`. -/
def heronRadicand (a b c : ℝ) : ℝ :=
  let s := heronSemiperimeter a b c
  s * (s - a) * (s - b) * (s - c)

/-- Heron's exact area expression. -/
def heronArea (a b c : ℝ) : ℝ :=
  Real.sqrt (heronRadicand a b c)

/-- Kahan's parenthesized Heron radicand from Higham equation (2.7). -/
def kahanHeronRadicand (a b c : ℝ) : ℝ :=
  (a + (b + c)) * (c - (a - b)) *
    (c + (a - b)) * (a + (b - c))

/-- Kahan's parenthesized Heron area expression. -/
def kahanHeronArea (a b c : ℝ) : ℝ :=
  Real.sqrt (kahanHeronRadicand a b c) / 4

/-- Rounded trace component for the parenthesized `a-b` in Kahan's formula. -/
def finiteKahanHeronAB (fmt : FloatingPointFormat) (a b : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.sub a b

/-- Rounded trace component for the parenthesized `b-c` in Kahan's formula. -/
def finiteKahanHeronBC (fmt : FloatingPointFormat) (b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.sub b c

/-- Rounded trace component for the parenthesized `b+c` in Kahan's formula. -/
def finiteKahanHeronBplusC (fmt : FloatingPointFormat) (b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.add b c

/-- First rounded Kahan factor, computed as `fl(a + fl(b+c))`. -/
def finiteKahanHeronFactor1 (fmt : FloatingPointFormat) (a b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.add a (finiteKahanHeronBplusC fmt b c)

/-- Second rounded Kahan factor, computed as `fl(c - fl(a-b))`. -/
def finiteKahanHeronFactor2 (fmt : FloatingPointFormat) (a b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.sub c (finiteKahanHeronAB fmt a b)

/-- Third rounded Kahan factor, computed as `fl(c + fl(a-b))`. -/
def finiteKahanHeronFactor3 (fmt : FloatingPointFormat) (a b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.add c (finiteKahanHeronAB fmt a b)

/-- Fourth rounded Kahan factor, computed as `fl(a + fl(b-c))`. -/
def finiteKahanHeronFactor4 (fmt : FloatingPointFormat) (a b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.add a (finiteKahanHeronBC fmt b c)

/-- First rounded product accumulation in Kahan's Heron trace. -/
def finiteKahanHeronProduct12 (fmt : FloatingPointFormat) (a b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.mul
    (finiteKahanHeronFactor1 fmt a b c)
    (finiteKahanHeronFactor2 fmt a b c)

/-- Second rounded product accumulation in Kahan's Heron trace. -/
def finiteKahanHeronProduct123 (fmt : FloatingPointFormat) (a b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.mul
    (finiteKahanHeronProduct12 fmt a b c)
    (finiteKahanHeronFactor3 fmt a b c)

/-- Rounded parenthesized Kahan radicand trace:
`fl(fl(fl(f1*f2)*f3)*f4)`, with `f1`--`f4` computed by the parenthesized
trace above. -/
def finiteKahanHeronRadicand (fmt : FloatingPointFormat) (a b c : ℝ) : ℝ :=
  let f4 := finiteKahanHeronFactor4 fmt a b c
  fmt.finiteRoundToEvenOp BasicOp.mul
    (finiteKahanHeronProduct123 fmt a b c) f4

/-- Rounded square-root stage in Kahan's Heron trace. -/
def finiteKahanHeronSqrt (fmt : FloatingPointFormat) (a b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenSqrt (finiteKahanHeronRadicand fmt a b c)

/-- Rounded parenthesized Kahan area trace:
`fl(fl_sqrt(radicand) / 4)`. -/
def finiteKahanHeronArea (fmt : FloatingPointFormat) (a b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.div
    (finiteKahanHeronSqrt fmt a b c) 4

/-- A single certificate for the rounded Kahan Heron trace.  It records the
strict standard-model equation for every rounded operation after the exact
Sterbenz subtraction `a-b` has been exposed. -/
def kahanHeronTraceStandardModel
    (fmt : FloatingPointFormat) (a b c : ℝ)
    (δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea : ℝ) :
    Prop :=
  |δbc| < fmt.unitRoundoff ∧
    finiteKahanHeronBC fmt b c = (b - c) * (1 + δbc) ∧
  |δbpc| < fmt.unitRoundoff ∧
    finiteKahanHeronBplusC fmt b c = (b + c) * (1 + δbpc) ∧
  |δf1| < fmt.unitRoundoff ∧
    finiteKahanHeronFactor1 fmt a b c =
      (a + finiteKahanHeronBplusC fmt b c) * (1 + δf1) ∧
  |δf2| < fmt.unitRoundoff ∧
    finiteKahanHeronFactor2 fmt a b c = (c - (a - b)) * (1 + δf2) ∧
  |δf3| < fmt.unitRoundoff ∧
    finiteKahanHeronFactor3 fmt a b c = (c + (a - b)) * (1 + δf3) ∧
  |δf4| < fmt.unitRoundoff ∧
    finiteKahanHeronFactor4 fmt a b c =
      (a + finiteKahanHeronBC fmt b c) * (1 + δf4) ∧
  |δp12| < fmt.unitRoundoff ∧
    finiteKahanHeronProduct12 fmt a b c =
      (finiteKahanHeronFactor1 fmt a b c *
        finiteKahanHeronFactor2 fmt a b c) * (1 + δp12) ∧
  |δp123| < fmt.unitRoundoff ∧
    finiteKahanHeronProduct123 fmt a b c =
      (finiteKahanHeronProduct12 fmt a b c *
        finiteKahanHeronFactor3 fmt a b c) * (1 + δp123) ∧
  |δr| < fmt.unitRoundoff ∧
    finiteKahanHeronRadicand fmt a b c =
      (finiteKahanHeronProduct123 fmt a b c *
        finiteKahanHeronFactor4 fmt a b c) * (1 + δr) ∧
  |δsqrt| < fmt.unitRoundoff ∧
    finiteKahanHeronSqrt fmt a b c =
      Real.sqrt (finiteKahanHeronRadicand fmt a b c) * (1 + δsqrt) ∧
  |δarea| < fmt.unitRoundoff ∧
    finiteKahanHeronArea fmt a b c =
      (finiteKahanHeronSqrt fmt a b c / 4) * (1 + δarea)

/-- The radicand expression obtained by expanding the rounded Kahan trace
through the product accumulation and substituting the local standard-model
factors. -/
def kahanHeronExpandedRadicand
    (a b c : ℝ)
    (δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr : ℝ) : ℝ :=
  ((((((a + (b + c) * (1 + δbpc)) * (1 + δf1)) *
      ((c - (a - b)) * (1 + δf2))) * (1 + δp12) *
      ((c + (a - b)) * (1 + δf3))) * (1 + δp123) *
      ((a + (b - c) * (1 + δbc)) * (1 + δf4))) * (1 + δr))

/-- Relative distortion induced in the first exact Kahan factor by rounding
the preliminary `b+c` operation. -/
def kahanHeronBplusCRelativeDistortion (a b c δ : ℝ) : ℝ :=
  ((b + c) / (a + (b + c))) * δ

/-- Relative distortion induced in the fourth exact Kahan factor by rounding
the preliminary `b-c` operation. -/
def kahanHeronBminusCRelativeDistortion (a b c δ : ℝ) : ℝ :=
  ((b - c) / (a + (b - c))) * δ

/-- The nine local relative-error factors that multiply the exact Kahan
radicand after expanding the rounded product trace. -/
def kahanHeronRadicandLocalFactorProduct
    (a b c : ℝ)
    (δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr : ℝ) : ℝ :=
  (1 + kahanHeronBplusCRelativeDistortion a b c δbpc) *
    (1 + δf1) *
    (1 + δf2) *
    (1 + δp12) *
    (1 + δf3) *
    (1 + δp123) *
    (1 + kahanHeronBminusCRelativeDistortion a b c δbc) *
    (1 + δf4) *
    (1 + δr)

/-- The local radicand errors in the order consumed by `prod_error_bound`. -/
def kahanHeronRadicandLocalErrors
    (a b c : ℝ)
    (δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr : ℝ) : Fin 9 → ℝ :=
  ![kahanHeronBplusCRelativeDistortion a b c δbpc,
    δf1,
    δf2,
    δp12,
    δf3,
    δp123,
    kahanHeronBminusCRelativeDistortion a b c δbc,
    δf4,
    δr]

/-- A lightweight `FPModel` carrier whose unit roundoff is the concrete finite
format's `unitRoundoff`; used only to reuse the repository's `γ_n` product
bound. -/
noncomputable def finiteFormatUnitRoundoffModel
    (fmt : FloatingPointFormat) : FPModel :=
  FPModel.exactWithUnitRoundoff fmt.unitRoundoff fmt.unitRoundoff_nonneg

/-- Source-side ordering for Kahan's formula: `a > b > c > 0` and the
nondegenerate triangle inequality `a < b+c`. -/
def kahanOrderedTriangleSides (a b c : ℝ) : Prop :=
  0 < c ∧ c < b ∧ b < a ∧ a < b + c

theorem kahanOrderedTriangleSides_b_pos
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < b :=
  lt_trans h.1 h.2.1

theorem kahanOrderedTriangleSides_a_pos
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < a :=
  lt_trans (kahanOrderedTriangleSides_b_pos h) h.2.2.1

theorem kahanOrderedTriangleSides_a_sub_b_pos
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < a - b := by
  linarith [h.2.2.1]

theorem kahanOrderedTriangleSides_a_sub_b_lt_c
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    a - b < c := by
  linarith [h.2.2.2]

theorem kahanHeronFactor_a_add_b_add_c_pos
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < a + (b + c) := by
  linarith [kahanOrderedTriangleSides_a_pos h,
    kahanOrderedTriangleSides_b_pos h, h.1]

theorem kahanHeronFactor_b_sub_c_pos
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < b - c := by
  linarith [h.2.1]

theorem kahanHeronFactor_b_add_c_pos
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < b + c := by
  linarith [kahanOrderedTriangleSides_b_pos h, h.1]

theorem kahanHeronFactor_c_sub_a_sub_b_pos
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < c - (a - b) := by
  linarith [kahanOrderedTriangleSides_a_sub_b_lt_c h]

theorem kahanHeronFactor_c_add_a_sub_b_pos
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < c + (a - b) := by
  linarith [h.1, kahanOrderedTriangleSides_a_sub_b_pos h]

theorem kahanHeronFactor_a_add_b_sub_c_pos
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < a + (b - c) := by
  linarith [kahanOrderedTriangleSides_a_pos h, h.2.1]

/-- Ordered nondegenerate triangle sides make all four exact Kahan product
factors positive. -/
theorem kahanHeronExactFactors_pos_of_kahanOrderedTriangleSides
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < a + (b + c) ∧
      0 < c - (a - b) ∧
      0 < c + (a - b) ∧
      0 < a + (b - c) :=
  ⟨kahanHeronFactor_a_add_b_add_c_pos h,
    kahanHeronFactor_c_sub_a_sub_b_pos h,
    kahanHeronFactor_c_add_a_sub_b_pos h,
    kahanHeronFactor_a_add_b_sub_c_pos h⟩

/-- The rounded `b+c` perturbation contributes only the fraction of that
inner sum present in the first exact Kahan factor. -/
theorem kahanHeronRatio_b_add_c_abs_le_one
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    |(b + c) / (a + (b + c))| ≤ 1 := by
  have hnum_nonneg : 0 ≤ b + c :=
    le_of_lt (kahanHeronFactor_b_add_c_pos h)
  have hden_pos : 0 < a + (b + c) :=
    kahanHeronFactor_a_add_b_add_c_pos h
  have hratio_nonneg : 0 ≤ (b + c) / (a + (b + c)) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hratio_le_one : (b + c) / (a + (b + c)) ≤ 1 :=
    (div_le_one hden_pos).2 (by linarith [kahanOrderedTriangleSides_a_pos h])
  simpa [abs_of_nonneg hratio_nonneg] using hratio_le_one

/-- The rounded `b-c` perturbation contributes only the fraction of that
inner difference present in the fourth exact Kahan factor. -/
theorem kahanHeronRatio_b_sub_c_abs_le_one
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    |(b - c) / (a + (b - c))| ≤ 1 := by
  have hnum_nonneg : 0 ≤ b - c :=
    le_of_lt (kahanHeronFactor_b_sub_c_pos h)
  have hden_pos : 0 < a + (b - c) :=
    kahanHeronFactor_a_add_b_sub_c_pos h
  have hratio_nonneg : 0 ≤ (b - c) / (a + (b - c)) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hratio_le_one : (b - c) / (a + (b - c)) ≤ 1 :=
    (div_le_one hden_pos).2 (by linarith [kahanOrderedTriangleSides_a_pos h])
  simpa [abs_of_nonneg hratio_nonneg] using hratio_le_one

theorem kahanHeronScaled_b_add_c_delta_abs_le_unitRoundoff
    {fmt : FloatingPointFormat} {a b c δ : ℝ}
    (h : kahanOrderedTriangleSides a b c)
    (hδ : |δ| < fmt.unitRoundoff) :
    |kahanHeronBplusCRelativeDistortion a b c δ| ≤ fmt.unitRoundoff := by
  have hratio := kahanHeronRatio_b_add_c_abs_le_one h
  have hbound : |((b + c) / (a + (b + c))) * δ| < fmt.unitRoundoff := by
    calc
      |((b + c) / (a + (b + c))) * δ|
          = |(b + c) / (a + (b + c))| * |δ| := by rw [abs_mul]
      _ ≤ 1 * |δ| := by
          exact mul_le_mul_of_nonneg_right hratio (abs_nonneg δ)
      _ = |δ| := by ring
      _ < fmt.unitRoundoff := hδ
  simpa [kahanHeronBplusCRelativeDistortion] using le_of_lt hbound

theorem kahanHeronScaled_b_sub_c_delta_abs_le_unitRoundoff
    {fmt : FloatingPointFormat} {a b c δ : ℝ}
    (h : kahanOrderedTriangleSides a b c)
    (hδ : |δ| < fmt.unitRoundoff) :
    |kahanHeronBminusCRelativeDistortion a b c δ| ≤ fmt.unitRoundoff := by
  have hratio := kahanHeronRatio_b_sub_c_abs_le_one h
  have hbound : |((b - c) / (a + (b - c))) * δ| < fmt.unitRoundoff := by
    calc
      |((b - c) / (a + (b - c))) * δ|
          = |(b - c) / (a + (b - c))| * |δ| := by rw [abs_mul]
      _ ≤ 1 * |δ| := by
          exact mul_le_mul_of_nonneg_right hratio (abs_nonneg δ)
      _ = |δ| := by ring
      _ < fmt.unitRoundoff := hδ
  simpa [kahanHeronBminusCRelativeDistortion] using le_of_lt hbound

/-- Kahan's product is exactly sixteen times Heron's radicand. -/
theorem kahanHeronRadicand_eq_sixteen_mul_heronRadicand
    (a b c : ℝ) :
    kahanHeronRadicand a b c = 16 * heronRadicand a b c := by
  unfold kahanHeronRadicand heronRadicand heronSemiperimeter
  ring

theorem heronRadicand_pos_of_kahanOrderedTriangleSides
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < heronRadicand a b c := by
  unfold heronRadicand heronSemiperimeter
  have hs : 0 < (a + b + c) / 2 := by
    linarith [kahanOrderedTriangleSides_a_pos h,
      kahanOrderedTriangleSides_b_pos h, h.1]
  have hsa : 0 < (a + b + c) / 2 - a := by
    linarith [h.2.2.2]
  have hsb : 0 < (a + b + c) / 2 - b := by
    linarith [h.2.2.1, h.1]
  have hsc : 0 < (a + b + c) / 2 - c := by
    linarith [kahanOrderedTriangleSides_a_pos h, h.2.1]
  positivity

theorem kahanHeronRadicand_pos_of_kahanOrderedTriangleSides
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < kahanHeronRadicand a b c := by
  rw [kahanHeronRadicand_eq_sixteen_mul_heronRadicand]
  exact mul_pos (by norm_num) (heronRadicand_pos_of_kahanOrderedTriangleSides h)

theorem kahanHeronArea_pos_of_kahanOrderedTriangleSides
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    0 < kahanHeronArea a b c := by
  unfold kahanHeronArea
  exact div_pos
    (Real.sqrt_pos_of_pos (kahanHeronRadicand_pos_of_kahanOrderedTriangleSides h))
    (by norm_num)

/-- Kahan's parenthesized area has the same squared value as Heron's radicand
for ordered nondegenerate triangle sides. -/
theorem kahanHeronArea_sq_eq_heronRadicand_of_kahanOrderedTriangleSides
    {a b c : ℝ} (h : kahanOrderedTriangleSides a b c) :
    kahanHeronArea a b c ^ 2 = heronRadicand a b c := by
  unfold kahanHeronArea
  rw [kahanHeronRadicand_eq_sixteen_mul_heronRadicand]
  have hRnonneg : 0 ≤ heronRadicand a b c :=
    le_of_lt (heronRadicand_pos_of_kahanOrderedTriangleSides h)
  have h16R : 0 ≤ 16 * heronRadicand a b c :=
    mul_nonneg (by norm_num) hRnonneg
  rw [div_pow, Real.sq_sqrt h16R]
  ring

/-- Ordered triangle sides imply Sterbenz's ratio condition for the first
inner subtraction `a-b` in Kahan's formula. -/
theorem kahanOrderedTriangleSides_sterbenzRatioCondition_a_b
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (h : kahanOrderedTriangleSides a b c) :
    fmt.sterbenzRatioCondition a b := by
  unfold FloatingPointFormat.sterbenzRatioCondition
  constructor
  · have hbpos : 0 < b := kahanOrderedTriangleSides_b_pos h
    linarith [hbpos, h.2.2.1]
  · linarith [h.2.1, h.2.2.2]

/-- First finite-format Kahan/Heron bridge: the parenthesized subtraction
`a-b` is exact for finite round-to-even subtraction under the source ordering
and triangle inequality. -/
theorem finiteRoundToEvenOp_sub_a_b_eq_exact_of_kahanOrderedTriangleSides
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (h : kahanOrderedTriangleSides a b c) :
    fmt.finiteRoundToEvenOp BasicOp.sub a b = a - b :=
  fmt.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition
    ha hb (kahanOrderedTriangleSides_sterbenzRatioCondition_a_b (fmt := fmt) h)

/-- The first subtraction in the rounded Kahan trace is exact under the source
ordered-side assumptions whenever `a` and `b` are finite-system inputs. -/
theorem finiteKahanHeronAB_eq_exact_of_kahanOrderedTriangleSides
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (h : kahanOrderedTriangleSides a b c) :
    finiteKahanHeronAB fmt a b = a - b :=
  finiteRoundToEvenOp_sub_a_b_eq_exact_of_kahanOrderedTriangleSides ha hb h

theorem finiteKahanHeronBC_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {b c : ℝ}
    (hbc : fmt.finiteNormalRange (b - c)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronBC fmt b c = (b - c) * (1 + δ) := by
  simpa [finiteKahanHeronBC, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.sub) (x := b) (y := c) hbc)

theorem finiteKahanHeronBplusC_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {b c : ℝ}
    (hbpc : fmt.finiteNormalRange (b + c)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronBplusC fmt b c = (b + c) * (1 + δ) := by
  simpa [finiteKahanHeronBplusC, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.add) (x := b) (y := c) hbpc)

theorem finiteKahanHeronFactor1_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (hf1 : fmt.finiteNormalRange (a + finiteKahanHeronBplusC fmt b c)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronFactor1 fmt a b c =
        (a + finiteKahanHeronBplusC fmt b c) * (1 + δ) := by
  simpa [finiteKahanHeronFactor1, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.add) (x := a) (y := finiteKahanHeronBplusC fmt b c) hf1)

theorem finiteKahanHeronFactor2_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (hf2 : fmt.finiteNormalRange (c - finiteKahanHeronAB fmt a b)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronFactor2 fmt a b c =
        (c - finiteKahanHeronAB fmt a b) * (1 + δ) := by
  simpa [finiteKahanHeronFactor2, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.sub) (x := c) (y := finiteKahanHeronAB fmt a b) hf2)

theorem finiteKahanHeronFactor2_standardModel_lt_of_finiteNormalRange_exactAB
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (h : kahanOrderedTriangleSides a b c)
    (hf2 : fmt.finiteNormalRange (c - (a - b))) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronFactor2 fmt a b c = (c - (a - b)) * (1 + δ) := by
  have hab := finiteKahanHeronAB_eq_exact_of_kahanOrderedTriangleSides
    (fmt := fmt) (c := c) ha hb h
  have hf2' : fmt.finiteNormalRange (c - finiteKahanHeronAB fmt a b) := by
    simpa [hab] using hf2
  simpa [hab] using
    (finiteKahanHeronFactor2_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c) hf2')

theorem finiteKahanHeronFactor3_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (hf3 : fmt.finiteNormalRange (c + finiteKahanHeronAB fmt a b)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronFactor3 fmt a b c =
        (c + finiteKahanHeronAB fmt a b) * (1 + δ) := by
  simpa [finiteKahanHeronFactor3, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.add) (x := c) (y := finiteKahanHeronAB fmt a b) hf3)

theorem finiteKahanHeronFactor3_standardModel_lt_of_finiteNormalRange_exactAB
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (h : kahanOrderedTriangleSides a b c)
    (hf3 : fmt.finiteNormalRange (c + (a - b))) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronFactor3 fmt a b c = (c + (a - b)) * (1 + δ) := by
  have hab := finiteKahanHeronAB_eq_exact_of_kahanOrderedTriangleSides
    (fmt := fmt) (c := c) ha hb h
  have hf3' : fmt.finiteNormalRange (c + finiteKahanHeronAB fmt a b) := by
    simpa [hab] using hf3
  simpa [hab] using
    (finiteKahanHeronFactor3_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c) hf3')

theorem finiteKahanHeronFactor4_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (hf4 : fmt.finiteNormalRange (a + finiteKahanHeronBC fmt b c)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronFactor4 fmt a b c =
        (a + finiteKahanHeronBC fmt b c) * (1 + δ) := by
  simpa [finiteKahanHeronFactor4, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.add) (x := a) (y := finiteKahanHeronBC fmt b c) hf4)

theorem finiteKahanHeronProduct12_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (hp12 : fmt.finiteNormalRange
      (finiteKahanHeronFactor1 fmt a b c * finiteKahanHeronFactor2 fmt a b c)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronProduct12 fmt a b c =
        (finiteKahanHeronFactor1 fmt a b c *
          finiteKahanHeronFactor2 fmt a b c) * (1 + δ) := by
  simpa [finiteKahanHeronProduct12, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.mul)
      (x := finiteKahanHeronFactor1 fmt a b c)
      (y := finiteKahanHeronFactor2 fmt a b c) hp12)

theorem finiteKahanHeronProduct123_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (hp123 : fmt.finiteNormalRange
      (finiteKahanHeronProduct12 fmt a b c * finiteKahanHeronFactor3 fmt a b c)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronProduct123 fmt a b c =
        (finiteKahanHeronProduct12 fmt a b c *
          finiteKahanHeronFactor3 fmt a b c) * (1 + δ) := by
  simpa [finiteKahanHeronProduct123, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.mul)
      (x := finiteKahanHeronProduct12 fmt a b c)
      (y := finiteKahanHeronFactor3 fmt a b c) hp123)

theorem finiteKahanHeronRadicand_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (hr : fmt.finiteNormalRange
      (finiteKahanHeronProduct123 fmt a b c * finiteKahanHeronFactor4 fmt a b c)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronRadicand fmt a b c =
        (finiteKahanHeronProduct123 fmt a b c *
          finiteKahanHeronFactor4 fmt a b c) * (1 + δ) := by
  simpa [finiteKahanHeronRadicand, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.mul)
      (x := finiteKahanHeronProduct123 fmt a b c)
      (y := finiteKahanHeronFactor4 fmt a b c) hr)

theorem finiteKahanHeronSqrt_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (hr_nonneg : 0 ≤ finiteKahanHeronRadicand fmt a b c)
    (hsqrt : fmt.finiteNormalRange
      (Real.sqrt (finiteKahanHeronRadicand fmt a b c))) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronSqrt fmt a b c =
        Real.sqrt (finiteKahanHeronRadicand fmt a b c) * (1 + δ) := by
  simpa [finiteKahanHeronSqrt] using
    (fmt.finiteRoundToEvenSqrt_standardModel_lt_of_finiteNormalRange
      (x := finiteKahanHeronRadicand fmt a b c) hr_nonneg hsqrt)

theorem finiteKahanHeronArea_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (harea : fmt.finiteNormalRange (finiteKahanHeronSqrt fmt a b c / 4)) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧
      finiteKahanHeronArea fmt a b c =
        (finiteKahanHeronSqrt fmt a b c / 4) * (1 + δ) := by
  simpa [finiteKahanHeronArea, BasicOp.exact, div_eq_mul_inv] using
    (fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.div) (x := finiteKahanHeronSqrt fmt a b c) (y := 4) harea)

/-- Combined strict standard-model certificate for Kahan's rounded Heron trace.
The assumptions are exactly the finite-system/exact-subtraction inputs plus the
finite-normal-range premises needed by each remaining rounded operation. -/
theorem finiteKahanHeronTrace_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (h : kahanOrderedTriangleSides a b c)
    (hbc : fmt.finiteNormalRange (b - c))
    (hbpc : fmt.finiteNormalRange (b + c))
    (hf1 : fmt.finiteNormalRange (a + finiteKahanHeronBplusC fmt b c))
    (hf2 : fmt.finiteNormalRange (c - (a - b)))
    (hf3 : fmt.finiteNormalRange (c + (a - b)))
    (hf4 : fmt.finiteNormalRange (a + finiteKahanHeronBC fmt b c))
    (hp12 : fmt.finiteNormalRange
      (finiteKahanHeronFactor1 fmt a b c * finiteKahanHeronFactor2 fmt a b c))
    (hp123 : fmt.finiteNormalRange
      (finiteKahanHeronProduct12 fmt a b c * finiteKahanHeronFactor3 fmt a b c))
    (hr : fmt.finiteNormalRange
      (finiteKahanHeronProduct123 fmt a b c * finiteKahanHeronFactor4 fmt a b c))
    (hr_nonneg : 0 ≤ finiteKahanHeronRadicand fmt a b c)
    (hsqrt : fmt.finiteNormalRange
      (Real.sqrt (finiteKahanHeronRadicand fmt a b c)))
    (harea : fmt.finiteNormalRange (finiteKahanHeronSqrt fmt a b c / 4)) :
    ∃ δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea : ℝ,
      kahanHeronTraceStandardModel fmt a b c
        δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea := by
  rcases finiteKahanHeronBC_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (b := b) (c := c) hbc with
    ⟨δbc, hδbc, hbc_eq⟩
  rcases finiteKahanHeronBplusC_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (b := b) (c := c) hbpc with
    ⟨δbpc, hδbpc, hbpc_eq⟩
  rcases finiteKahanHeronFactor1_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c) hf1 with
    ⟨δf1, hδf1, hf1_eq⟩
  rcases finiteKahanHeronFactor2_standardModel_lt_of_finiteNormalRange_exactAB
      (fmt := fmt) (a := a) (b := b) (c := c) ha hb h hf2 with
    ⟨δf2, hδf2, hf2_eq⟩
  rcases finiteKahanHeronFactor3_standardModel_lt_of_finiteNormalRange_exactAB
      (fmt := fmt) (a := a) (b := b) (c := c) ha hb h hf3 with
    ⟨δf3, hδf3, hf3_eq⟩
  rcases finiteKahanHeronFactor4_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c) hf4 with
    ⟨δf4, hδf4, hf4_eq⟩
  rcases finiteKahanHeronProduct12_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c) hp12 with
    ⟨δp12, hδp12, hp12_eq⟩
  rcases finiteKahanHeronProduct123_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c) hp123 with
    ⟨δp123, hδp123, hp123_eq⟩
  rcases finiteKahanHeronRadicand_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c) hr with
    ⟨δr, hδr, hr_eq⟩
  rcases finiteKahanHeronSqrt_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c) hr_nonneg hsqrt with
    ⟨δsqrt, hδsqrt, hsqrt_eq⟩
  rcases finiteKahanHeronArea_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c) harea with
    ⟨δarea, hδarea, harea_eq⟩
  refine ⟨δbc, δbpc, δf1, δf2, δf3, δf4, δp12, δp123, δr, δsqrt, δarea, ?_⟩
  exact ⟨hδbc, hbc_eq, hδbpc, hbpc_eq, hδf1, hf1_eq,
    hδf2, hf2_eq, hδf3, hf3_eq, hδf4, hf4_eq, hδp12, hp12_eq,
    hδp123, hp123_eq, hδr, hr_eq, hδsqrt, hsqrt_eq, hδarea, harea_eq⟩

/-- Exact expanded radicand equation obtained by substituting the combined
Kahan trace certificate through the product accumulation.  This is the
algebraic substrate for the later aggregate relative-error bound. -/
theorem kahanHeronTraceStandardModel_radicand_eq_expanded
    {fmt : FloatingPointFormat} {a b c : ℝ}
    {δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea : ℝ}
    (htrace : kahanHeronTraceStandardModel fmt a b c
      δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea) :
    finiteKahanHeronRadicand fmt a b c =
      kahanHeronExpandedRadicand a b c
        δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr := by
  rcases htrace with
    ⟨_hδbc, hbc_eq, _hδbpc, hbpc_eq, _hδf1, hf1_eq,
      _hδf2, hf2_eq, _hδf3, hf3_eq, _hδf4, hf4_eq,
      _hδp12, hp12_eq, _hδp123, hp123_eq, _hδr, hr_eq,
      _hδsqrt, _hsqrt_eq, _hδarea, _harea_eq⟩
  rw [hr_eq, hp123_eq, hp12_eq, hf1_eq, hf2_eq, hf3_eq, hf4_eq, hbpc_eq, hbc_eq]
  rfl

/-- Algebraic rewrite of the first perturbed factor in the expanded trace as
the exact first Kahan factor times one scaled local relative error. -/
theorem kahanHeronFactor1_perturbed_eq_exact_mul_local_factor
    {a b c : ℝ}
    {δ : ℝ}
    (h : kahanOrderedTriangleSides a b c) :
    a + (b + c) * (1 + δ) =
      (a + (b + c)) * (1 + kahanHeronBplusCRelativeDistortion a b c δ) := by
  have hden1 : a + (b + c) ≠ 0 :=
    ne_of_gt (kahanHeronFactor_a_add_b_add_c_pos h)
  unfold kahanHeronBplusCRelativeDistortion
  field_simp [hden1]
  ring

/-- Algebraic rewrite of the fourth perturbed factor in the expanded trace as
the exact fourth Kahan factor times one scaled local relative error. -/
theorem kahanHeronFactor4_perturbed_eq_exact_mul_local_factor
    {a b c : ℝ}
    {δ : ℝ}
    (h : kahanOrderedTriangleSides a b c) :
    a + (b - c) * (1 + δ) =
      (a + (b - c)) * (1 + kahanHeronBminusCRelativeDistortion a b c δ) := by
  have hden4 : a + (b - c) ≠ 0 :=
    ne_of_gt (kahanHeronFactor_a_add_b_sub_c_pos h)
  unfold kahanHeronBminusCRelativeDistortion
  field_simp [hden4]
  ring

/-- Abstract commutative-ring identity used to keep the Kahan radicand
factorization proof from expanding the side expressions `a+(b+c)` and
`a+(b-c)`. -/
theorem kahanHeronRadicand_local_factor_product_algebra
    (A B C D e1 ef1 ef2 ep12 ef3 ep123 e4 ef4 er : ℝ) :
    A * (1 + e1) * (1 + ef1) * (B * (1 + ef2)) *
        (1 + ep12) * (C * (1 + ef3)) *
        (1 + ep123) * (D * (1 + e4) * (1 + ef4)) *
        (1 + er) =
      (A * B * C * D) *
        ((1 + e1) *
          (1 + ef1) *
          (1 + ef2) *
          (1 + ep12) *
          (1 + ef3) *
          (1 + ep123) *
          (1 + e4) *
          (1 + ef4) *
          (1 + er)) := by
  ring

theorem kahanHeronRadicandLocalFactorProduct_eq_prod
    (a b c : ℝ)
    (δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr : ℝ) :
    kahanHeronRadicandLocalFactorProduct a b c
        δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr =
      ∏ i : Fin 9,
        (1 + kahanHeronRadicandLocalErrors a b c
          δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr i) := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_eight]
  simp [kahanHeronRadicandLocalFactorProduct,
    kahanHeronRadicandLocalErrors]

/-- Every local factor in the expanded Kahan radicand is bounded by the
format unit roundoff.  The first and seventh entries are the scaled preliminary
`b+c` and `b-c` errors; all other entries come directly from the trace
certificate. -/
theorem kahanHeronRadicandLocalErrors_abs_le_unitRoundoff
    {fmt : FloatingPointFormat} {a b c : ℝ}
    {δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea : ℝ}
    (hside : kahanOrderedTriangleSides a b c)
    (htrace : kahanHeronTraceStandardModel fmt a b c
      δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea) :
    ∀ i : Fin 9,
      |kahanHeronRadicandLocalErrors a b c
        δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr i| ≤
        (finiteFormatUnitRoundoffModel fmt).u := by
  rcases htrace with
    ⟨hδbc, _hbc_eq, hδbpc, _hbpc_eq, hδf1, _hf1_eq,
      hδf2, _hf2_eq, hδf3, _hf3_eq, hδf4, _hf4_eq,
      hδp12, _hp12_eq, hδp123, _hp123_eq, hδr, _hr_eq,
      _hδsqrt, _hsqrt_eq, _hδarea, _harea_eq⟩
  intro i
  fin_cases i
  · simpa [kahanHeronRadicandLocalErrors, finiteFormatUnitRoundoffModel] using
      kahanHeronScaled_b_add_c_delta_abs_le_unitRoundoff
        (fmt := fmt) hside hδbpc
  · simpa [kahanHeronRadicandLocalErrors, finiteFormatUnitRoundoffModel] using
      le_of_lt hδf1
  · simpa [kahanHeronRadicandLocalErrors, finiteFormatUnitRoundoffModel] using
      le_of_lt hδf2
  · simpa [kahanHeronRadicandLocalErrors, finiteFormatUnitRoundoffModel] using
      le_of_lt hδp12
  · simpa [kahanHeronRadicandLocalErrors, finiteFormatUnitRoundoffModel] using
      le_of_lt hδf3
  · simpa [kahanHeronRadicandLocalErrors, finiteFormatUnitRoundoffModel] using
      le_of_lt hδp123
  · simpa [kahanHeronRadicandLocalErrors, finiteFormatUnitRoundoffModel] using
      kahanHeronScaled_b_sub_c_delta_abs_le_unitRoundoff
        (fmt := fmt) hside hδbc
  · simpa [kahanHeronRadicandLocalErrors, finiteFormatUnitRoundoffModel] using
      le_of_lt hδf4
  · simpa [kahanHeronRadicandLocalErrors, finiteFormatUnitRoundoffModel] using
      le_of_lt hδr

/-- The expanded rounded radicand is the exact Kahan product times nine local
relative-error factors.  The two extra factors are the scaled errors inherited
from the preliminary rounded `b+c` and `b-c` operations. -/
theorem kahanHeronExpandedRadicand_eq_exact_mul_local_factors
    {a b c : ℝ}
    {δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr : ℝ}
    (h : kahanOrderedTriangleSides a b c) :
    kahanHeronExpandedRadicand a b c
        δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr =
      kahanHeronRadicand a b c *
        kahanHeronRadicandLocalFactorProduct a b c
          δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr := by
  have h1 :=
    kahanHeronFactor1_perturbed_eq_exact_mul_local_factor
      (a := a) (b := b) (c := c) (δ := δbpc) h
  have h4 :=
    kahanHeronFactor4_perturbed_eq_exact_mul_local_factor
      (a := a) (b := b) (c := c) (δ := δbc) h
  unfold kahanHeronExpandedRadicand
  rw [h1, h4]
  simpa [kahanHeronRadicand, kahanHeronRadicandLocalFactorProduct] using
    kahanHeronRadicand_local_factor_product_algebra
      (a + (b + c))
      (c - (a - b))
      (c + (a - b))
      (a + (b - c))
      (kahanHeronBplusCRelativeDistortion a b c δbpc)
      δf1 δf2 δp12 δf3 δp123
      (kahanHeronBminusCRelativeDistortion a b c δbc)
      δf4 δr

/-- Aggregate radicand-level relative-error theorem for Kahan's rounded Heron
trace: after the exact Sterbenz subtraction `a-b`, the rounded radicand differs
from the exact Kahan radicand by one `γ₉` relative factor. -/
theorem kahanHeronTraceStandardModel_radicand_rel_error_le_gamma9
    {fmt : FloatingPointFormat} {a b c : ℝ}
    {δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea : ℝ}
    (hside : kahanOrderedTriangleSides a b c)
    (htrace : kahanHeronTraceStandardModel fmt a b c
      δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea)
    (hγ : gammaValid (finiteFormatUnitRoundoffModel fmt) 9) :
    ∃ θ : ℝ,
      |θ| ≤ gamma (finiteFormatUnitRoundoffModel fmt) 9 ∧
        finiteKahanHeronRadicand fmt a b c =
          kahanHeronRadicand a b c * (1 + θ) := by
  obtain ⟨θ, hθ, hprod⟩ :=
    prod_error_bound (finiteFormatUnitRoundoffModel fmt) 9
      (kahanHeronRadicandLocalErrors a b c
        δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr)
      (kahanHeronRadicandLocalErrors_abs_le_unitRoundoff
        (fmt := fmt) (a := a) (b := b) (c := c)
        (δbc := δbc) (δbpc := δbpc) (δf1 := δf1) (δf2 := δf2)
        (δf3 := δf3) (δf4 := δf4) (δp12 := δp12)
        (δp123 := δp123) (δr := δr) (δsqrt := δsqrt)
        (δarea := δarea) hside htrace)
      hγ
  refine ⟨θ, hθ, ?_⟩
  rw [kahanHeronTraceStandardModel_radicand_eq_expanded
      (fmt := fmt) (a := a) (b := b) (c := c)
      (δbc := δbc) (δbpc := δbpc) (δf1 := δf1) (δf2 := δf2)
      (δf3 := δf3) (δf4 := δf4) (δp12 := δp12) (δp123 := δp123)
      (δr := δr) (δsqrt := δsqrt) (δarea := δarea) htrace]
  rw [kahanHeronExpandedRadicand_eq_exact_mul_local_factors hside]
  rw [kahanHeronRadicandLocalFactorProduct_eq_prod]
  rw [hprod]

/-- Exact expanded area equation obtained by substituting the combined Kahan
trace certificate through product accumulation, square-root rounding, and the
final division by four. -/
theorem kahanHeronTraceStandardModel_area_eq_expanded
    {fmt : FloatingPointFormat} {a b c : ℝ}
    {δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea : ℝ}
    (htrace : kahanHeronTraceStandardModel fmt a b c
      δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea) :
    finiteKahanHeronArea fmt a b c =
      (Real.sqrt (kahanHeronExpandedRadicand a b c
        δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr) *
        (1 + δsqrt) / 4) * (1 + δarea) := by
  have hr_exp :=
    kahanHeronTraceStandardModel_radicand_eq_expanded
      (fmt := fmt) (a := a) (b := b) (c := c)
      (δbc := δbc) (δbpc := δbpc) (δf1 := δf1) (δf2 := δf2)
      (δf3 := δf3) (δf4 := δf4) (δp12 := δp12) (δp123 := δp123)
      (δr := δr) (δsqrt := δsqrt) (δarea := δarea) htrace
  rcases htrace with
    ⟨_hδbc, _hbc_eq, _hδbpc, _hbpc_eq, _hδf1, _hf1_eq,
      _hδf2, _hf2_eq, _hδf3, _hf3_eq, _hδf4, _hf4_eq,
      _hδp12, _hp12_eq, _hδp123, _hp123_eq, _hδr, _hr_eq,
      _hδsqrt, hsqrt_eq, _hδarea, harea_eq⟩
  rw [harea_eq, hsqrt_eq, hr_exp]

/-- Full rounded area trace after aggregating the radicand computation into
one `γ₉` factor.  The square-root and final division roundings remain visible
as their own local standard-model factors. -/
theorem kahanHeronTraceStandardModel_area_eq_gamma9_radicand
    {fmt : FloatingPointFormat} {a b c : ℝ}
    {δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea : ℝ}
    (hside : kahanOrderedTriangleSides a b c)
    (htrace : kahanHeronTraceStandardModel fmt a b c
      δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea)
    (hγ : gammaValid (finiteFormatUnitRoundoffModel fmt) 9) :
    ∃ θ : ℝ,
      |θ| ≤ gamma (finiteFormatUnitRoundoffModel fmt) 9 ∧
        finiteKahanHeronArea fmt a b c =
          (Real.sqrt (kahanHeronRadicand a b c * (1 + θ)) *
            (1 + δsqrt) / 4) * (1 + δarea) := by
  obtain ⟨θ, hθ, hrad⟩ :=
    kahanHeronTraceStandardModel_radicand_rel_error_le_gamma9
      (fmt := fmt) (a := a) (b := b) (c := c)
      (δbc := δbc) (δbpc := δbpc) (δf1 := δf1) (δf2 := δf2)
      (δf3 := δf3) (δf4 := δf4) (δp12 := δp12) (δp123 := δp123)
      (δr := δr) (δsqrt := δsqrt) (δarea := δarea)
      hside htrace hγ
  refine ⟨θ, hθ, ?_⟩
  have hexp :
      kahanHeronExpandedRadicand a b c
          δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr =
        kahanHeronRadicand a b c * (1 + θ) := by
    rw [← kahanHeronTraceStandardModel_radicand_eq_expanded
      (fmt := fmt) (a := a) (b := b) (c := c)
      (δbc := δbc) (δbpc := δbpc) (δf1 := δf1) (δf2 := δf2)
      (δf3 := δf3) (δf4 := δf4) (δp12 := δp12) (δp123 := δp123)
      (δr := δr) (δsqrt := δsqrt) (δarea := δarea) htrace]
    exact hrad
  rw [kahanHeronTraceStandardModel_area_eq_expanded
      (fmt := fmt) (a := a) (b := b) (c := c)
      (δbc := δbc) (δbpc := δbpc) (δf1 := δf1) (δf2 := δf2)
      (δf3 := δf3) (δf4 := δf4) (δp12 := δp12) (δp123 := δp123)
      (δr := δr) (δsqrt := δsqrt) (δarea := δarea) htrace]
  rw [hexp]

/-- Area-level exact factorization after radicand aggregation.  Under the
slightly stronger `gammaValid` guard for `18`, the aggregate radicand factor
has nonnegative square-root argument, so the rounded area is the exact Kahan
area times `sqrt (1 + theta)` and the two remaining local rounding factors. -/
theorem kahanHeronTraceStandardModel_area_eq_kahanArea_mul_sqrt_gamma9
    {fmt : FloatingPointFormat} {a b c : ℝ}
    {δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea : ℝ}
    (hside : kahanOrderedTriangleSides a b c)
    (htrace : kahanHeronTraceStandardModel fmt a b c
      δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea)
    (hγ : gammaValid (finiteFormatUnitRoundoffModel fmt) 18) :
    ∃ θ : ℝ,
      |θ| ≤ gamma (finiteFormatUnitRoundoffModel fmt) 9 ∧
        0 ≤ 1 + θ ∧
        finiteKahanHeronArea fmt a b c =
          kahanHeronArea a b c *
            Real.sqrt (1 + θ) * (1 + δsqrt) * (1 + δarea) := by
  have hγ9 : gammaValid (finiteFormatUnitRoundoffModel fmt) 9 :=
    gammaValid_mono (finiteFormatUnitRoundoffModel fmt) (by norm_num) hγ
  obtain ⟨θ, hθ, harea⟩ :=
    kahanHeronTraceStandardModel_area_eq_gamma9_radicand
      (fmt := fmt) (a := a) (b := b) (c := c)
      (δbc := δbc) (δbpc := δbpc) (δf1 := δf1) (δf2 := δf2)
      (δf3 := δf3) (δf4 := δf4) (δp12 := δp12) (δp123 := δp123)
      (δr := δr) (δsqrt := δsqrt) (δarea := δarea)
      hside htrace hγ9
  refine ⟨θ, hθ, ?_, ?_⟩
  · have hγ_lt_one :
        gamma (finiteFormatUnitRoundoffModel fmt) 9 < 1 := by
      simpa using gamma_lt_one (finiteFormatUnitRoundoffModel fmt) 9 hγ
    have hθ_lower : -gamma (finiteFormatUnitRoundoffModel fmt) 9 ≤ θ := by
      exact le_trans (neg_le_neg hθ) (neg_abs_le θ)
    linarith
  · have hR_nonneg : 0 ≤ kahanHeronRadicand a b c :=
      le_of_lt (kahanHeronRadicand_pos_of_kahanOrderedTriangleSides hside)
    rw [harea]
    rw [Real.sqrt_mul hR_nonneg]
    unfold kahanHeronArea
    ring

theorem sqrt_one_add_sub_one_abs_le_abs
    {θ : ℝ} (hθ : 0 ≤ 1 + θ) :
    |Real.sqrt (1 + θ) - 1| ≤ |θ| := by
  have hden_pos : 0 < Real.sqrt (1 + θ) + 1 := by
    linarith [Real.sqrt_nonneg (1 + θ)]
  have hden_ne : Real.sqrt (1 + θ) + 1 ≠ 0 := hden_pos.ne'
  have hrewrite :
      Real.sqrt (1 + θ) - 1 =
        θ / (Real.sqrt (1 + θ) + 1) := by
    field_simp [hden_ne]
    have hsq : Real.sqrt (1 + θ) * Real.sqrt (1 + θ) = 1 + θ := by
      simpa [sq] using Real.sq_sqrt hθ
    nlinarith
  rw [hrewrite, abs_div, abs_of_pos hden_pos]
  rw [div_le_iff₀ hden_pos]
  have hden_ge_one : 1 ≤ Real.sqrt (1 + θ) + 1 := by
    linarith [Real.sqrt_nonneg (1 + θ)]
  nlinarith [abs_nonneg θ]

theorem three_local_factors_abs_sub_one_le
    {e0 e1 e2 A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he0 : |e0| ≤ A) (he1 : |e1| ≤ B) (he2 : |e2| ≤ C) :
    |(1 + e0) * (1 + e1) * (1 + e2) - 1| ≤
      (1 + A) * (1 + B) * (1 + C) - 1 := by
  have hexpand :
      (1 + e0) * (1 + e1) * (1 + e2) - 1 =
        e0 + e1 + e2 + e0 * e1 + e0 * e2 + e1 * e2 + e0 * e1 * e2 := by
    ring
  rw [hexpand]
  have htri :
      |e0 + e1 + e2 + e0 * e1 + e0 * e2 + e1 * e2 + e0 * e1 * e2| ≤
        |e0| + |e1| + |e2| + |e0 * e1| + |e0 * e2| +
          |e1 * e2| + |e0 * e1 * e2| := by
    have h1 := abs_add_le e0 e1
    have h2 := abs_add_le (e0 + e1) e2
    have h3 := abs_add_le (e0 + e1 + e2) (e0 * e1)
    have h4 := abs_add_le (e0 + e1 + e2 + e0 * e1) (e0 * e2)
    have h5 := abs_add_le (e0 + e1 + e2 + e0 * e1 + e0 * e2) (e1 * e2)
    have h6 :=
      abs_add_le (e0 + e1 + e2 + e0 * e1 + e0 * e2 + e1 * e2)
        (e0 * e1 * e2)
    linarith
  have h01 : |e0 * e1| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul he0 he1 (abs_nonneg e1) hA
  have h02 : |e0 * e2| ≤ A * C := by
    rw [abs_mul]
    exact mul_le_mul he0 he2 (abs_nonneg e2) hA
  have h12 : |e1 * e2| ≤ B * C := by
    rw [abs_mul]
    exact mul_le_mul he1 he2 (abs_nonneg e2) hB
  have h012 : |e0 * e1 * e2| ≤ A * B * C := by
    rw [abs_mul]
    exact mul_le_mul h01 he2 (abs_nonneg e2) (mul_nonneg hA hB)
  calc
    |e0 + e1 + e2 + e0 * e1 + e0 * e2 + e1 * e2 + e0 * e1 * e2|
        ≤ |e0| + |e1| + |e2| + |e0 * e1| + |e0 * e2| +
          |e1 * e2| + |e0 * e1 * e2| := htri
    _ ≤ A + B + C + A * B + A * C + B * C + A * B * C := by
      nlinarith [he0, he1, he2, h01, h02, h12, h012]
    _ = (1 + A) * (1 + B) * (1 + C) - 1 := by
      ring

/-- Final closed-form C2.14 area relative-error bound.  The exact
factorization above reduces the rounded Kahan trace to three remaining local
factors: the square root of the aggregate `γ₉` radicand factor and the
square-root/final-division roundings.  Expanding those three factors gives the
readable radius `(1 + γ₉)(1 + u)^2 - 1`, a modest multiple of unit roundoff. -/
theorem kahanHeronTraceStandardModel_area_relError_le_gamma9_unitRoundoff
    {fmt : FloatingPointFormat} {a b c : ℝ}
    {δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea : ℝ}
    (hside : kahanOrderedTriangleSides a b c)
    (htrace : kahanHeronTraceStandardModel fmt a b c
      δbc δbpc δf1 δf2 δf3 δf4 δp12 δp123 δr δsqrt δarea)
    (hγ : gammaValid (finiteFormatUnitRoundoffModel fmt) 18) :
    relError (finiteKahanHeronArea fmt a b c) (kahanHeronArea a b c) ≤
      (1 + gamma (finiteFormatUnitRoundoffModel fmt) 9) *
        (1 + fmt.unitRoundoff) ^ 2 - 1 := by
  let fp := finiteFormatUnitRoundoffModel fmt
  have htrace_copy := htrace
  obtain ⟨θ, hθ, hθ_nonneg, harea⟩ :=
    kahanHeronTraceStandardModel_area_eq_kahanArea_mul_sqrt_gamma9
      (fmt := fmt) (a := a) (b := b) (c := c)
      (δbc := δbc) (δbpc := δbpc) (δf1 := δf1) (δf2 := δf2)
      (δf3 := δf3) (δf4 := δf4) (δp12 := δp12) (δp123 := δp123)
      (δr := δr) (δsqrt := δsqrt) (δarea := δarea)
      hside htrace hγ
  rcases htrace_copy with
    ⟨_hδbc, _hbc_eq, _hδbpc, _hbpc_eq, _hδf1, _hf1_eq,
      _hδf2, _hf2_eq, _hδf3, _hf3_eq, _hδf4, _hf4_eq,
      _hδp12, _hp12_eq, _hδp123, _hp123_eq, _hδr, _hr_eq,
      hδsqrt, _hsqrt_eq, hδarea, _harea_eq⟩
  have hγ9 : gammaValid fp 9 := by
    simpa [fp] using gammaValid_mono (finiteFormatUnitRoundoffModel fmt)
      (by norm_num : 9 ≤ 18) hγ
  have hγ9_nonneg : 0 ≤ gamma fp 9 := gamma_nonneg fp hγ9
  have hsqrt_bound :
      |Real.sqrt (1 + θ) - 1| ≤ gamma fp 9 := by
    exact (sqrt_one_add_sub_one_abs_le_abs hθ_nonneg).trans (by simpa [fp] using hθ)
  have hδsqrt_le : |δsqrt| ≤ fmt.unitRoundoff := le_of_lt hδsqrt
  have hδarea_le : |δarea| ≤ fmt.unitRoundoff := le_of_lt hδarea
  have hfactor :
      |(1 + (Real.sqrt (1 + θ) - 1)) * (1 + δsqrt) *
          (1 + δarea) - 1| ≤
        (1 + gamma fp 9) * (1 + fmt.unitRoundoff) *
          (1 + fmt.unitRoundoff) - 1 :=
    three_local_factors_abs_sub_one_le
      hγ9_nonneg fmt.unitRoundoff_nonneg
      hsqrt_bound hδsqrt_le hδarea_le
  let ρ := Real.sqrt (1 + θ) * (1 + δsqrt) * (1 + δarea) - 1
  have hwitness :
      signedRelErrorWitness
        (finiteKahanHeronArea fmt a b c) (kahanHeronArea a b c) ρ := by
    unfold signedRelErrorWitness
    rw [harea]
    dsimp [ρ]
    ring
  have hrel :
      relError (finiteKahanHeronArea fmt a b c) (kahanHeronArea a b c) =
        |ρ| :=
    relError_eq_abs_of_signedRelErrorWitness
      (kahanHeronArea_pos_of_kahanOrderedTriangleSides hside).ne' hwitness
  rw [hrel]
  dsimp [ρ]
  have hleft :
      Real.sqrt (1 + θ) * (1 + δsqrt) * (1 + δarea) - 1 =
        (1 + (Real.sqrt (1 + θ) - 1)) * (1 + δsqrt) *
          (1 + δarea) - 1 := by
    ring
  rw [hleft]
  calc
    |(1 + (Real.sqrt (1 + θ) - 1)) * (1 + δsqrt) *
        (1 + δarea) - 1|
        ≤ (1 + gamma fp 9) * (1 + fmt.unitRoundoff) *
          (1 + fmt.unitRoundoff) - 1 := hfactor
    _ = (1 + gamma (finiteFormatUnitRoundoffModel fmt) 9) *
        (1 + fmt.unitRoundoff) ^ 2 - 1 := by
      simp [fp]
      ring

/-- Direct finite-trace version of the Kahan/Heron area relative-error bound:
from the actual rounded operation trace and its finite-normal-range side
conditions, the computed area has relative error at most
`(1 + γ₉) * (1 + u)^2 - 1` relative to Kahan's exact parenthesized area. -/
theorem finiteKahanHeronArea_relError_le_gamma9_unitRoundoff_of_finiteNormalRange
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (hside : kahanOrderedTriangleSides a b c)
    (hbc : fmt.finiteNormalRange (b - c))
    (hbpc : fmt.finiteNormalRange (b + c))
    (hf1 : fmt.finiteNormalRange (a + finiteKahanHeronBplusC fmt b c))
    (hf2 : fmt.finiteNormalRange (c - (a - b)))
    (hf3 : fmt.finiteNormalRange (c + (a - b)))
    (hf4 : fmt.finiteNormalRange (a + finiteKahanHeronBC fmt b c))
    (hp12 : fmt.finiteNormalRange
      (finiteKahanHeronFactor1 fmt a b c * finiteKahanHeronFactor2 fmt a b c))
    (hp123 : fmt.finiteNormalRange
      (finiteKahanHeronProduct12 fmt a b c * finiteKahanHeronFactor3 fmt a b c))
    (hr : fmt.finiteNormalRange
      (finiteKahanHeronProduct123 fmt a b c * finiteKahanHeronFactor4 fmt a b c))
    (hr_nonneg : 0 ≤ finiteKahanHeronRadicand fmt a b c)
    (hsqrt : fmt.finiteNormalRange
      (Real.sqrt (finiteKahanHeronRadicand fmt a b c)))
    (harea : fmt.finiteNormalRange (finiteKahanHeronSqrt fmt a b c / 4))
    (hγ : gammaValid (finiteFormatUnitRoundoffModel fmt) 18) :
    relError (finiteKahanHeronArea fmt a b c) (kahanHeronArea a b c) ≤
      (1 + gamma (finiteFormatUnitRoundoffModel fmt) 9) *
        (1 + fmt.unitRoundoff) ^ 2 - 1 := by
  rcases finiteKahanHeronTrace_standardModel_lt_of_finiteNormalRange
      (fmt := fmt) (a := a) (b := b) (c := c)
      ha hb hside hbc hbpc hf1 hf2 hf3 hf4 hp12 hp123 hr
      hr_nonneg hsqrt harea with
    ⟨δbc, δbpc, δf1, δf2, δf3, δf4, δp12, δp123, δr, δsqrt, δarea, htrace⟩
  exact kahanHeronTraceStandardModel_area_relError_le_gamma9_unitRoundoff
    (fmt := fmt) (a := a) (b := b) (c := c)
    (δbc := δbc) (δbpc := δbpc) (δf1 := δf1) (δf2 := δf2)
    (δf3 := δf3) (δf4 := δf4) (δp12 := δp12) (δp123 := δp123)
    (δr := δr) (δsqrt := δsqrt) (δarea := δarea)
    hside htrace hγ

end

end NumStability
