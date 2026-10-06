-- Analysis/CancellationOfRoundingErrors.lean
--
-- Exact baselines for Higham Chapter 1, Section 1.14.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import NumStability.Analysis.Accumulation
import NumStability.Analysis.Error
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.Rounding

namespace NumStability

open Filter
open scoped Topology

/-!
# Cancellation of Rounding Errors

Higham Chapter 1, Section 1.14.1 compares two algorithms for evaluating
`(exp x - 1) / x`.  This file records the exact branch-level identity behind
Algorithm 2, the local rounded algebra through equation (1.9), and reusable
bridges for the source-shaped `3.5u` estimate.  Concrete exp/log routine
contracts and guard-digit instantiation are selected-model strengthening work;
machine-specific Table 1.2 traces are empirical replay artifacts unless a
full routine/display model is supplied.
-/

/-- Algorithm 1 from Higham §1.14.1, interpreted in exact real arithmetic. -/
noncomputable def expm1Algorithm1Exact (x : ℝ) : ℝ :=
  if x = 0 then 1 else (Real.exp x - 1) / x

/-- Algorithm 2 from Higham §1.14.1, interpreted in exact real arithmetic. -/
noncomputable def expm1Algorithm2Exact (x : ℝ) : ℝ :=
  let y := Real.exp x
  if y = 1 then 1 else (y - 1) / Real.log y

/-- Both exact algorithms return `1` at the removable singularity `x = 0`. -/
theorem expm1Algorithm1Exact_zero :
    expm1Algorithm1Exact 0 = 1 := by
  simp [expm1Algorithm1Exact]

/-- Algorithm 2 also returns `1` at `x = 0`, since `exp 0 = 1`. -/
theorem expm1Algorithm2Exact_zero :
    expm1Algorithm2Exact 0 = 1 := by
  simp [expm1Algorithm2Exact]

/-- With exact `exp` and `log`, Algorithm 2 computes the same branch function
as Algorithm 1. -/
theorem expm1Algorithm2Exact_eq_algorithm1Exact (x : ℝ) :
    expm1Algorithm2Exact x = expm1Algorithm1Exact x := by
  by_cases hx : x = 0
  · simp [expm1Algorithm2Exact, expm1Algorithm1Exact, hx]
  · have hy : Real.exp x ≠ 1 := by
      intro h
      exact hx ((Real.exp_eq_one_iff x).mp h)
    simp [expm1Algorithm2Exact, expm1Algorithm1Exact, hx, hy, Real.log_exp]

/-! ## Table 1.2 displayed finite data -/

/-- The `x` values displayed in Higham Table 1.2: row `i` is
`10^-(5+i)`, for `i = 0, ..., 11`. -/
noncomputable def expm1Table12X (i : Fin 12) : ℝ :=
  1 / (10 : ℝ) ^ (5 + i.val)

/-- The Algorithm 1 column displayed in Higham Table 1.2, encoded as exact
rational decimals.  These are source-table values, not a proof of MATLAB's
hidden floating-point execution path. -/
noncomputable def expm1Table12Algorithm1 (i : Fin 12) : ℝ :=
  match i.val with
  | 0 => 1000005000006965 / (10 : ℝ) ^ 15
  | 1 => 1000000499962184 / (10 : ℝ) ^ 15
  | 2 => 1000000049433680 / (10 : ℝ) ^ 15
  | 3 => 9999999939225290 / (10 : ℝ) ^ 16
  | 4 => 1000000082740371 / (10 : ℝ) ^ 15
  | 5 => 1000000082740371 / (10 : ℝ) ^ 15
  | 6 => 1000000082740371 / (10 : ℝ) ^ 15
  | 7 => 1000088900582341 / (10 : ℝ) ^ 15
  | 8 => 9992007221626408 / (10 : ℝ) ^ 16
  | 9 => 9992007221626408 / (10 : ℝ) ^ 16
  | 10 => 1110223024625156 / (10 : ℝ) ^ 15
  | _ => 0

/-- The Algorithm 2 column displayed in Higham Table 1.2.  The final
`10^-16` row has no Algorithm 2 entry in the source table, hence `none`. -/
noncomputable def expm1Table12Algorithm2 (i : Fin 12) : Option ℝ :=
  match i.val with
  | 0 => some (1000005000016667 / (10 : ℝ) ^ 15)
  | 1 => some (1000000500000167 / (10 : ℝ) ^ 15)
  | 2 => some (1000000050000002 / (10 : ℝ) ^ 15)
  | 3 => some (1000000005000000 / (10 : ℝ) ^ 15)
  | 4 => some (1000000000500000 / (10 : ℝ) ^ 15)
  | 5 => some (1000000000050000 / (10 : ℝ) ^ 15)
  | 6 => some (1000000000005000 / (10 : ℝ) ^ 15)
  | 7 => some (1000000000000500 / (10 : ℝ) ^ 15)
  | 8 => some (1000000000000050 / (10 : ℝ) ^ 15)
  | 9 => some (1000000000000005 / (10 : ℝ) ^ 15)
  | 10 => some (1000000000000000 / (10 : ℝ) ^ 15)
  | _ => none

/-- The last digit that the source text says should appear in the Algorithm 2
`x = 10^-15` row. -/
noncomputable def expm1Table12Algorithm2TenPowNeg15Corrected : ℝ :=
  1000000000000001 / (10 : ℝ) ^ 15

/-- The displayed `x` column is exactly the source sequence
`10^-5, ..., 10^-16`. -/
theorem expm1Table12_x_rows :
    expm1Table12X ⟨0, by norm_num⟩ = 1 / (10 : ℝ) ^ 5 ∧
    expm1Table12X ⟨1, by norm_num⟩ = 1 / (10 : ℝ) ^ 6 ∧
    expm1Table12X ⟨2, by norm_num⟩ = 1 / (10 : ℝ) ^ 7 ∧
    expm1Table12X ⟨3, by norm_num⟩ = 1 / (10 : ℝ) ^ 8 ∧
    expm1Table12X ⟨4, by norm_num⟩ = 1 / (10 : ℝ) ^ 9 ∧
    expm1Table12X ⟨5, by norm_num⟩ = 1 / (10 : ℝ) ^ 10 ∧
    expm1Table12X ⟨6, by norm_num⟩ = 1 / (10 : ℝ) ^ 11 ∧
    expm1Table12X ⟨7, by norm_num⟩ = 1 / (10 : ℝ) ^ 12 ∧
    expm1Table12X ⟨8, by norm_num⟩ = 1 / (10 : ℝ) ^ 13 ∧
    expm1Table12X ⟨9, by norm_num⟩ = 1 / (10 : ℝ) ^ 14 ∧
    expm1Table12X ⟨10, by norm_num⟩ = 1 / (10 : ℝ) ^ 15 ∧
    expm1Table12X ⟨11, by norm_num⟩ = 1 / (10 : ℝ) ^ 16 := by
  norm_num [expm1Table12X]

/-- Exact rational transcription of the Algorithm 1 column in Table 1.2. -/
theorem expm1Table12_algorithm1_rows :
    expm1Table12Algorithm1 ⟨0, by norm_num⟩ =
        1000005000006965 / (10 : ℝ) ^ 15 ∧
    expm1Table12Algorithm1 ⟨1, by norm_num⟩ =
        1000000499962184 / (10 : ℝ) ^ 15 ∧
    expm1Table12Algorithm1 ⟨2, by norm_num⟩ =
        1000000049433680 / (10 : ℝ) ^ 15 ∧
    expm1Table12Algorithm1 ⟨3, by norm_num⟩ =
        9999999939225290 / (10 : ℝ) ^ 16 ∧
    expm1Table12Algorithm1 ⟨4, by norm_num⟩ =
        1000000082740371 / (10 : ℝ) ^ 15 ∧
    expm1Table12Algorithm1 ⟨5, by norm_num⟩ =
        1000000082740371 / (10 : ℝ) ^ 15 ∧
    expm1Table12Algorithm1 ⟨6, by norm_num⟩ =
        1000000082740371 / (10 : ℝ) ^ 15 ∧
    expm1Table12Algorithm1 ⟨7, by norm_num⟩ =
        1000088900582341 / (10 : ℝ) ^ 15 ∧
    expm1Table12Algorithm1 ⟨8, by norm_num⟩ =
        9992007221626408 / (10 : ℝ) ^ 16 ∧
    expm1Table12Algorithm1 ⟨9, by norm_num⟩ =
        9992007221626408 / (10 : ℝ) ^ 16 ∧
    expm1Table12Algorithm1 ⟨10, by norm_num⟩ =
        1110223024625156 / (10 : ℝ) ^ 15 ∧
    expm1Table12Algorithm1 ⟨11, by norm_num⟩ = 0 := by
  norm_num [expm1Table12Algorithm1]

/-- Exact rational transcription of the Algorithm 2 column in Table 1.2,
including the missing final table entry. -/
theorem expm1Table12_algorithm2_rows :
    expm1Table12Algorithm2 ⟨0, by norm_num⟩ =
        some (1000005000016667 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨1, by norm_num⟩ =
        some (1000000500000167 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨2, by norm_num⟩ =
        some (1000000050000002 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨3, by norm_num⟩ =
        some (1000000005000000 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨4, by norm_num⟩ =
        some (1000000000500000 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨5, by norm_num⟩ =
        some (1000000000050000 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨6, by norm_num⟩ =
        some (1000000000005000 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨7, by norm_num⟩ =
        some (1000000000000500 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨8, by norm_num⟩ =
        some (1000000000000050 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨9, by norm_num⟩ =
        some (1000000000000005 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨10, by norm_num⟩ =
        some (1000000000000000 / (10 : ℝ) ^ 15) ∧
    expm1Table12Algorithm2 ⟨11, by norm_num⟩ = none := by
  norm_num [expm1Table12Algorithm2]

/-- The source note after Table 1.2 says that the Algorithm 2 value for
`x = 10^-15` should have last digit `1`.  The corrected displayed decimal is
exactly one unit in the last displayed place above the table entry. -/
theorem expm1Table12_algorithm2_ten_pow_neg15_last_digit_correction :
    expm1Table12Algorithm2 ⟨10, by norm_num⟩ = some (1 : ℝ) ∧
    expm1Table12Algorithm2TenPowNeg15Corrected =
      1 + 1 / (10 : ℝ) ^ 15 ∧
    expm1Table12Algorithm2TenPowNeg15Corrected - 1 =
      1 / (10 : ℝ) ^ 15 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [expm1Table12Algorithm2]
    rfl
  · norm_num [expm1Table12Algorithm2TenPowNeg15Corrected]
  · norm_num [expm1Table12Algorithm2TenPowNeg15Corrected]

/-- Source-shaped finite numbers in the page-23 single-precision example:
`1.19209290e-7 / 1.19209282e-7` reduces to this exact rational ratio when the
displayed decimals are read literally. -/
theorem expm1Page23_displayed_single_precision_ratio :
    (119209290 / (10 : ℝ) ^ 15) / (119209282 / (10 : ℝ) ^ 15) =
      59604645 / (59604641 : ℝ) := by
  norm_num

/-- The exact-arithmetic comparison line on page 23, read as literal displayed
decimals, similarly reduces to a rational ratio. -/
theorem expm1Page23_displayed_exact_arithmetic_ratio :
    (900000041 / (10 : ℝ) ^ 16) / (900000001 / (10 : ℝ) ^ 16) =
      900000041 / (900000001 : ℝ) := by
  norm_num

/-! ## Modeled floating-point algebra for Algorithm 2 -/

/-- The rounded core of Algorithm 2 after the rounded exponential and rounded
logarithm have already been supplied: subtract `1` from `yhat`, then divide by
`logHat`. -/
noncomputable def expm1Algorithm2RoundedCore
    (fp : FPModel) (yhat logHat : ℝ) : ℝ :=
  fp.fl_div (fp.fl_sub yhat 1) logHat

/-- The slowly varying ratio `g(y) = (y-1)/log y` used in Higham §1.14.1. -/
noncomputable def expm1LogRatio (y : ℝ) : ℝ :=
  (y - 1) / Real.log y

/-- Away from the removable singularity, the slow ratio at `exp x` is exactly
the source function `(exp x - 1) / x` used by Algorithm 1. -/
theorem expm1LogRatio_exp_eq_algorithm1Exact_of_ne_zero
    {x : ℝ} (hx : x ≠ 0) :
    expm1LogRatio (Real.exp x) = expm1Algorithm1Exact x := by
  simp [expm1LogRatio, expm1Algorithm1Exact, hx, Real.log_exp]

/-- The ratio `g(y) = (y-1)/log y` has a removable singularity at `y = 1`:
as `y` tends to `1` through `y ≠ 1`, `g(y)` tends to `1`. -/
theorem expm1LogRatio_tendsto_one :
    Tendsto expm1LogRatio (𝓝[≠] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hlogDeriv : HasDerivAt Real.log (1 : ℝ) (1 : ℝ) := by
    simpa using (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0))
  have hslope : Tendsto (slope Real.log (1 : ℝ)) (𝓝[≠] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    hlogDeriv.tendsto_slope
  have hinv : Tendsto (fun y : ℝ => (slope Real.log (1 : ℝ) y)⁻¹)
      (𝓝[≠] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using hslope.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y _hy
  unfold expm1LogRatio
  simp [slope, Real.log_one, div_eq_mul_inv, mul_comm]

/-- The denominator remainder in the source expansion
`log(1+v) = v - v^2/2 + v * R(v)`. -/
noncomputable def expm1LogRatioDenRemainder (v : ℝ) : ℝ :=
  (Real.log (1 + v) - (v - v ^ 2 / 2)) / v

/-- Higham §1.14.1's page-24 expansion
`log(1+v) = v - v^2/2 + O(v^3)`, with an explicit remainder bound. -/
theorem expm1Log_one_add_sub_linear_quadratic_abs_le
    {v : ℝ} (hv : |v| < 1) :
    |Real.log (1 + v) - (v - v ^ 2 / 2)| ≤
      |v| ^ 3 * (1 - |v|)⁻¹ / 3 := by
  have hvpos_nonneg : 0 ≤ 1 + v := by
    have hlt := (abs_lt.mp hv).1
    linarith
  have hcomplex :=
    Complex.norm_log_sub_logTaylor_le (n := 2) (z := (v : ℂ)) (by simpa using hv)
  have hpoly : Complex.logTaylor 3 (v : ℂ) = (v - v ^ 2 / 2 : ℝ) := by
    simp [Complex.logTaylor, Finset.sum_range_succ]
    ring_nf
  have hlogcast : Complex.log (1 + (v : ℂ)) = (Real.log (1 + v) : ℂ) := by
    rw [show (1 + (v : ℂ)) = ((1 + v : ℝ) : ℂ) by norm_num]
    exact (Complex.ofReal_log hvpos_nonneg).symm
  norm_num at hcomplex
  rw [hpoly, hlogcast] at hcomplex
  have hnorm :
      ‖(Real.log (1 + v) : ℂ) - ((v - v ^ 2 / 2 : ℝ) : ℂ)‖ =
        |Real.log (1 + v) - (v - v ^ 2 / 2)| := by
    rw [← Complex.ofReal_sub]
    rw [Complex.norm_real, Real.norm_eq_abs]
  rwa [hnorm] at hcomplex

/-- Dividing the log Taylor remainder by `v` gives the `O(v^2)` denominator
remainder used in `g(1+v) = 1/(1 - v/2 + O(v^2))`. -/
theorem expm1LogRatioDenRemainder_abs_le
    {v : ℝ} (hv : |v| < 1) (hv0 : v ≠ 0) :
    |expm1LogRatioDenRemainder v| ≤
      |v| ^ 2 * (1 - |v|)⁻¹ / 3 := by
  unfold expm1LogRatioDenRemainder
  rw [abs_div]
  have hmain := expm1Log_one_add_sub_linear_quadratic_abs_le hv
  have hstep :
      |Real.log (1 + v) - (v - v ^ 2 / 2)| / |v| ≤
        (|v| ^ 3 * (1 - |v|)⁻¹ / 3) / |v| := by
    exact div_le_div_of_nonneg_right hmain (abs_nonneg v)
  refine le_trans hstep ?_
  have habs_pos : 0 < |v| := abs_pos.mpr hv0
  have hcalc :
      (|v| ^ 3 * (1 - |v|)⁻¹ / 3) / |v| =
        |v| ^ 2 * (1 - |v|)⁻¹ / 3 := by
    field_simp [habs_pos.ne']
  rw [hcalc]

/-- The exact reciprocal form behind the source line
`g(1+v)=1/(1-v/2+O(v^2))`, with the `O(v^2)` term named above. -/
theorem expm1LogRatio_one_add_eq_inv_one_sub_half_add_remainder
    {v : ℝ} (hvpos : 0 < 1 + v) (hv0 : v ≠ 0) :
    expm1LogRatio (1 + v) =
      (1 - v / 2 + expm1LogRatioDenRemainder v)⁻¹ := by
  have hne_one : 1 + v ≠ 1 := by
    intro h
    apply hv0
    linarith
  have hlog_ne : Real.log (1 + v) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hvpos hne_one
  unfold expm1LogRatio expm1LogRatioDenRemainder
  field_simp [hv0, hlog_ne]
  ring

/-- A quantitative version of the source expansion
`g(1+v) = 1 + v/2 + O(v^2)` on a small punctured neighborhood of `0`. -/
theorem expm1LogRatio_one_add_sub_one_add_half_abs_le
    {v : ℝ} (hv : |v| ≤ (1 / 2 : ℝ)) (hv0 : v ≠ 0) :
    |expm1LogRatio (1 + v) - (1 + v / 2)| ≤ 3 * |v| ^ 2 := by
  let R := expm1LogRatioDenRemainder v
  let d := 1 - v / 2 + R
  have hvlt1 : |v| < 1 := by
    linarith [abs_nonneg v]
  have hvpos : 0 < 1 + v := by
    have hv_lower := (abs_le.mp hv).1
    linarith
  have hratio : expm1LogRatio (1 + v) = d⁻¹ := by
    simpa [d, R] using
      (expm1LogRatio_one_add_eq_inv_one_sub_half_add_remainder (v := v) hvpos hv0)
  have hRraw : |R| ≤ |v| ^ 2 * (1 - |v|)⁻¹ / 3 := by
    simpa [R] using expm1LogRatioDenRemainder_abs_le hvlt1 hv0
  have hden_pos : 0 < 1 - |v| := by
    linarith [abs_nonneg v]
  have hinv_le_two : (1 - |v|)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ hden_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
    linarith
  have hR2 : |R| ≤ (2 / 3 : ℝ) * |v| ^ 2 := by
    have hmul : |v| ^ 2 * (1 - |v|)⁻¹ ≤ |v| ^ 2 * (2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hinv_le_two (sq_nonneg |v|)
    have hdiv : |v| ^ 2 * (1 - |v|)⁻¹ / 3 ≤ |v| ^ 2 * (2 : ℝ) / 3 := by
      exact div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 3)
    calc
      |R| ≤ |v| ^ 2 * (1 - |v|)⁻¹ / 3 := hRraw
      _ ≤ |v| ^ 2 * (2 : ℝ) / 3 := hdiv
      _ = (2 / 3 : ℝ) * |v| ^ 2 := by ring
  have hv_sq_le_quarter : |v| ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (|v| - (1 / 2 : ℝ)), abs_nonneg v, hv]
  have hRsmall : |R| ≤ (1 / 6 : ℝ) := by
    calc
      |R| ≤ (2 / 3 : ℝ) * |v| ^ 2 := hR2
      _ ≤ (2 / 3 : ℝ) * (1 / 4 : ℝ) := by nlinarith
      _ = (1 / 6 : ℝ) := by norm_num
  have hRlower : -(1 / 6 : ℝ) ≤ R := by
    have hneg := neg_abs_le R
    linarith
  have hvterm_lower : -(1 / 4 : ℝ) ≤ -v / 2 := by
    have hvle : v ≤ |v| := le_abs_self v
    linarith
  have hd_lower : (1 / 2 : ℝ) ≤ d := by
    dsimp [d]
    linarith
  have hd_abs_lower : (1 / 2 : ℝ) ≤ |d| := by
    have hd_nonneg : 0 ≤ d := by linarith
    rw [abs_of_nonneg hd_nonneg]
    exact hd_lower
  have hd_abs_pos : 0 < |d| := by linarith
  have hd_ne : d ≠ 0 := abs_pos.mp hd_abs_pos
  have hinv_abs : |d⁻¹| ≤ (2 : ℝ) := by
    rw [abs_inv]
    rw [inv_le_comm₀ hd_abs_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
    exact hd_abs_lower
  have hvhalf_abs : |v / 2| ≤ (1 / 4 : ℝ) := by
    rw [abs_div]
    norm_num
    linarith
  have hone_plus : |1 + v / 2| ≤ (5 / 4 : ℝ) := by
    calc
      |1 + v / 2| ≤ |(1 : ℝ)| + |v / 2| := abs_add_le 1 (v / 2)
      _ ≤ 1 + (1 / 4 : ℝ) := by nlinarith
      _ = (5 / 4 : ℝ) := by norm_num
  have hnum : |v ^ 2 / 4 - R * (1 + v / 2)| ≤ (3 / 2 : ℝ) * |v| ^ 2 := by
    have htri :
        |v ^ 2 / 4 - R * (1 + v / 2)| ≤ |v ^ 2 / 4| + |R * (1 + v / 2)| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (v ^ 2 / 4) (-(R * (1 + v / 2)))
    have hterm1 : |v ^ 2 / 4| = |v| ^ 2 / 4 := by
      rw [abs_div, abs_pow]
      norm_num
    have hterm2 :
        |R * (1 + v / 2)| ≤ ((2 / 3 : ℝ) * |v| ^ 2) * (5 / 4 : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hR2 hone_plus (abs_nonneg (1 + v / 2))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) (sq_nonneg |v|))
    calc
      |v ^ 2 / 4 - R * (1 + v / 2)| ≤
          |v ^ 2 / 4| + |R * (1 + v / 2)| := htri
      _ ≤ |v| ^ 2 / 4 + ((2 / 3 : ℝ) * |v| ^ 2) * (5 / 4 : ℝ) := by
        exact add_le_add (le_of_eq hterm1) hterm2
      _ ≤ (3 / 2 : ℝ) * |v| ^ 2 := by
        nlinarith [sq_nonneg |v|]
  have hdiff :
      d⁻¹ - (1 + v / 2) = d⁻¹ * (v ^ 2 / 4 - R * (1 + v / 2)) := by
    field_simp [hd_ne]
    ring
  calc
    |expm1LogRatio (1 + v) - (1 + v / 2)| =
        |d⁻¹ - (1 + v / 2)| := by rw [hratio]
    _ = |d⁻¹ * (v ^ 2 / 4 - R * (1 + v / 2))| := by rw [hdiff]
    _ = |d⁻¹| * |v ^ 2 / 4 - R * (1 + v / 2)| := abs_mul _ _
    _ ≤ (2 : ℝ) * ((3 / 2 : ℝ) * |v| ^ 2) := by
      exact mul_le_mul hinv_abs hnum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    _ = 3 * |v| ^ 2 := by ring

/-- The slow ratio is close to `1` near the removable singularity.  This is
the quantitative substrate for replacing `delta/2` by `g(y)*delta/2`. -/
theorem expm1LogRatio_one_add_sub_one_abs_le
    {v : ℝ} (hv : |v| ≤ (1 / 2 : ℝ)) (hv0 : v ≠ 0) :
    |expm1LogRatio (1 + v) - 1| ≤ |v| / 2 + 3 * |v| ^ 2 := by
  let E := expm1LogRatio (1 + v) - (1 + v / 2)
  have hE : |E| ≤ 3 * |v| ^ 2 := by
    simpa [E] using expm1LogRatio_one_add_sub_one_add_half_abs_le hv hv0
  have hvhalf : |v / 2| = |v| / 2 := by
    rw [abs_div]
    norm_num
  have hidentity :
      expm1LogRatio (1 + v) - 1 = E + v / 2 := by
    dsimp [E]
    ring
  calc
    |expm1LogRatio (1 + v) - 1| = |E + v / 2| := by rw [hidentity]
    _ ≤ |E| + |v / 2| := abs_add_le E (v / 2)
    _ ≤ 3 * |v| ^ 2 + |v| / 2 := add_le_add hE (le_of_eq hvhalf)
    _ = |v| / 2 + 3 * |v| ^ 2 := by ring

/-- A `y`-form of `expm1LogRatio_one_add_sub_one_abs_le`. -/
theorem expm1LogRatio_sub_one_abs_le
    {y : ℝ} (hy : |y - 1| ≤ (1 / 2 : ℝ)) (hy0 : y ≠ 1) :
    |expm1LogRatio y - 1| ≤ |y - 1| / 2 + 3 * |y - 1| ^ 2 := by
  have hv0 : y - 1 ≠ 0 := by
    intro h
    apply hy0
    linarith
  have harg : 1 + (y - 1) = y := by ring
  simpa [harg] using
    (expm1LogRatio_one_add_sub_one_abs_le (v := y - 1) hy hv0)

/-- Radius lower bound for the slow ratio.  This turns the local expansion
`g(y) = 1 + O(|y-1|)` into denominator control for the later Algorithm 2
relative-error bounds. -/
theorem expm1LogRatio_abs_ge_one_sub_radius_bound
    {y r : ℝ}
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1)
    (hyRadius : |y - 1| ≤ r)
    (hr_nonneg : 0 ≤ r) :
    1 - (r / 2 + 3 * r ^ 2) ≤ |expm1LogRatio y| := by
  let a := |y - 1|
  let B := r / 2 + 3 * r ^ 2
  have ha_nonneg : 0 ≤ a := abs_nonneg (y - 1)
  have ha_le_r : a ≤ r := by
    simpa [a] using hyRadius
  have ha_sq : a ^ 2 ≤ r ^ 2 := by
    nlinarith [ha_le_r, ha_nonneg, hr_nonneg]
  have hB :
      a / 2 + 3 * a ^ 2 ≤ B := by
    have hhalf : a / 2 ≤ r / 2 := by linarith
    have hquad : 3 * a ^ 2 ≤ 3 * r ^ 2 := by nlinarith
    dsimp [B]
    exact add_le_add hhalf hquad
  have hclose :
      |expm1LogRatio y - 1| ≤ B := by
    exact le_trans (expm1LogRatio_sub_one_abs_le hySmall hy0) (by simpa [a, B] using hB)
  have hbounds := abs_sub_le_iff.mp hclose
  have hge :
      1 - B ≤ expm1LogRatio y := by
    linarith
  exact le_trans hge (le_abs_self (expm1LogRatio y))

/-- Convenient small-radius denominator bound for Algorithm 2: within radius
`1/3` of the removable singularity, the slow ratio has magnitude at least
`1/2`. -/
theorem expm1LogRatio_abs_ge_half_of_radius
    {y r : ℝ}
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1)
    (hyRadius : |y - 1| ≤ r)
    (hr_nonneg : 0 ≤ r)
    (hr_le : r ≤ (1 / 3 : ℝ)) :
    (1 / 2 : ℝ) ≤ |expm1LogRatio y| := by
  have hden :=
    expm1LogRatio_abs_ge_one_sub_radius_bound
      (y := y) (r := r) hySmall hy0 hyRadius hr_nonneg
  have hB : r / 2 + 3 * r ^ 2 ≤ (1 / 2 : ℝ) := by
    nlinarith [hr_nonneg, hr_le]
  linarith

/-- The slow ratio is also close to the nearby argument `1+v`. -/
theorem expm1LogRatio_one_add_self_sub_abs_le
    {v : ℝ} (hv : |v| ≤ (1 / 2 : ℝ)) (hv0 : v ≠ 0) :
    |(1 + v) - expm1LogRatio (1 + v)| ≤ |v| / 2 + 3 * |v| ^ 2 := by
  let E := expm1LogRatio (1 + v) - (1 + v / 2)
  have hE : |E| ≤ 3 * |v| ^ 2 := by
    simpa [E] using expm1LogRatio_one_add_sub_one_add_half_abs_le hv hv0
  have hvhalf : |v / 2| = |v| / 2 := by
    rw [abs_div]
    norm_num
  have hidentity :
      (1 + v) - expm1LogRatio (1 + v) = v / 2 - E := by
    dsimp [E]
    ring
  have htri : |v / 2 - E| ≤ |v / 2| + |E| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le (v / 2) (-E)
  calc
    |(1 + v) - expm1LogRatio (1 + v)| = |v / 2 - E| := by rw [hidentity]
    _ ≤ |v / 2| + |E| := htri
    _ ≤ |v| / 2 + 3 * |v| ^ 2 := add_le_add (le_of_eq hvhalf) hE

/-- A `y`-form of `expm1LogRatio_one_add_self_sub_abs_le`. -/
theorem expm1LogRatio_self_sub_abs_le
    {y : ℝ} (hy : |y - 1| ≤ (1 / 2 : ℝ)) (hy0 : y ≠ 1) :
    |y - expm1LogRatio y| ≤ |y - 1| / 2 + 3 * |y - 1| ^ 2 := by
  have hv0 : y - 1 ≠ 0 := by
    intro h
    apply hy0
    linarith
  have harg : 1 + (y - 1) = y := by ring
  simpa [harg] using
    (expm1LogRatio_one_add_self_sub_abs_le (v := y - 1) hy hv0)

/-- A two-point version of the slow-ratio expansion.  This is the exact
real-analysis substrate for the source estimate
`g(yhat) - g(y) ≈ (yhat - y)/2` when `yhat = 1+w` and `y = 1+v`. -/
theorem expm1LogRatio_one_add_diff_sub_half_abs_le
    {v w : ℝ}
    (hv : |v| ≤ (1 / 2 : ℝ)) (hw : |w| ≤ (1 / 2 : ℝ))
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    |(expm1LogRatio (1 + w) - expm1LogRatio (1 + v)) - (w - v) / 2| ≤
      3 * |w| ^ 2 + 3 * |v| ^ 2 := by
  let Ew := expm1LogRatio (1 + w) - (1 + w / 2)
  let Ev := expm1LogRatio (1 + v) - (1 + v / 2)
  have hwexp : |Ew| ≤ 3 * |w| ^ 2 := by
    simpa [Ew] using expm1LogRatio_one_add_sub_one_add_half_abs_le hw hw0
  have hvexp : |Ev| ≤ 3 * |v| ^ 2 := by
    simpa [Ev] using expm1LogRatio_one_add_sub_one_add_half_abs_le hv hv0
  have hidentity :
      (expm1LogRatio (1 + w) - expm1LogRatio (1 + v)) - (w - v) / 2 =
        Ew - Ev := by
    simp [Ew, Ev]
    ring
  have htri : |Ew - Ev| ≤ |Ew| + |Ev| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le Ew (-Ev)
  calc
    |(expm1LogRatio (1 + w) - expm1LogRatio (1 + v)) - (w - v) / 2| =
        |Ew - Ev| := by rw [hidentity]
    _ ≤ |Ew| + |Ev| := htri
    _ ≤ 3 * |w| ^ 2 + 3 * |v| ^ 2 := add_le_add hwexp hvexp

/-- Substitute the rounded exponential relation `yhat = y*(1+delta)` into the
two-point slow-ratio comparison.  This closes the exact algebra behind
`(yhat-y)/2 = y*delta/2`. -/
theorem expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le
    {y delta : ℝ}
    (hy : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhat : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1) :
    |(expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) - y * delta / 2| ≤
      3 * |y * (1 + delta) - 1| ^ 2 + 3 * |y - 1| ^ 2 := by
  have hbase0 : y - 1 ≠ 0 := by
    intro h
    apply hy0
    linarith
  have hhat0 : y * (1 + delta) - 1 ≠ 0 := by
    intro h
    apply hyhat0
    linarith
  have hcomp := expm1LogRatio_one_add_diff_sub_half_abs_le
    (v := y - 1) (w := y * (1 + delta) - 1) hy hyhat hbase0 hhat0
  have harg1 : 1 + (y * (1 + delta) - 1) = y * (1 + delta) := by ring
  have harg2 : 1 + (y - 1) = y := by ring
  have hdiff : y * (1 + delta) - y = y * delta := by ring
  simpa [harg1, harg2, hdiff, abs_sq] using hcomp

/-- Replace `y*delta/2` by `delta/2` in the slow-ratio perturbation comparison.
The extra term records the exact price of using `y ≈ 1`. -/
theorem expm1LogRatio_mul_one_add_delta_diff_sub_delta_half_abs_le
    {y delta : ℝ}
    (hy : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhat : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1) :
    |(expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) - delta / 2| ≤
      3 * |y * (1 + delta) - 1| ^ 2 + 3 * |y - 1| ^ 2 +
        |y - 1| * |delta| / 2 := by
  have hmain :=
    expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le
      hy hyhat hy0 hyhat0
  have hcorr : |y * delta / 2 - delta / 2| = |y - 1| * |delta| / 2 := by
    rw [← sub_div]
    have hnum : y * delta - delta = (y - 1) * delta := by ring
    rw [hnum, abs_div, abs_mul]
    norm_num
  have hsplit :
      (expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) - delta / 2 =
        ((expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) - y * delta / 2) +
          (y * delta / 2 - delta / 2) := by
    ring
  rw [hsplit]
  calc
    |((expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) - y * delta / 2) +
        (y * delta / 2 - delta / 2)| ≤
        |(expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) - y * delta / 2| +
          |y * delta / 2 - delta / 2| := abs_add_le _ _
    _ ≤ (3 * |y * (1 + delta) - 1| ^ 2 + 3 * |y - 1| ^ 2) +
          |y - 1| * |delta| / 2 := add_le_add hmain (le_of_eq hcorr)
    _ = 3 * |y * (1 + delta) - 1| ^ 2 + 3 * |y - 1| ^ 2 +
          |y - 1| * |delta| / 2 := by ring

/-- Replace the linearized term by `g(y)*delta/2`.  This packages the last
exact slow-ratio substitution in Higham's page-24 estimate before one charges
the concrete floating-point `exp`/`log` and guard-digit contracts. -/
theorem expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le
    {y delta : ℝ}
    (hy : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhat : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1) :
    |(expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) -
        expm1LogRatio y * delta / 2| ≤
      3 * |y * (1 + delta) - 1| ^ 2 + 3 * |y - 1| ^ 2 +
        (|y - 1| / 2 + 3 * |y - 1| ^ 2) * |delta| / 2 := by
  have hmain :=
    expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le
      hy hyhat hy0 hyhat0
  have hclose := expm1LogRatio_self_sub_abs_le hy hy0
  have hcorr_eq :
      |y * delta / 2 - expm1LogRatio y * delta / 2| =
        |y - expm1LogRatio y| * |delta| / 2 := by
    rw [← sub_div]
    have hnum : y * delta - expm1LogRatio y * delta =
        (y - expm1LogRatio y) * delta := by ring
    rw [hnum, abs_div, abs_mul]
    norm_num
  have hcorr_le :
      |y * delta / 2 - expm1LogRatio y * delta / 2| ≤
        (|y - 1| / 2 + 3 * |y - 1| ^ 2) * |delta| / 2 := by
    rw [hcorr_eq]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hclose (abs_nonneg delta))
      (by norm_num : (0 : ℝ) ≤ 2)
  have hsplit :
      (expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) -
          expm1LogRatio y * delta / 2 =
        ((expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) -
          y * delta / 2) +
          (y * delta / 2 - expm1LogRatio y * delta / 2) := by
    ring
  rw [hsplit]
  calc
    |((expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) -
          y * delta / 2) +
        (y * delta / 2 - expm1LogRatio y * delta / 2)| ≤
        |(expm1LogRatio (y * (1 + delta)) - expm1LogRatio y) -
          y * delta / 2| +
          |y * delta / 2 - expm1LogRatio y * delta / 2| := abs_add_le _ _
    _ ≤ (3 * |y * (1 + delta) - 1| ^ 2 + 3 * |y - 1| ^ 2) +
          (|y - 1| / 2 + 3 * |y - 1| ^ 2) * |delta| / 2 :=
        add_le_add hmain hcorr_le
    _ = 3 * |y * (1 + delta) - 1| ^ 2 + 3 * |y - 1| ^ 2 +
          (|y - 1| / 2 + 3 * |y - 1| ^ 2) * |delta| / 2 := by ring

/-- If the rounded exponential value `yhat = exp x * (1 + delta)` is exactly
`1`, then the source identity `x = -log(1+delta)` follows. -/
theorem expm1Algorithm2_yhat_eq_one_implies_x_eq_neg_log_one_add_delta
    {x delta : ℝ} (hy : Real.exp x * (1 + delta) = 1) :
    x = - Real.log (1 + delta) := by
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have hdelta_pos : 0 < 1 + delta := by
    nlinarith
  have hdelta_eq : 1 + delta = Real.exp (-x) := by
    have h := congrArg (fun t : ℝ => t / Real.exp x) hy
    field_simp [hexp_pos.ne'] at h
    rw [Real.exp_neg]
    field_simp [hexp_pos.ne']
    linarith
  have hlog : Real.log (1 + delta) = -x := by
    rw [hdelta_eq, Real.log_exp]
  linarith

/-- Higham §1.14.1 equation (1.9), isolated from the later asymptotic
`3.5u` argument.  The rounded logarithm is supplied as
`logHat = log(yhat) * (1 + epsLog)`, while the rounded subtraction and final
division are discharged by the local `FPModel` laws. -/
theorem expm1Algorithm2RoundedCore_eq_source_1_9
    (fp : FPModel) (yhat logHat epsLog : ℝ)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp yhat logHat =
          ((yhat - 1) * (1 + epsSub)) /
            (Real.log yhat * (1 + epsLog)) * (1 + epsDiv) := by
  obtain ⟨epsSub, hepsSub, hsub⟩ := fp.model_sub yhat 1
  obtain ⟨epsDiv, hepsDiv, hdiv⟩ :=
    fp.model_div (fp.fl_sub yhat 1) logHat hlogHat
  refine ⟨epsSub, epsDiv, hepsSub, hepsLog, hepsDiv, ?_⟩
  unfold expm1Algorithm2RoundedCore
  rw [hdiv, hsub, hlog]

/-- Equation (1.9) when the subtraction `yhat - 1` is known to be exact.
This isolates the guard-digit instantiation point: the subtraction factor can
be taken to have `epsSub = 0`, while the rounded logarithm and final division
remain modeled by their usual relative-error factors. -/
theorem expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub
    (fp : FPModel) (yhat logHat epsLog : ℝ)
    (hsubExact : fp.fl_sub yhat 1 = yhat - 1)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      epsSub = 0 ∧
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp yhat logHat =
          ((yhat - 1) * (1 + epsSub)) /
            (Real.log yhat * (1 + epsLog)) * (1 + epsDiv) := by
  obtain ⟨epsDiv, hepsDiv, hdiv⟩ :=
    fp.model_div (fp.fl_sub yhat 1) logHat hlogHat
  refine ⟨0, epsDiv, rfl, ?_, hepsLog, hepsDiv, ?_⟩
  · simpa using fp.u_nonneg
  · unfold expm1Algorithm2RoundedCore
    rw [hdiv, hsubExact, hlog]
    simp

/-- Guard-digit-model instantiation of the Algorithm 2 subtraction in
equation (1.9).  If the local subtraction routine satisfies Higham/Ferguson's
guard-digit model and the operands `yhat` and `1` satisfy the Ferguson exponent
condition, the source equation holds with exact subtraction, i.e. `epsSub = 0`.
-/
theorem expm1Algorithm2RoundedCore_eq_source_1_9_of_guardDigitSubtractionModel
    (fp : FPModel) {fmt : FloatingPointFormat} (yhat logHat epsLog : ℝ)
    (hguard : fmt.guardDigitSubtractionModel fp.fl_sub)
    (hferguson : fmt.fergusonExponentCondition yhat 1)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      epsSub = 0 ∧
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp yhat logHat =
          ((yhat - 1) * (1 + epsSub)) /
            (Real.log yhat * (1 + epsLog)) * (1 + epsDiv) := by
  exact
    expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub
      fp yhat logHat epsLog
      (fmt.guardDigitSubtractionModel_exact_of_fergusonCondition
        hguard hferguson)
      hepsLog hlog hlogHat

/-- Concrete finite round-to-even/Ferguson instantiation of the Algorithm 2
subtraction in equation (1.9).  This connects the Chapter 1 cancellation
analysis to the already-proved Chapter 2 guard-digit finite-format theorem for
the local `yhat - 1` subtraction, without assuming the later log routine is
concrete. -/
theorem expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_ferguson
    (fp : FPModel) (fmt : FloatingPointFormat) (yhat logHat epsLog : ℝ)
    (hsubRound :
      fp.fl_sub yhat 1 = fmt.finiteRoundToEvenOp BasicOp.sub yhat 1)
    (hferguson : fmt.fergusonExponentCondition yhat 1)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      epsSub = 0 ∧
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp yhat logHat =
          ((yhat - 1) * (1 + epsSub)) /
            (Real.log yhat * (1 + epsLog)) * (1 + epsDiv) := by
  have hsubExact : fp.fl_sub yhat 1 = yhat - 1 := by
    rw [hsubRound]
    exact fmt.finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition hferguson
  exact
    expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub
      fp yhat logHat epsLog hsubExact hepsLog hlog hlogHat

/-- The local small-`x` radius used in Algorithm 2 implies Sterbenz's ratio
condition for the subtraction `yhat - 1`.  This is the source-shaped
replacement for checking exponent cases one by one. -/
theorem expm1Algorithm2_yhat_one_sterbenzRatioCondition_of_abs_sub_one_le_third
    (fmt : FloatingPointFormat) {yhat : ℝ}
    (hyhat_radius : |yhat - 1| ≤ (1 / 3 : ℝ)) :
    fmt.sterbenzRatioCondition yhat 1 := by
  rcases abs_le.mp hyhat_radius with ⟨hlo, hhi⟩
  change (1 : ℝ) / 2 < yhat ∧ yhat < 2 * (1 : ℝ)
  constructor <;> nlinarith

/-- Exact subtraction fact behind the finite round-to-even/Sterbenz-radius
Algorithm 2 adapter.  This exposes the reusable machine step
`fl_sub yhat 1 = yhat - 1`, rather than only the downstream equation-(1.9)
form. -/
theorem expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_sterbenz_radius
    (fp : FPModel) (fmt : FloatingPointFormat) {yhat : ℝ}
    (hsubRound :
      fp.fl_sub yhat 1 = fmt.finiteRoundToEvenOp BasicOp.sub yhat 1)
    (hyhatFinite : fmt.finiteSystem yhat)
    (honeFinite : fmt.finiteSystem 1)
    (hyhat_radius : |yhat - 1| ≤ (1 / 3 : ℝ)) :
    fp.fl_sub yhat 1 = yhat - 1 := by
  have hsterbenz :
      fmt.sterbenzRatioCondition yhat 1 :=
    expm1Algorithm2_yhat_one_sterbenzRatioCondition_of_abs_sub_one_le_third
      fmt hyhat_radius
  rw [hsubRound]
  exact
    fmt.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition
      hyhatFinite honeFinite hsterbenz

/-- Finite round-to-even/Sterbenz-radius instantiation of the Algorithm 2
subtraction in equation (1.9).  If `yhat` and `1` are finite representable and
the local small-`x` analysis has already shown `|yhat-1| <= 1/3`, then
Sterbenz exact subtraction gives the equation-(1.9) form with `epsSub = 0`. -/
theorem expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_sterbenz_radius
    (fp : FPModel) (fmt : FloatingPointFormat) (yhat logHat epsLog : ℝ)
    (hsubRound :
      fp.fl_sub yhat 1 = fmt.finiteRoundToEvenOp BasicOp.sub yhat 1)
    (hyhatFinite : fmt.finiteSystem yhat)
    (honeFinite : fmt.finiteSystem 1)
    (hyhat_radius : |yhat - 1| ≤ (1 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      epsSub = 0 ∧
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp yhat logHat =
          ((yhat - 1) * (1 + epsSub)) /
            (Real.log yhat * (1 + epsLog)) * (1 + epsDiv) := by
  have hsubExact : fp.fl_sub yhat 1 = yhat - 1 :=
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_sterbenz_radius
      fp fmt hsubRound hyhatFinite honeFinite hyhat_radius
  exact
    expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub
      fp yhat logHat epsLog hsubExact hepsLog hlog hlogHat

/-- A reusable consequence of equation (1.9): the rounded subtraction, rounded
logarithm, and final rounded division differ from the slow ratio
`g(yhat) = (yhat-1)/log(yhat)` by one `gamma_4` factor.  This is a generic
gamma-calculus wrapper, not Higham's sharper local `3.5u` analysis. -/
theorem expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4
    (fp : FPModel) (yhat logHat epsLog : ℝ)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid4 : gammaValid fp 4) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 4 ∧
        expm1Algorithm2RoundedCore fp yhat logHat =
          expm1LogRatio yhat * (1 + theta) := by
  obtain ⟨epsSub, epsDiv, hepsSub, _hepsLog, hepsDiv, hcore⟩ :=
    expm1Algorithm2RoundedCore_eq_source_1_9 fp yhat logHat epsLog
      hepsLog hlog hlogHat
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (by norm_num : 1 ≤ 4) hvalid4
  have hvalid3 : gammaValid fp 3 :=
    gammaValid_mono fp (by norm_num : 3 ≤ 4) hvalid4
  have hSubGamma : |epsSub| ≤ gamma fp 1 :=
    le_trans hepsSub (u_le_gamma fp (by norm_num : 0 < 1) hvalid1)
  have hLogGamma : |epsLog| ≤ gamma fp 1 :=
    le_trans hepsLog (u_le_gamma fp (by norm_num : 0 < 1) hvalid1)
  have hDivGamma : |epsDiv| ≤ gamma fp 1 :=
    le_trans hepsDiv (u_le_gamma fp (by norm_num : 0 < 1) hvalid1)
  obtain ⟨thetaDiv, hthetaDiv, hthetaDivEq⟩ :=
    gamma_div fp 1 1 epsSub epsLog hSubGamma hLogGamma hposLog
      (by simpa using hvalid3)
  obtain ⟨theta, htheta, hthetaEq⟩ :=
    gamma_mul fp 3 1 thetaDiv epsDiv hthetaDiv hDivGamma
      (by simpa using hvalid4)
  refine ⟨theta, htheta, ?_⟩
  have hfac_ne : 1 + epsLog ≠ 0 := ne_of_gt hposLog
  have hlog_ne : Real.log yhat ≠ 0 := by
    intro hzero
    apply hlogHat
    rw [hlog, hzero]
    ring
  rw [hcore, ← hthetaEq, ← hthetaDivEq]
  unfold expm1LogRatio
  field_simp [hlog_ne, hfac_ne]

/-- Sharper signed-product version of the Algorithm 2 core wrapper.  The three
local factors from equation (1.9), namely rounded subtraction, rounded logarithm,
and final rounded division, combine into one `gamma_3` factor around
`g(yhat)=(yhat-1)/log(yhat)`. -/
theorem expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3
    (fp : FPModel) (yhat logHat epsLog : ℝ)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 3 ∧
        expm1Algorithm2RoundedCore fp yhat logHat =
          expm1LogRatio yhat * (1 + theta) := by
  obtain ⟨epsSub, epsDiv, hepsSub, _hepsLog, hepsDiv, hcore⟩ :=
    expm1Algorithm2RoundedCore_eq_source_1_9 fp yhat logHat epsLog
      hepsLog hlog hlogHat
  let delta : Fin 3 → ℝ :=
    fun i => if i = 0 then epsSub else if i = 1 then epsLog else epsDiv
  let neg : Fin 3 → Bool := fun i => i = 1
  have hdelta : ∀ i : Fin 3, |delta i| ≤ fp.u := by
    intro i
    fin_cases i <;> simp [delta, hepsSub, hepsLog, hepsDiv]
  obtain ⟨theta, htheta, hprod⟩ :=
    prod_signed_error_bound fp 3 delta neg hdelta hvalid3
  refine ⟨theta, htheta, ?_⟩
  have hprod' :
      (1 + epsSub) * (1 / (1 + epsLog)) * (1 + epsDiv) = 1 + theta := by
    simpa [delta, neg, Fin.prod_univ_three] using hprod
  have hfac_ne : 1 + epsLog ≠ 0 := ne_of_gt hposLog
  have hlog_ne : Real.log yhat ≠ 0 := by
    intro hzero
    apply hlogHat
    rw [hlog, hzero]
    ring
  rw [hcore]
  calc
    ((yhat - 1) * (1 + epsSub)) /
          (Real.log yhat * (1 + epsLog)) * (1 + epsDiv) =
        expm1LogRatio yhat *
          ((1 + epsSub) * (1 / (1 + epsLog)) * (1 + epsDiv)) := by
      unfold expm1LogRatio
      field_simp [hlog_ne, hfac_ne]
    _ = expm1LogRatio yhat * (1 + theta) := by rw [hprod']

/-- Exact-subtraction version of the Algorithm 2 core wrapper.  Once the local
`yhat - 1` subtraction is exact, equation (1.9) has only the rounded logarithm
and final rounded division factors left, so the rounded core is within one
`gamma_2` signed-product factor of `g(yhat)`. -/
theorem expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub
    (fp : FPModel) (yhat logHat epsLog : ℝ)
    (hsubExact : fp.fl_sub yhat 1 = yhat - 1)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp yhat logHat =
          expm1LogRatio yhat * (1 + theta) := by
  obtain ⟨epsSub, epsDiv, hepsSubEq, _hepsSub, _hepsLog, hepsDiv, hcore⟩ :=
    expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub
      fp yhat logHat epsLog hsubExact hepsLog hlog hlogHat
  let delta : Fin 2 → ℝ :=
    fun i => if i = 0 then epsLog else epsDiv
  let neg : Fin 2 → Bool := fun i => i = 0
  have hdelta : ∀ i : Fin 2, |delta i| ≤ fp.u := by
    intro i
    fin_cases i <;> simp [delta, hepsLog, hepsDiv]
  obtain ⟨theta, htheta, hprod⟩ :=
    prod_signed_error_bound fp 2 delta neg hdelta hvalid2
  refine ⟨theta, htheta, ?_⟩
  have hprod' :
      (1 / (1 + epsLog)) * (1 + epsDiv) = 1 + theta := by
    simpa [delta, neg, Fin.prod_univ_two] using hprod
  have hfac_ne : 1 + epsLog ≠ 0 := ne_of_gt hposLog
  have hlog_ne : Real.log yhat ≠ 0 := by
    intro hzero
    apply hlogHat
    rw [hlog, hzero]
    ring
  rw [hcore, hepsSubEq]
  calc
    ((yhat - 1) * (1 + 0)) /
          (Real.log yhat * (1 + epsLog)) * (1 + epsDiv) =
        expm1LogRatio yhat *
          ((1 / (1 + epsLog)) * (1 + epsDiv)) := by
      unfold expm1LogRatio
      field_simp [hlog_ne, hfac_ne]
      ring
    _ = expm1LogRatio yhat * (1 + theta) := by rw [hprod']

/-- Relative-error form of `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4`.
Once the rounded exponential and logarithm inputs are supplied, the rounded
subtraction/division core is within one `gamma_4` factor of the slow ratio
`g(yhat) = (yhat - 1) / log(yhat)`. -/
theorem expm1Algorithm2RoundedCore_relError_le_gamma4
    (fp : FPModel) (yhat logHat epsLog : ℝ)
    (hg : expm1LogRatio yhat ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid4 : gammaValid fp 4) :
    relError (expm1Algorithm2RoundedCore fp yhat logHat)
        (expm1LogRatio yhat) ≤ gamma fp 4 := by
  obtain ⟨theta, htheta, hcore⟩ :=
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4 fp yhat logHat epsLog
      hepsLog hlog hlogHat hposLog hvalid4
  unfold relError
  have hden_nonneg : 0 ≤ |expm1LogRatio yhat| := abs_nonneg _
  have hden_pos : 0 < |expm1LogRatio yhat| := abs_pos.mpr hg
  have hnum :
      |expm1Algorithm2RoundedCore fp yhat logHat - expm1LogRatio yhat| =
        |expm1LogRatio yhat| * |theta| := by
    rw [hcore]
    have hdiff :
        expm1LogRatio yhat * (1 + theta) - expm1LogRatio yhat =
          expm1LogRatio yhat * theta := by ring
    rw [hdiff, abs_mul]
  calc
    |expm1Algorithm2RoundedCore fp yhat logHat - expm1LogRatio yhat| /
        |expm1LogRatio yhat| =
        |theta| := by
          rw [hnum]
          field_simp [hden_pos.ne']
    _ ≤ gamma fp 4 := htheta

/-- Relative-error form of
`expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3`. -/
theorem expm1Algorithm2RoundedCore_relError_le_gamma3
    (fp : FPModel) (yhat logHat epsLog : ℝ)
    (hg : expm1LogRatio yhat ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3) :
    relError (expm1Algorithm2RoundedCore fp yhat logHat)
        (expm1LogRatio yhat) ≤ gamma fp 3 := by
  obtain ⟨theta, htheta, hcore⟩ :=
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3 fp yhat logHat epsLog
      hepsLog hlog hlogHat hposLog hvalid3
  unfold relError
  have hden_nonneg : 0 ≤ |expm1LogRatio yhat| := abs_nonneg _
  have hden_pos : 0 < |expm1LogRatio yhat| := abs_pos.mpr hg
  have hnum :
      |expm1Algorithm2RoundedCore fp yhat logHat - expm1LogRatio yhat| =
        |expm1LogRatio yhat| * |theta| := by
    rw [hcore]
    have hdiff :
        expm1LogRatio yhat * (1 + theta) - expm1LogRatio yhat =
          expm1LogRatio yhat * theta := by ring
    rw [hdiff, abs_mul]
  calc
    |expm1Algorithm2RoundedCore fp yhat logHat - expm1LogRatio yhat| /
        |expm1LogRatio yhat| =
        |theta| := by
          rw [hnum]
          field_simp [hden_pos.ne']
    _ ≤ gamma fp 3 := htheta

/-- Relative-error form of
`expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub`. -/
theorem expm1Algorithm2RoundedCore_relError_le_gamma2_of_exact_sub
    (fp : FPModel) (yhat logHat epsLog : ℝ)
    (hg : expm1LogRatio yhat ≠ 0)
    (hsubExact : fp.fl_sub yhat 1 = yhat - 1)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log yhat * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    relError (expm1Algorithm2RoundedCore fp yhat logHat)
        (expm1LogRatio yhat) ≤ gamma fp 2 := by
  obtain ⟨theta, htheta, hcore⟩ :=
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub
      fp yhat logHat epsLog hsubExact hepsLog hlog hlogHat hposLog hvalid2
  unfold relError
  have hden_nonneg : 0 ≤ |expm1LogRatio yhat| := abs_nonneg _
  have hden_pos : 0 < |expm1LogRatio yhat| := abs_pos.mpr hg
  have hnum :
      |expm1Algorithm2RoundedCore fp yhat logHat - expm1LogRatio yhat| =
        |expm1LogRatio yhat| * |theta| := by
    rw [hcore]
    have hdiff :
        expm1LogRatio yhat * (1 + theta) - expm1LogRatio yhat =
          expm1LogRatio yhat * theta := by ring
    rw [hdiff, abs_mul]
  calc
    |expm1Algorithm2RoundedCore fp yhat logHat - expm1LogRatio yhat| /
        |expm1LogRatio yhat| =
        |theta| := by
          rw [hnum]
          field_simp [hden_pos.ne']
    _ ≤ gamma fp 2 := htheta

/-- The non-asymptotic slow-ratio perturbation budget used by the local
Algorithm 2 error bridge.  It is the explicit right-hand side of
`expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le`. -/
noncomputable def expm1Algorithm2SlowRatioPerturbationBound
    (y delta : ℝ) : ℝ :=
  3 * |y * (1 + delta) - 1| ^ 2 + 3 * |y - 1| ^ 2 +
    (|y - 1| / 2 + 3 * |y - 1| ^ 2) * |delta| / 2

/-- A local relative-error budget for Algorithm 2, after supplying a rounded
exponential relation `yhat = y * (1 + delta)` and a rounded logarithm relation.
This is still a generic bridge: it packages the exact page-24 slow-ratio
perturbation together with the local `gamma_4` arithmetic factor, but it does
not instantiate a concrete exp/log implementation or the sharper `3.5u`
constant. -/
noncomputable def expm1Algorithm2LocalRelErrorBound
    (fp : FPModel) (y delta : ℝ) : ℝ :=
  let g := expm1LogRatio y
  let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
  let drift := |g * delta / 2| + slow
  (drift + (|g| + drift) * gamma fp 4) / |g|

/-- Local relative-error bridge for Higham §1.14.1 Algorithm 2.  The rounded
core is compared with the exact slow ratio at the unrounded exponential value
`y`; the bound consists of the exact slow-ratio drift caused by
`yhat = y*(1+delta)` plus the `gamma_4` factor for rounded subtraction,
rounded logarithm use, and final rounded division. -/
theorem expm1Algorithm2RoundedCore_relError_le_local_bound
    (fp : FPModel) {y delta logHat epsLog : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid4 : gammaValid fp 4)
    (hy : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhat : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ expm1Algorithm2LocalRelErrorBound fp y delta := by
  let g := expm1LogRatio y
  let yhat := y * (1 + delta)
  let ghat := expm1LogRatio yhat
  let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
  let drift := |g * delta / 2| + slow
  have hslow_nonneg : 0 ≤ slow := by
    dsimp [slow, expm1Algorithm2SlowRatioPerturbationBound]
    positivity
  have hdrift_nonneg : 0 ≤ drift := by
    dsimp [drift]
    positivity
  have hgamma_nonneg : 0 ≤ gamma fp 4 := gamma_nonneg fp hvalid4
  have hslow_bound :
      |(ghat - g) - g * delta / 2| ≤ slow := by
    simpa [g, ghat, yhat, slow, expm1Algorithm2SlowRatioPerturbationBound] using
      expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le
        (y := y) (delta := delta) hy hyhat hy0 hyhat0
  have hghat_sub_le : |ghat - g| ≤ drift := by
    have hsplit :
        ghat - g = ((ghat - g) - g * delta / 2) + g * delta / 2 := by ring
    calc
      |ghat - g| =
          |((ghat - g) - g * delta / 2) + g * delta / 2| := by
            exact congrArg abs hsplit
      _ ≤ |(ghat - g) - g * delta / 2| + |g * delta / 2| :=
          abs_add_le _ _
      _ ≤ slow + |g * delta / 2| := add_le_add hslow_bound (le_refl _)
      _ = drift := by simp [drift, add_comm]
  have hghat_abs_le : |ghat| ≤ |g| + drift := by
    have hsplit : ghat = g + (ghat - g) := by ring
    calc
      |ghat| = |g + (ghat - g)| := by
        exact congrArg abs hsplit
      _ ≤ |g| + |ghat - g| := abs_add_le _ _
      _ ≤ |g| + drift := add_le_add (le_refl |g|) hghat_sub_le
  obtain ⟨theta, htheta, hcore⟩ :=
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4
      fp (y * (1 + delta)) logHat epsLog
      hepsLog hlog hlogHat hposLog hvalid4
  have hnum :
      |expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat - g| ≤
        drift + (|g| + drift) * gamma fp 4 := by
    have hsplit :
        expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat - g =
          (ghat - g) + ghat * theta := by
      rw [hcore]
      simp [ghat, yhat]
      ring
    calc
      |expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat - g| =
          |(ghat - g) + ghat * theta| := by rw [hsplit]
      _ ≤ |ghat - g| + |ghat * theta| := abs_add_le _ _
      _ = |ghat - g| + |ghat| * |theta| := by rw [abs_mul]
      _ ≤ drift + (|g| + drift) * gamma fp 4 := by
          exact add_le_add hghat_sub_le
            (mul_le_mul hghat_abs_le htheta (abs_nonneg theta)
              (add_nonneg (abs_nonneg g) hdrift_nonneg))
  have hden_nonneg : 0 ≤ |g| := le_of_lt (abs_pos.mpr (by simpa [g] using hg))
  unfold relError expm1Algorithm2LocalRelErrorBound
  dsimp [g, slow, drift]
  exact div_le_div_of_nonneg_right hnum hden_nonneg

/-- Sharper local Algorithm 2 bridge using the signed-product `gamma_3` core
factor instead of the more conservative `gamma_4` quotient wrapper. -/
theorem expm1Algorithm2RoundedCore_relError_le_local_bound_gamma3
    (fp : FPModel) {y delta logHat epsLog : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hy : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhat : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1) :
    let g := expm1LogRatio y
    let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
    let drift := |g * delta / 2| + slow
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (drift + (|g| + drift) * gamma fp 3) / |g| := by
  let g := expm1LogRatio y
  let yhat := y * (1 + delta)
  let ghat := expm1LogRatio yhat
  let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
  let drift := |g * delta / 2| + slow
  have hslow_nonneg : 0 ≤ slow := by
    dsimp [slow, expm1Algorithm2SlowRatioPerturbationBound]
    positivity
  have hdrift_nonneg : 0 ≤ drift := by
    dsimp [drift]
    positivity
  have hgamma_nonneg : 0 ≤ gamma fp 3 := gamma_nonneg fp hvalid3
  have hslow_bound :
      |(ghat - g) - g * delta / 2| ≤ slow := by
    simpa [g, ghat, yhat, slow, expm1Algorithm2SlowRatioPerturbationBound] using
      expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le
        (y := y) (delta := delta) hy hyhat hy0 hyhat0
  have hghat_sub_le : |ghat - g| ≤ drift := by
    have hsplit :
        ghat - g = ((ghat - g) - g * delta / 2) + g * delta / 2 := by ring
    calc
      |ghat - g| =
          |((ghat - g) - g * delta / 2) + g * delta / 2| := by
            exact congrArg abs hsplit
      _ ≤ |(ghat - g) - g * delta / 2| + |g * delta / 2| :=
          abs_add_le _ _
      _ ≤ slow + |g * delta / 2| := add_le_add hslow_bound (le_refl _)
      _ = drift := by simp [drift, add_comm]
  have hghat_abs_le : |ghat| ≤ |g| + drift := by
    have hsplit : ghat = g + (ghat - g) := by ring
    calc
      |ghat| = |g + (ghat - g)| := by
        exact congrArg abs hsplit
      _ ≤ |g| + |ghat - g| := abs_add_le _ _
      _ ≤ |g| + drift := add_le_add (le_refl |g|) hghat_sub_le
  obtain ⟨theta, htheta, hcore⟩ :=
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3
      fp (y * (1 + delta)) logHat epsLog
      hepsLog hlog hlogHat hposLog hvalid3
  have hnum :
      |expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat - g| ≤
        drift + (|g| + drift) * gamma fp 3 := by
    have hsplit :
        expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat - g =
          (ghat - g) + ghat * theta := by
      rw [hcore]
      simp [ghat, yhat]
      ring
    calc
      |expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat - g| =
          |(ghat - g) + ghat * theta| := by rw [hsplit]
      _ ≤ |ghat - g| + |ghat * theta| := abs_add_le _ _
      _ = |ghat - g| + |ghat| * |theta| := by rw [abs_mul]
      _ ≤ drift + (|g| + drift) * gamma fp 3 := by
          exact add_le_add hghat_sub_le
            (mul_le_mul hghat_abs_le htheta (abs_nonneg theta)
              (add_nonneg (abs_nonneg g) hdrift_nonneg))
  have hden_nonneg : 0 ≤ |g| := le_of_lt (abs_pos.mpr (by simpa [g] using hg))
  unfold relError
  dsimp [g, slow, drift]
  exact div_le_div_of_nonneg_right hnum hden_nonneg

/-- Readable expansion of the local Algorithm 2 relative-error budget: it is
the normalized slow-ratio drift plus a `gamma_4` factor applied to `1` plus
that normalized drift. -/
theorem expm1Algorithm2LocalRelErrorBound_eq_drift_div_add_gamma4
    (fp : FPModel) {y delta : ℝ}
    (hg : expm1LogRatio y ≠ 0) :
    expm1Algorithm2LocalRelErrorBound fp y delta =
      let g := expm1LogRatio y
      let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
      let drift := |g * delta / 2| + slow
      drift / |g| + (1 + drift / |g|) * gamma fp 4 := by
  let g := expm1LogRatio y
  let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
  let drift := |g * delta / 2| + slow
  have hden : |g| ≠ 0 := by
    exact ne_of_gt (abs_pos.mpr (by simpa [g] using hg))
  unfold expm1Algorithm2LocalRelErrorBound
  change
    (drift + (|g| + drift) * gamma fp 4) / |g| =
      drift / |g| + (1 + drift / |g|) * gamma fp 4
  field_simp [hden]

/-- Certificate consumer for the local Algorithm 2 bridge.  If a later
exp/log analysis proves that the slow-ratio drift is at most `eta` times
`|g(y)|`, then the local relative-error budget is bounded by
`eta + (1+eta)*gamma_4`. -/
theorem expm1Algorithm2LocalRelErrorBound_le_eta_add_gamma4
    (fp : FPModel) {y delta eta : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hvalid4 : gammaValid fp 4)
    (hdrift :
      let g := expm1LogRatio y
      let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
      let drift := |g * delta / 2| + slow
      drift ≤ eta * |g|) :
    expm1Algorithm2LocalRelErrorBound fp y delta ≤
      eta + (1 + eta) * gamma fp 4 := by
  let g := expm1LogRatio y
  let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
  let drift := |g * delta / 2| + slow
  have hden_pos : 0 < |g| := abs_pos.mpr (by simpa [g] using hg)
  have hgamma_nonneg : 0 ≤ gamma fp 4 := gamma_nonneg fp hvalid4
  have hdrift' : drift ≤ eta * |g| := by simpa [g, slow, drift] using hdrift
  have hdrift_div : drift / |g| ≤ eta := by
    calc
      drift / |g| ≤ (eta * |g|) / |g| :=
        div_le_div_of_nonneg_right hdrift' (le_of_lt hden_pos)
      _ = eta := by field_simp [hden_pos.ne']
  rw [expm1Algorithm2LocalRelErrorBound_eq_drift_div_add_gamma4 fp (y := y)
      (delta := delta) hg]
  change drift / |g| + (1 + drift / |g|) * gamma fp 4 ≤
    eta + (1 + eta) * gamma fp 4
  have hfactor : 1 + drift / |g| ≤ 1 + eta := by linarith
  exact add_le_add hdrift_div
    (mul_le_mul_of_nonneg_right hfactor hgamma_nonneg)

/-- End-to-end certificate version of the local Algorithm 2 bridge.  This
packages the rounded core theorem with a future drift certificate, leaving only
the concrete exp/log and guard-digit work to instantiate. -/
theorem expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4
    (fp : FPModel) {y delta logHat epsLog eta : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid4 : gammaValid fp 4)
    (hy : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhat : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hdrift :
      let g := expm1LogRatio y
      let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
      let drift := |g * delta / 2| + slow
      drift ≤ eta * |g|) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ eta + (1 + eta) * gamma fp 4 := by
  exact le_trans
    (expm1Algorithm2RoundedCore_relError_le_local_bound
      fp hg hepsLog hlog hlogHat hposLog hvalid4 hy hyhat hy0 hyhat0)
    (expm1Algorithm2LocalRelErrorBound_le_eta_add_gamma4
      fp hg hvalid4 hdrift)

/-- End-to-end certificate version of the sharper local Algorithm 2 bridge.  If
the slow-ratio drift is at most `eta*|g(y)|`, the signed-product core gives
`eta + (1+eta)*gamma_3`. -/
theorem expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3
    (fp : FPModel) {y delta logHat epsLog eta : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hy : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhat : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hdrift :
      let g := expm1LogRatio y
      let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
      let drift := |g * delta / 2| + slow
      drift ≤ eta * |g|) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ eta + (1 + eta) * gamma fp 3 := by
  let g := expm1LogRatio y
  let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
  let drift := |g * delta / 2| + slow
  have hden_pos : 0 < |g| := abs_pos.mpr (by simpa [g] using hg)
  have hgamma_nonneg : 0 ≤ gamma fp 3 := gamma_nonneg fp hvalid3
  have hdrift' : drift ≤ eta * |g| := by simpa [g, slow, drift] using hdrift
  have hdrift_div : drift / |g| ≤ eta := by
    calc
      drift / |g| ≤ (eta * |g|) / |g| :=
        div_le_div_of_nonneg_right hdrift' (le_of_lt hden_pos)
      _ = eta := by field_simp [hden_pos.ne']
  have hlocal :=
    expm1Algorithm2RoundedCore_relError_le_local_bound_gamma3
      fp hg hepsLog hlog hlogHat hposLog hvalid3 hy hyhat hy0 hyhat0
  refine le_trans hlocal ?_
  change (drift + (|g| + drift) * gamma fp 3) / |g| ≤
    eta + (1 + eta) * gamma fp 3
  have hrewrite :
      (drift + (|g| + drift) * gamma fp 3) / |g| =
        drift / |g| + (1 + drift / |g|) * gamma fp 3 := by
    field_simp [hden_pos.ne']
  rw [hrewrite]
  have hfactor : 1 + drift / |g| ≤ 1 + eta := by linarith
  exact add_le_add hdrift_div
    (mul_le_mul_of_nonneg_right hfactor hgamma_nonneg)

/-- Primitive absolute-value budget for the local Algorithm 2 drift.  The
parameters stand for bounds on `|g(y)|`, `|y-1|`, `|yhat-1|`, and `|delta|`,
respectively. -/
noncomputable def expm1Algorithm2PrimitiveDriftBound
    (gAbs yAbs yhatAbs deltaAbs : ℝ) : ℝ :=
  gAbs * deltaAbs / 2 + 3 * yhatAbs ^ 2 + 3 * yAbs ^ 2 +
    (yAbs / 2 + 3 * yAbs ^ 2) * deltaAbs / 2

/-- The non-leading part of the primitive Algorithm 2 drift budget.  After
`|delta| <= u` and `gAbs = |g(y)|`, this is the explicit local remainder beyond
the first-order `(u/2)*|g(y)|` term. -/
noncomputable def expm1Algorithm2PrimitiveSlowRemainderBound
    (yAbs yhatAbs deltaAbs : ℝ) : ℝ :=
  3 * yhatAbs ^ 2 + 3 * yAbs ^ 2 +
    (yAbs / 2 + 3 * yAbs ^ 2) * deltaAbs / 2

/-- Radius form of the primitive slow-remainder budget.  If both local
distances are bounded by the same radius `r`, the residual Algorithm 2
slow-ratio work is bounded by one compact expression. -/
theorem expm1Algorithm2PrimitiveSlowRemainderBound_le_of_radius
    {yAbs yhatAbs deltaAbs r u : ℝ}
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hyAbs : yAbs ≤ r)
    (hyhatAbs : yhatAbs ≤ r)
    (hdeltaAbs : deltaAbs ≤ u)
    (hu_nonneg : 0 ≤ u) :
    expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs ≤
      6 * r ^ 2 + (r / 2 + 3 * r ^ 2) * u / 2 := by
  have hr_nonneg : 0 ≤ r := le_trans hyAbs_nonneg hyAbs
  have hy_sq : yAbs ^ 2 ≤ r ^ 2 := by
    nlinarith [hyAbs, hyAbs_nonneg, hr_nonneg]
  have hyhat_sq : yhatAbs ^ 2 ≤ r ^ 2 := by
    nlinarith [hyhatAbs, hyhatAbs_nonneg, hr_nonneg]
  have hcoeff :
      yAbs / 2 + 3 * yAbs ^ 2 ≤ r / 2 + 3 * r ^ 2 := by
    nlinarith [hyAbs, hy_sq]
  have hcoeff_nonneg : 0 ≤ yAbs / 2 + 3 * yAbs ^ 2 := by
    nlinarith [hyAbs_nonneg, sq_nonneg yAbs]
  have hprod :
      (yAbs / 2 + 3 * yAbs ^ 2) * deltaAbs ≤
        (r / 2 + 3 * r ^ 2) * u := by
    calc
      (yAbs / 2 + 3 * yAbs ^ 2) * deltaAbs ≤
          (yAbs / 2 + 3 * yAbs ^ 2) * u :=
        mul_le_mul_of_nonneg_left hdeltaAbs hcoeff_nonneg
      _ ≤ (r / 2 + 3 * r ^ 2) * u :=
        mul_le_mul_of_nonneg_right hcoeff hu_nonneg
  unfold expm1Algorithm2PrimitiveSlowRemainderBound
  nlinarith [hy_sq, hyhat_sq, hprod]

/-- Radius propagation for the rounded exponential substitution
`yhat = y*(1+delta)`.  If `y` is within radius `r` of `1` and the exponential
relative error is bounded by `u`, then the rounded value is within
`r + (1+r)u` of `1`. -/
theorem expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius
    {y delta r u : ℝ}
    (hy : |y - 1| ≤ r)
    (hdelta : |delta| ≤ u)
    (hr_nonneg : 0 ≤ r) :
    |y * (1 + delta) - 1| ≤ r + (1 + r) * u := by
  have hy_abs : |y| ≤ 1 + r := by
    calc
      |y| = |1 + (y - 1)| := by ring_nf
      _ ≤ |(1 : ℝ)| + |y - 1| := abs_add_le _ _
      _ ≤ 1 + r := by
        norm_num
        exact hy
  have hprod : |y| * |delta| ≤ (1 + r) * u := by
    exact mul_le_mul hy_abs hdelta (abs_nonneg delta) (by linarith)
  calc
    |y * (1 + delta) - 1|
        = |(y - 1) + y * delta| := by
          congr 1
          ring
    _ ≤ |y - 1| + |y * delta| := abs_add_le _ _
    _ = |y - 1| + |y| * |delta| := by rw [abs_mul]
    _ ≤ r + (1 + r) * u := add_le_add hy hprod

/-- Source-domain radius for `y = exp x`: if `|x| <= X`, then the exact
exponential value used by Algorithm 2 satisfies
`|exp x - 1| <= exp X - 1`. -/
theorem expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le
    {x X : ℝ} (hx : |x| ≤ X) :
    |Real.exp x - 1| ≤ Real.exp X - 1 :=
  real_abs_exp_sub_one_le_of_abs_le hx

/-- For nonzero `x`, the slow ratio at `y = exp x` has nonzero denominator and
nonzero numerator. -/
theorem expm1LogRatio_exp_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    expm1LogRatio (Real.exp x) ≠ 0 := by
  unfold expm1LogRatio
  have hnum : Real.exp x - 1 ≠ 0 := by
    intro h
    exact hx ((Real.exp_eq_one_iff x).mp (sub_eq_zero.mp h))
  have hden : Real.log (Real.exp x) ≠ 0 := by
    simpa [Real.log_exp] using hx
  exact div_ne_zero hnum hden

/-- Compact scalar smallness adapter for the `x`-radius Algorithm 2 theorem.
The propagated local radius is
`(exp X - 1) + exp X*u = exp X*(1+u) - 1`, so the source-domain condition
`exp X*(1+u) <= 4/3` implies the required local radius bound `<= 1/3`. -/
theorem expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le
    (fp : FPModel) {X : ℝ}
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    (Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u ≤ (1 / 3 : ℝ) := by
  have hrewrite :
      (Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u =
        Real.exp X * (1 + fp.u) - 1 := by
    ring
  rw [hrewrite]
  linarith

/-- Source-shaped exact-subtraction fact for the rounded exponential
perturbation `yhat = y*(1+delta)`.  The finite round-to-even subtraction
`yhat - 1` is exact once the propagated radius stays in the Sterbenz ball. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_perturb_sterbenz_radius
    (fp : FPModel) (fmt : FloatingPointFormat) {y delta r : ℝ}
    (hsubRound :
      fp.fl_sub (y * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (y * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (y * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hy_radius : |y - 1| ≤ r)
    (hdelta_u : |delta| ≤ fp.u)
    (hr_nonneg : 0 ≤ r)
    (hcombined_radius : r + (1 + r) * fp.u ≤ (1 / 3 : ℝ)) :
    fp.fl_sub (y * (1 + delta)) 1 = y * (1 + delta) - 1 := by
  have hyhat_radius : |y * (1 + delta) - 1| ≤ (1 / 3 : ℝ) :=
    le_trans
      (expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius
        hy_radius hdelta_u hr_nonneg)
      hcombined_radius
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_sterbenz_radius
      fp fmt hsubRound hyhatFinite honeFinite hyhat_radius

/-- `x`-radius exact-subtraction fact for the Algorithm 2 subtraction
`exp x*(1+delta) - 1`. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_sterbenz_radius
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hcombined_radius :
      (Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u ≤ (1 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  let r : ℝ := Real.exp X - 1
  have hX_nonneg : 0 ≤ X := le_trans (abs_nonneg x) hx_radius
  have hr_nonneg : 0 ≤ r := by
    have hone : (1 : ℝ) ≤ Real.exp X := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr hX_nonneg
    dsimp [r]
    linarith
  have hy_radius : |Real.exp x - 1| ≤ r := by
    simpa [r] using expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le hx_radius
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_perturb_sterbenz_radius
      (fp := fp) (fmt := fmt) (y := Real.exp x) (delta := delta) (r := r)
      hsubRound hyhatFinite honeFinite hy_radius hdelta_u hr_nonneg
      (by simpa [r] using hcombined_radius)

/-- Compact source-domain exact-subtraction fact for Algorithm 2.  The single
smallness condition `exp X*(1+u) <= 4/3` implies the propagated Sterbenz
radius for the subtraction `exp x*(1+delta) - 1`. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_sterbenz_radius
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u
      (expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le
        fp hsmall)

/-- Source-shaped finite round-to-even/Sterbenz instantiation of Algorithm 2
equation (1.9).  The exact-subtraction hypothesis is no longer a separate
local fact about `yhat`: it follows from `yhat = y*(1+delta)`, the local
radius `|y-1| <= r`, the exponential relative-error bound `|delta| <= u`, and
the propagated-radius condition `r + (1+r)u <= 1/3`. -/
theorem
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_perturb_sterbenz_radius
    (fp : FPModel) (fmt : FloatingPointFormat) {y delta logHat epsLog r : ℝ}
    (hsubRound :
      fp.fl_sub (y * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (y * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (y * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hy_radius : |y - 1| ≤ r)
    (hdelta_u : |delta| ≤ fp.u)
    (hr_nonneg : 0 ≤ r)
    (hcombined_radius : r + (1 + r) * fp.u ≤ (1 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      epsSub = 0 ∧
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat =
          (((y * (1 + delta)) - 1) * (1 + epsSub)) /
            (Real.log (y * (1 + delta)) * (1 + epsLog)) *
              (1 + epsDiv) := by
  have hyhat_radius : |y * (1 + delta) - 1| ≤ (1 / 3 : ℝ) :=
    le_trans
      (expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius
        hy_radius hdelta_u hr_nonneg)
      hcombined_radius
  exact
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_sterbenz_radius
      fp fmt (y * (1 + delta)) logHat epsLog hsubRound hyhatFinite
      honeFinite hyhat_radius hepsLog hlog hlogHat

/-- `x`-radius version of the finite round-to-even/Sterbenz exact-subtraction
bridge for Algorithm 2 equation (1.9).  This packages the source's small-`x`
language: from `|x| <= X`, `y = exp x` stays within `exp X - 1` of `1`, and
the rounded exponential perturbation keeps `yhat` inside the Sterbenz ball. -/
theorem
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hcombined_radius :
      (Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u ≤ (1 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      epsSub = 0 ∧
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          (((Real.exp x * (1 + delta)) - 1) * (1 + epsSub)) /
            (Real.log (Real.exp x * (1 + delta)) * (1 + epsLog)) *
              (1 + epsDiv) := by
  let r : ℝ := Real.exp X - 1
  have hX_nonneg : 0 ≤ X := le_trans (abs_nonneg x) hx_radius
  have hr_nonneg : 0 ≤ r := by
    have hone : (1 : ℝ) ≤ Real.exp X := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr hX_nonneg
    dsimp [r]
    linarith
  have hy_radius : |Real.exp x - 1| ≤ r := by
    simpa [r] using expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le hx_radius
  exact
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_perturb_sterbenz_radius
      (fp := fp) (fmt := fmt) (y := Real.exp x) (delta := delta)
      (logHat := logHat) (epsLog := epsLog) (r := r)
      hsubRound hyhatFinite honeFinite hy_radius hdelta_u hr_nonneg
      (by simpa [r] using hcombined_radius) hepsLog hlog hlogHat

/-- Compact source-domain smallness version of the finite round-to-even
Sterbenz bridge for Algorithm 2 equation (1.9).  The single condition
`exp X*(1+u) <= 4/3` implies the propagated local radius needed for exact
subtraction. -/
theorem
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      epsSub = 0 ∧
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          (((Real.exp x * (1 + delta)) - 1) * (1 + epsSub)) /
            (Real.log (Real.exp x * (1 + delta)) * (1 + epsLog)) *
              (1 + epsDiv) := by
  exact
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u
      (expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le
        fp hsmall)
      hepsLog hlog hlogHat

/-- Compact source-domain `gamma_2` core wrapper for Algorithm 2 on the
finite round-to-even/Sterbenz path.  The subtraction `exp x*(1+delta)-1` is
proved exact from the source smallness condition, so only the rounded log and
final division factors are charged. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  have hsubExact :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        Real.exp x * (1 + delta) - 1 :=
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub
      fp (Real.exp x * (1 + delta)) logHat epsLog hsubExact hepsLog hlog
      hlogHat hposLog hvalid2

/-- Relative-error form of the compact source-domain `gamma_2` Algorithm 2
core wrapper on the finite round-to-even/Sterbenz path. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  have hsubExact :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        Real.exp x * (1 + delta) - 1 :=
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_exact_sub
      fp (Real.exp x * (1 + delta)) logHat epsLog hg hsubExact hepsLog hlog
      hlogHat hposLog hvalid2

/-- Finite-normal rounded-exp adapter for the source-shaped Algorithm 2
perturbation variable.  If the value used by Algorithm 2 is the finite
round-to-even result for `exp x`, then the supplied `delta` in
`exp x * (1 + delta)` has the usual unit-roundoff bound. -/
theorem expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hyhatRound :
      Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x)) :
    |delta| ≤ fp.u := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hxnormal with
    ⟨delta₀, _hround, hdelta₀, hwit⟩
  have hx_ne : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
  have hdelta_eq : delta = delta₀ := by
    unfold signedRelErrorWitness at hwit
    have hmul :
        Real.exp x * (1 + delta) = Real.exp x * (1 + delta₀) :=
      hyhatRound.trans hwit
    have hone : 1 + delta = 1 + delta₀ := mul_left_cancel₀ hx_ne hmul
    linarith
  calc
    |delta| = |delta₀| := by rw [hdelta_eq]
    _ ≤ fmt.unitRoundoff := le_of_lt hdelta₀
    _ ≤ fp.u := hu

/-- Rounded-exp-produced `yhat` version of the compact source-domain exact
subtraction fact.  If the value used by Algorithm 2 is explicitly the finite
round-to-even value of `exp x`, its finite representability follows from the
rounding selector rather than being an external hypothesis. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  have hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)) := by
    simpa [hyhatRound] using fmt.finiteRoundToEven_finiteSystem (Real.exp x)
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall

/-- Rounded-exp-produced `yhat` version of the compact source-domain `gamma_2`
Algorithm 2 core wrapper.  This discharges the finite-representability
hypothesis for `yhat` from the concrete equality
`yhat = finiteRoundToEven(exp x)`. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  have hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)) := by
    simpa [hyhatRound] using fmt.finiteRoundToEven_finiteSystem (Real.exp x)
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall
      hepsLog hlog hlogHat hposLog hvalid2

/-- Relative-error form of the rounded-exp-produced `gamma_2` Algorithm 2 core
wrapper. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  have hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)) := by
    simpa [hyhatRound] using fmt.finiteRoundToEven_finiteSystem (Real.exp x)
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hg hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall
      hepsLog hlog hlogHat hposLog hvalid2

/-- Finite-normal rounded-exp version of the compact source-domain exact
subtraction fact.  This consumes the round-to-even normal-range contract for
`exp x` to derive the `|delta| <= u` hypothesis used by the Sterbenz radius
wrapper. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  have hdelta_u :
      |delta| ≤ fp.u :=
    expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange
      fp fmt hu hxnormal hyhatRound
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
      fp fmt hyhatRound hsubRound honeFinite hx_radius hdelta_u hsmall

/-- Finite-normal rounded-exp version of the compact source-domain `gamma_2`
Algorithm 2 core wrapper.  The relative-error bound for the rounded
exponential is derived from the finite round-to-even normal-range contract. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  have hdelta_u :
      |delta| ≤ fp.u :=
    expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange
      fp fmt hu hxnormal hyhatRound
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
      fp fmt hyhatRound hsubRound honeFinite hx_radius hdelta_u hsmall
      hepsLog hlog hlogHat hposLog hvalid2

/-- Relative-error form of the finite-normal rounded-exp `gamma_2` Algorithm 2
core wrapper. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  have hdelta_u :
      |delta| ≤ fp.u :=
    expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange
      fp fmt hu hxnormal hyhatRound
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
      fp fmt hg hyhatRound hsubRound honeFinite hx_radius hdelta_u hsmall
      hepsLog hlog hlogHat hposLog hvalid2

/-- Finite-normal rounded-log adapter for the source-shaped Algorithm 2
logarithm variable.  If the value used for `logHat` is the finite
round-to-even result for `log yhat`, then a source-shaped `epsLog` exists with
the usual unit-roundoff bound; the same strict normal-range bound also gives
`logHat ≠ 0` and `0 < 1 + epsLog`. -/
theorem expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange
    (fp : FPModel) (fmt : FloatingPointFormat) {yhat logHat : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hlognormal : fmt.finiteNormalRange (Real.log yhat))
    (hlogRound : logHat = fmt.finiteRoundToEven (Real.log yhat)) :
    ∃ epsLog : ℝ,
      |epsLog| ≤ fp.u ∧
        logHat = Real.log yhat * (1 + epsLog) ∧
          logHat ≠ 0 ∧ 0 < 1 + epsLog := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hlognormal with
    ⟨epsLog, _hround, hepsLog_lt, hwit⟩
  have hlogRel : logHat = Real.log yhat * (1 + epsLog) := by
    calc
      logHat = fmt.finiteRoundToEven (Real.log yhat) := hlogRound
      _ = Real.log yhat * (1 + epsLog) := by
        simpa [signedRelErrorWitness] using hwit
  have hepsLog_le : |epsLog| ≤ fp.u :=
    le_trans (le_of_lt hepsLog_lt) hu
  have hepsLog_lt_one : |epsLog| < 1 :=
    lt_trans hepsLog_lt hunit_lt_one
  have hposLog : 0 < 1 + epsLog := by
    have hgt : -1 < epsLog := (abs_lt.mp hepsLog_lt_one).1
    linarith
  have hlog_ne : Real.log yhat ≠ 0 :=
    fmt.finiteNormalRange_ne_zero hlognormal
  have hlogHat : logHat ≠ 0 := by
    rw [hlogRel]
    exact mul_ne_zero hlog_ne (ne_of_gt hposLog)
  exact ⟨epsLog, hepsLog_le, hlogRel, hlogHat, hposLog⟩

/-- Finite-normal rounded-exp/log version of the compact source-domain
`gamma_2` Algorithm 2 core wrapper.  Both the rounded exponential and rounded
logarithm error witnesses are produced from finite round-to-even normal-range
contracts; the subtraction operation link remains explicit. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  rcases
    expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange
      fp fmt hu hunit_lt_one hlognormal hlogRound with
    ⟨epsLog, hepsLog, hlog, hlogHat, hposLog⟩
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz
      fp fmt hu hxnormal hyhatRound hsubRound honeFinite hx_radius hsmall
      hepsLog hlog hlogHat hposLog hvalid2

/-- Relative-error form of the finite-normal rounded-exp/log `gamma_2`
Algorithm 2 core wrapper. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  rcases
    expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange
      fp fmt hu hunit_lt_one hlognormal hlogRound with
    ⟨epsLog, hepsLog, hlog, hlogHat, hposLog⟩
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz
      fp fmt hg hu hxnormal hyhatRound hsubRound honeFinite hx_radius hsmall
      hepsLog hlog hlogHat hposLog hvalid2

/-- Routine-level operation link saying that the subtraction operation of an
abstract `FPModel` is implemented by the source-facing finite round-to-even
operation wrapper for a concrete format. -/
def finiteRoundToEvenSubtractionLink
    (fp : FPModel) (fmt : FloatingPointFormat) : Prop :=
  ∀ x y : ℝ, fp.fl_sub x y = fmt.finiteRoundToEvenOp BasicOp.sub x y

theorem finiteRoundToEvenSubtractionLink.sub_one
    {fp : FPModel} {fmt : FloatingPointFormat}
    (hlink : finiteRoundToEvenSubtractionLink fp fmt) (yhat : ℝ) :
    fp.fl_sub yhat 1 = fmt.finiteRoundToEvenOp BasicOp.sub yhat 1 :=
  hlink yhat 1

/-- Finite-normal rounded-exp version of exact subtraction using a
routine-level finite round-to-even subtraction link rather than a pointwise
operation equality at the produced `yhat`. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz_of_subtractionLink
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hsubLink : finiteRoundToEvenSubtractionLink fp fmt)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz
      fp fmt hu hxnormal hyhatRound
      (hsubLink.sub_one (Real.exp x * (1 + delta)))
      honeFinite hx_radius hsmall

/-- Finite-normal rounded-exp/log `gamma_2` core wrapper using a routine-level
finite round-to-even subtraction link.  The rounded exp/log witnesses come
from finite round-to-even normal-range contracts; the subtraction link is now
one routine-level hypothesis instead of a pointwise equality at `yhat`. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz_of_subtractionLink
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hsubLink : finiteRoundToEvenSubtractionLink fp fmt)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz
      fp fmt hu hunit_lt_one hxnormal hlognormal hyhatRound hlogRound
      (hsubLink.sub_one (Real.exp x * (1 + delta)))
      honeFinite hx_radius hsmall hvalid2

/-- Relative-error form of the finite-normal rounded-exp/log `gamma_2` wrapper
with a routine-level finite round-to-even subtraction link. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz_of_subtractionLink
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hsubLink : finiteRoundToEvenSubtractionLink fp fmt)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz
      fp fmt hg hu hunit_lt_one hxnormal hlognormal hyhatRound hlogRound
      (hsubLink.sub_one (Real.exp x * (1 + delta)))
      honeFinite hx_radius hsmall hvalid2

/-- The explicit slow-ratio perturbation budget is monotone in elementary
absolute-value bounds for `|y-1|`, `|yhat-1|`, and `|delta|`. -/
theorem expm1Algorithm2SlowRatioPerturbationBound_le_of_abs_bounds
    {y delta yAbs yhatAbs deltaAbs : ℝ}
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs) :
    expm1Algorithm2SlowRatioPerturbationBound y delta ≤
      3 * yhatAbs ^ 2 + 3 * yAbs ^ 2 +
        (yAbs / 2 + 3 * yAbs ^ 2) * deltaAbs / 2 := by
  have hy_sq : |y - 1| ^ 2 ≤ yAbs ^ 2 := by
    nlinarith [hy, abs_nonneg (y - 1), hyAbs_nonneg]
  have hyhat_sq :
      |y * (1 + delta) - 1| ^ 2 ≤ yhatAbs ^ 2 := by
    nlinarith [hyhat, abs_nonneg (y * (1 + delta) - 1), hyhatAbs_nonneg]
  have hcoeff :
      |y - 1| / 2 + 3 * |y - 1| ^ 2 ≤
        yAbs / 2 + 3 * yAbs ^ 2 := by
    nlinarith [hy, hy_sq]
  have hcoeff_nonneg : 0 ≤ |y - 1| / 2 + 3 * |y - 1| ^ 2 := by
    positivity
  have hcoeff_bound_nonneg : 0 ≤ yAbs / 2 + 3 * yAbs ^ 2 := by
    nlinarith [hyAbs_nonneg, sq_nonneg yAbs]
  have hprod :
      (|y - 1| / 2 + 3 * |y - 1| ^ 2) * |delta| ≤
        (yAbs / 2 + 3 * yAbs ^ 2) * deltaAbs := by
    calc
      (|y - 1| / 2 + 3 * |y - 1| ^ 2) * |delta| ≤
          (|y - 1| / 2 + 3 * |y - 1| ^ 2) * deltaAbs :=
        mul_le_mul_of_nonneg_left hdelta hcoeff_nonneg
      _ ≤ (yAbs / 2 + 3 * yAbs ^ 2) * deltaAbs :=
        mul_le_mul_of_nonneg_right hcoeff hdeltaAbs_nonneg
  have hterm :
      (|y - 1| / 2 + 3 * |y - 1| ^ 2) * |delta| / 2 ≤
        (yAbs / 2 + 3 * yAbs ^ 2) * deltaAbs / 2 := by
    exact div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 2)
  unfold expm1Algorithm2SlowRatioPerturbationBound
  nlinarith [hy_sq, hyhat_sq, hterm]

/-- The full slow-ratio drift used by the local Algorithm 2 bridge is bounded
by the primitive absolute-value budget. -/
theorem expm1Algorithm2LocalDrift_le_primitive_bound
    {y delta gAbs yAbs yhatAbs deltaAbs : ℝ}
    (hgAbs : |expm1LogRatio y| ≤ gAbs)
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs) :
    let g := expm1LogRatio y
    let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
    let drift := |g * delta / 2| + slow
    drift ≤ expm1Algorithm2PrimitiveDriftBound gAbs yAbs yhatAbs deltaAbs := by
  let g := expm1LogRatio y
  let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
  let drift := |g * delta / 2| + slow
  have hgAbs_nonneg : 0 ≤ gAbs := by
    exact le_trans (abs_nonneg g) hgAbs
  have hmul_prod : |g| * |delta| ≤ gAbs * deltaAbs := by
    exact mul_le_mul (by simpa [g] using hgAbs) hdelta (abs_nonneg delta)
      hgAbs_nonneg
  have hmul : |g * delta / 2| ≤ gAbs * deltaAbs / 2 := by
    calc
      |g * delta / 2| = |g| * |delta| / 2 := by
        rw [abs_div, abs_mul]
        norm_num
      _ ≤ gAbs * deltaAbs / 2 :=
        div_le_div_of_nonneg_right hmul_prod (by norm_num : (0 : ℝ) ≤ 2)
  have hslow :
      slow ≤ 3 * yhatAbs ^ 2 + 3 * yAbs ^ 2 +
        (yAbs / 2 + 3 * yAbs ^ 2) * deltaAbs / 2 := by
    simpa [slow] using
      expm1Algorithm2SlowRatioPerturbationBound_le_of_abs_bounds
        (y := y) (delta := delta) hy hyhat hdelta
        hyAbs_nonneg hyhatAbs_nonneg hdeltaAbs_nonneg
  dsimp [drift, expm1Algorithm2PrimitiveDriftBound]
  nlinarith [hmul, hslow]

/-- End-to-end local Algorithm 2 bridge from primitive absolute-value bounds.
Once the primitive drift budget is shown to be at most `eta*|g(y)|`, the
rounded core has relative error at most `eta + (1+eta)*gamma_4`. -/
theorem expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4_of_primitive_bounds
    (fp : FPModel) {y delta logHat epsLog eta gAbs yAbs yhatAbs deltaAbs : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid4 : gammaValid fp 4)
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hgAbs : |expm1LogRatio y| ≤ gAbs)
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs)
    (hprimitive :
      expm1Algorithm2PrimitiveDriftBound gAbs yAbs yhatAbs deltaAbs ≤
        eta * |expm1LogRatio y|) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ eta + (1 + eta) * gamma fp 4 := by
  refine
    expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4
      fp hg hepsLog hlog hlogHat hposLog hvalid4
      hySmall hyhatSmall hy0 hyhat0 ?_
  exact le_trans
    (expm1Algorithm2LocalDrift_le_primitive_bound
      (y := y) (delta := delta) hgAbs hy hyhat hdelta
      hyAbs_nonneg hyhatAbs_nonneg hdeltaAbs_nonneg)
    hprimitive

/-- Sharper primitive-budget bridge for local Algorithm 2.  The same elementary
absolute-value budget feeds the signed-product `gamma_3` core factor. -/
theorem expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3_of_primitive_bounds
    (fp : FPModel) {y delta logHat epsLog eta gAbs yAbs yhatAbs deltaAbs : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hgAbs : |expm1LogRatio y| ≤ gAbs)
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs)
    (hprimitive :
      expm1Algorithm2PrimitiveDriftBound gAbs yAbs yhatAbs deltaAbs ≤
        eta * |expm1LogRatio y|) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ eta + (1 + eta) * gamma fp 3 := by
  refine
    expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3
      fp hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 ?_
  exact le_trans
    (expm1Algorithm2LocalDrift_le_primitive_bound
      (y := y) (delta := delta) hgAbs hy hyhat hdelta
      hyAbs_nonneg hyhatAbs_nonneg hdeltaAbs_nonneg)
    hprimitive

/-- Primitive drift decomposition after the rounded-exponential perturbation is
bounded by unit roundoff.  This isolates the source's first-order
`(u/2)*|g(y)|` contribution and leaves only an explicit slow-ratio remainder. -/
theorem
    expm1Algorithm2PrimitiveDriftBound_le_half_u_mul_abs_logRatio_add_slow_remainder
    (fp : FPModel) {y yAbs yhatAbs deltaAbs : ℝ}
    (hdeltaAbs_le_u : deltaAbs ≤ fp.u) :
    expm1Algorithm2PrimitiveDriftBound (|expm1LogRatio y|) yAbs yhatAbs deltaAbs ≤
      (fp.u / 2) * |expm1LogRatio y| +
        expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs := by
  let g := expm1LogRatio y
  have hfirst : |g| * deltaAbs / 2 ≤ (fp.u / 2) * |g| := by
    have hmul : |g| * deltaAbs ≤ |g| * fp.u :=
      mul_le_mul_of_nonneg_left hdeltaAbs_le_u (abs_nonneg g)
    nlinarith
  dsimp [g, expm1Algorithm2PrimitiveDriftBound,
    expm1Algorithm2PrimitiveSlowRemainderBound]
  nlinarith [hfirst]

/-- Source-shaped first-order Algorithm 2 bound.  Once the local slow-ratio
drift has been proved at most `(u/2)*|g(y)|`, the sharper signed-product core
gives Higham's advertised `3.5u` leading term plus an explicit higher-order
remainder.  The concrete exp/log and guard-digit hypotheses are still supplied
through the rounded-core model inputs. -/
theorem expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder
    (fp : FPModel) {y delta logHat epsLog : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hdrift :
      let g := expm1LogRatio y
      let slow := expm1Algorithm2SlowRatioPerturbationBound y delta
      let drift := |g * delta / 2| + slow
      drift ≤ (fp.u / 2) * |g|) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 := by
  have hbase :
      relError
          (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
          (expm1LogRatio y)
        ≤ fp.u / 2 + (1 + fp.u / 2) * gamma fp 3 :=
    expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3
      (fp := fp) (y := y) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (eta := fp.u / 2)
      hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 hdrift
  set G : ℝ := gamma fp 3 with hG
  set R : ℝ :=
    (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) with hR
  have hgamma : G = (3 : ℝ) * fp.u + R := by
    rw [hG, hR]
    exact gamma_eq_linear_plus_quadratic_remainder fp 3 hvalid3
  have hrewrite :
      fp.u / 2 + (1 + fp.u / 2) * G =
        (7 / 2 : ℝ) * fp.u + R + (fp.u / 2) * G := by
    rw [hgamma]
    ring
  rw [hrewrite] at hbase
  simpa [hG, hR, add_assoc] using hbase

/-- Primitive-budget version of the Algorithm 2 `3.5u`-plus-remainder bridge.
The elementary absolute-value drift budget is the only open local analytic
input needed before the source-shaped first-order estimate applies. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder_of_primitive_bounds
    (fp : FPModel) {y delta logHat epsLog gAbs yAbs yhatAbs deltaAbs : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hgAbs : |expm1LogRatio y| ≤ gAbs)
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs)
    (hprimitive :
      expm1Algorithm2PrimitiveDriftBound gAbs yAbs yhatAbs deltaAbs ≤
        (fp.u / 2) * |expm1LogRatio y|) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 := by
  refine
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder
      fp hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 ?_
  exact le_trans
    (expm1Algorithm2LocalDrift_le_primitive_bound
      (y := y) (delta := delta) hgAbs hy hyhat hdelta
      hyAbs_nonneg hyhatAbs_nonneg hdeltaAbs_nonneg)
    hprimitive

/-- Algorithm 2 `3.5u` leading term with the local slow-ratio remainder left
explicit.  This discharges the leading rounded-exponential contribution from
`|delta| <= deltaAbs <= u`; only the displayed quadratic/small-`y` remainder
has to be controlled by a future interval or machine-specific instantiation. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds
    (fp : FPModel) {y delta logHat epsLog yAbs yhatAbs deltaAbs : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs)
    (hdeltaAbs_le_u : deltaAbs ≤ fp.u) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs /
          |expm1LogRatio y|) * (1 + gamma fp 3) := by
  let g := expm1LogRatio y
  let S := expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs
  have hden_pos : 0 < |g| := abs_pos.mpr (by simpa [g] using hg)
  have hprimitive :
      expm1Algorithm2PrimitiveDriftBound (|expm1LogRatio y|) yAbs yhatAbs deltaAbs ≤
        (fp.u / 2 + S / |g|) * |expm1LogRatio y| := by
    have hsplit :
        expm1Algorithm2PrimitiveDriftBound (|expm1LogRatio y|) yAbs yhatAbs deltaAbs ≤
          (fp.u / 2) * |expm1LogRatio y| + S := by
      simpa [S] using
        expm1Algorithm2PrimitiveDriftBound_le_half_u_mul_abs_logRatio_add_slow_remainder
          (fp := fp) (y := y) (yAbs := yAbs) (yhatAbs := yhatAbs)
          (deltaAbs := deltaAbs) hdeltaAbs_le_u
    have hrewrite :
        (fp.u / 2 + S / |g|) * |expm1LogRatio y| =
          (fp.u / 2) * |expm1LogRatio y| + S := by
      field_simp [g, hden_pos.ne']
      ring
    simpa [hrewrite]
  have hbase :
      relError
          (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
          (expm1LogRatio y)
        ≤ fp.u / 2 + S / |g| +
          (1 + (fp.u / 2 + S / |g|)) * gamma fp 3 :=
    expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3_of_primitive_bounds
      (fp := fp) (y := y) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (eta := fp.u / 2 + S / |g|)
      (gAbs := |expm1LogRatio y|) (yAbs := yAbs) (yhatAbs := yhatAbs)
      (deltaAbs := deltaAbs)
      hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 le_rfl hy hyhat hdelta
      hyAbs_nonneg hyhatAbs_nonneg hdeltaAbs_nonneg hprimitive
  calc
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
        ≤ fp.u / 2 + S / |g| +
          (1 + (fp.u / 2 + S / |g|)) * gamma fp 3 := hbase
    _ =
      (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (S / |g|) * (1 + gamma fp 3) := by
          rw [gamma_eq_linear_plus_quadratic_remainder fp 3 hvalid3]
          ring
    _ =
      (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs /
          |expm1LogRatio y|) * (1 + gamma fp 3) := by
          simp [g, S]

/-- Radius-remainder version of the local Algorithm 2 `3.5u` bridge.  This
packages the explicit slow-ratio remainder into a single local radius `r` for
both `|y-1|` and `|yhat-1|`; concrete interval proofs can then focus on a
radius and a lower bound for `|g(y)|`. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_remainder_of_abs_bounds
    (fp : FPModel) {y delta logHat epsLog yAbs yhatAbs deltaAbs r : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs)
    (hdeltaAbs_le_u : deltaAbs ≤ fp.u)
    (hyAbs_le_radius : yAbs ≤ r)
    (hyhatAbs_le_radius : yhatAbs ≤ r) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        ((6 * r ^ 2 + (r / 2 + 3 * r ^ 2) * fp.u / 2) /
          |expm1LogRatio y|) * (1 + gamma fp 3) := by
  let S := expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs
  let R := 6 * r ^ 2 + (r / 2 + 3 * r ^ 2) * fp.u / 2
  let g := expm1LogRatio y
  have hlocal :=
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds
      (fp := fp) (y := y) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (yAbs := yAbs) (yhatAbs := yhatAbs)
      (deltaAbs := deltaAbs)
      hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 hy hyhat hdelta
      hyAbs_nonneg hyhatAbs_nonneg hdeltaAbs_nonneg hdeltaAbs_le_u
  have hS_le_R : S ≤ R := by
    simpa [S, R] using
      expm1Algorithm2PrimitiveSlowRemainderBound_le_of_radius
        hyAbs_nonneg hyhatAbs_nonneg hyAbs_le_radius hyhatAbs_le_radius
        hdeltaAbs_le_u fp.u_nonneg
  have hden_pos : 0 < |g| := abs_pos.mpr (by simpa [g] using hg)
  have hS_div_le_R_div : S / |g| ≤ R / |g| :=
    div_le_div_of_nonneg_right hS_le_R (le_of_lt hden_pos)
  have hfactor_nonneg : 0 ≤ 1 + gamma fp 3 := by
    have hgamma_nonneg : 0 ≤ gamma fp 3 := gamma_nonneg fp hvalid3
    linarith
  have htail :
      (S / |g|) * (1 + gamma fp 3) ≤
        (R / |g|) * (1 + gamma fp 3) :=
    mul_le_mul_of_nonneg_right hS_div_le_R_div hfactor_nonneg
  calc
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
        ≤ (7 / 2 : ℝ) * fp.u +
          (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
          (fp.u / 2) * gamma fp 3 +
          (S / |g|) * (1 + gamma fp 3) := by
            simpa [S, g] using hlocal
    _ ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (R / |g|) * (1 + gamma fp 3) := by
          linarith
    _ =
      (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        ((6 * r ^ 2 + (r / 2 + 3 * r ^ 2) * fp.u / 2) /
          |expm1LogRatio y|) * (1 + gamma fp 3) := by
          simp [R, g]

/-- Denominator-free radius version of the local Algorithm 2 `3.5u` bridge.
When the source slow ratio is controlled in a radius `r <= 1/3`, the denominator
lower bound `1/2 <= |g(y)|` removes the final normalized division.  Future
concrete exp/log or machine proofs can therefore supply only radius bounds for
`y` and `yhat`. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_bound_of_abs_bounds
    (fp : FPModel) {y delta logHat epsLog yAbs yhatAbs deltaAbs r : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs)
    (hdeltaAbs_le_u : deltaAbs ≤ fp.u)
    (hyAbs_le_radius : yAbs ≤ r)
    (hyhatAbs_le_radius : yhatAbs ≤ r)
    (hr_le : r ≤ (1 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * r ^ 2 + (r / 2 + 3 * r ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  let R := 6 * r ^ 2 + (r / 2 + 3 * r ^ 2) * fp.u / 2
  let g := expm1LogRatio y
  have hbase :=
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_remainder_of_abs_bounds
      (fp := fp) (y := y) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (yAbs := yAbs) (yhatAbs := yhatAbs)
      (deltaAbs := deltaAbs) (r := r)
      hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 hy hyhat hdelta
      hyAbs_nonneg hyhatAbs_nonneg hdeltaAbs_nonneg hdeltaAbs_le_u
      hyAbs_le_radius hyhatAbs_le_radius
  have hr_nonneg : 0 ≤ r := le_trans hyAbs_nonneg hyAbs_le_radius
  have hy_radius : |y - 1| ≤ r := le_trans hy hyAbs_le_radius
  have hden_half : (1 / 2 : ℝ) ≤ |g| := by
    simpa [g] using
      expm1LogRatio_abs_ge_half_of_radius
        (y := y) (r := r) hySmall hy0 hy_radius hr_nonneg hr_le
  have hden_pos : 0 < |g| := by linarith
  have hR_nonneg : 0 ≤ R := by
    have hcoeff_nonneg : 0 ≤ r / 2 + 3 * r ^ 2 := by
      nlinarith [hr_nonneg, sq_nonneg r]
    have hsix_nonneg : 0 ≤ 6 * r ^ 2 := by
      nlinarith [sq_nonneg r]
    have hterm_nonneg :
        0 ≤ (r / 2 + 3 * r ^ 2) * fp.u / 2 := by
      exact div_nonneg (mul_nonneg hcoeff_nonneg fp.u_nonneg)
        (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [R]
    nlinarith
  have hR_div_le : R / |g| ≤ 2 * R := by
    rw [div_le_iff₀ hden_pos]
    have htwoR_nonneg : 0 ≤ 2 * R := by nlinarith [hR_nonneg]
    have hmul := mul_le_mul_of_nonneg_left hden_half htwoR_nonneg
    nlinarith [hmul]
  have hfactor_nonneg : 0 ≤ 1 + gamma fp 3 := by
    have hgamma_nonneg : 0 ≤ gamma fp 3 := gamma_nonneg fp hvalid3
    linarith
  have htail :
      (R / |g|) * (1 + gamma fp 3) ≤
        (2 * R) * (1 + gamma fp 3) :=
    mul_le_mul_of_nonneg_right hR_div_le hfactor_nonneg
  calc
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
        ≤ (7 / 2 : ℝ) * fp.u +
          (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
          (fp.u / 2) * gamma fp 3 +
          (R / |g|) * (1 + gamma fp 3) := by
            simpa [R, g] using hbase
    _ ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * R) * (1 + gamma fp 3) := by
          linarith
    _ =
      (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * r ^ 2 + (r / 2 + 3 * r ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
          simp [R]

/-- Source-shaped rounded-exponential radius version of the local Algorithm 2
`3.5u` bridge.  Instead of assuming a separate bound for `|yhat-1|`, this
derives the needed radius from `yhat = y*(1+delta)`, `|y-1| <= r`, and
`|delta| <= u`.  This matches the page-23/24 exp-error hypothesis and avoids
case-by-case local-radius instantiations. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_perturb_radius_bound
    (fp : FPModel) {y delta logHat epsLog r : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hy_radius : |y - 1| ≤ r)
    (hdelta_u : |delta| ≤ fp.u)
    (hr_nonneg : 0 ≤ r)
    (hcombined_radius :
      r + (1 + r) * fp.u ≤ (1 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * (r + (1 + r) * fp.u) ^ 2 +
          ((r + (1 + r) * fp.u) / 2 +
            3 * (r + (1 + r) * fp.u) ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  let R : ℝ := r + (1 + r) * fp.u
  have hR_nonneg : 0 ≤ R := by
    have hprod_nonneg : 0 ≤ (1 + r) * fp.u :=
      mul_nonneg (by linarith) fp.u_nonneg
    dsimp [R]
    linarith
  have hr_le_R : r ≤ R := by
    have hprod_nonneg : 0 ≤ (1 + r) * fp.u :=
      mul_nonneg (by linarith) fp.u_nonneg
    dsimp [R]
    linarith
  have hR_le_third : R ≤ (1 / 3 : ℝ) := by
    simpa [R] using hcombined_radius
  have hR_le_half : R ≤ (1 / 2 : ℝ) := by
    nlinarith [hR_le_third]
  have hyhat_radius : |y * (1 + delta) - 1| ≤ R := by
    simpa [R] using
      expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius
        hy_radius hdelta_u hr_nonneg
  have hySmall : |y - 1| ≤ (1 / 2 : ℝ) :=
    le_trans hy_radius (le_trans hr_le_R hR_le_half)
  have hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ) :=
    le_trans hyhat_radius hR_le_half
  have hbase :=
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_bound_of_abs_bounds
      (fp := fp) (y := y) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (yAbs := r) (yhatAbs := R)
      (deltaAbs := fp.u) (r := R)
      hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 hy_radius hyhat_radius hdelta_u
      hr_nonneg hR_nonneg fp.u_nonneg le_rfl hr_le_R le_rfl hR_le_third
  simpa [R] using hbase

/-- `x`-radius version of the local Algorithm 2 `3.5u` bridge.  This packages
the source phrase "for small `x` (`y ≈ 1`)": a bound `|x| <= X` gives
`|exp x - 1| <= exp X - 1`, the rounded exponential relation gives the
combined `yhat` radius `(exp X - 1) + exp X*u`, and the existing local
Algorithm 2 theorem consumes that radius. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound
    (fp : FPModel) {x delta logHat epsLog X : ℝ}
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hx0 : x ≠ 0) (hyhat0 : Real.exp x * (1 + delta) ≠ 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hcombined_radius :
      (Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u ≤ (1 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x))
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * ((Real.exp X - 1) +
          (1 + (Real.exp X - 1)) * fp.u) ^ 2 +
          (((Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u) / 2 +
            3 * ((Real.exp X - 1) +
              (1 + (Real.exp X - 1)) * fp.u) ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  let r : ℝ := Real.exp X - 1
  have hX_nonneg : 0 ≤ X := le_trans (abs_nonneg x) hx_radius
  have hr_nonneg : 0 ≤ r := by
    have hone : (1 : ℝ) ≤ Real.exp X := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr hX_nonneg
    dsimp [r]
    linarith
  have hy_radius : |Real.exp x - 1| ≤ r := by
    simpa [r] using expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le hx_radius
  have hy0 : Real.exp x ≠ 1 := by
    intro h
    exact hx0 ((Real.exp_eq_one_iff x).mp h)
  have hg : expm1LogRatio (Real.exp x) ≠ 0 :=
    expm1LogRatio_exp_ne_zero_of_ne_zero hx0
  have hbase :=
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_perturb_radius_bound
      (fp := fp) (y := Real.exp x) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (r := r)
      hg hepsLog hlog hlogHat hposLog hvalid3 hy0 hyhat0
      hy_radius hdelta_u hr_nonneg (by simpa [r] using hcombined_radius)
  simpa [r] using hbase

/-- Source-domain smallness version of the `x`-radius Algorithm 2 `3.5u`
bridge.  The side condition `exp X*(1+u) <= 4/3` is a compact way to state
that the propagated rounded-exponential radius stays inside the local
`1/3` ball required by the denominator-free slow-ratio bound. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound
    (fp : FPModel) {x delta logHat epsLog X : ℝ}
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hx0 : x ≠ 0) (hyhat0 : Real.exp x * (1 + delta) ≠ 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x))
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * ((Real.exp X - 1) +
          (1 + (Real.exp X - 1)) * fp.u) ^ 2 +
          (((Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u) / 2 +
            3 * ((Real.exp X - 1) +
              (1 + (Real.exp X - 1)) * fp.u) ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  exact
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound
      fp hepsLog hlog hlogHat hposLog hvalid3 hx0 hyhat0 hx_radius hdelta_u
      (expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le
        fp hsmall)

/-- Finite-normal rounded-exp/log version of the source-shaped Algorithm 2
`3.5u` bridge.  The rounded exponential supplies `|delta| <= u`, and the
rounded logarithm supplies the log relative-error witness and positivity
contract, so the only remaining analytic side conditions are the source
small-`x` radius and nonzero branch facts. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (hvalid3 : gammaValid fp 3)
    (hx0 : x ≠ 0)
    (hyhat0 : Real.exp x * (1 + delta) ≠ 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x))
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * ((Real.exp X - 1) +
          (1 + (Real.exp X - 1)) * fp.u) ^ 2 +
          (((Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u) / 2 +
            3 * ((Real.exp X - 1) +
              (1 + (Real.exp X - 1)) * fp.u) ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  have hdelta_u : |delta| ≤ fp.u :=
    expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange
      fp fmt hu hxnormal hyhatRound
  rcases
    expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange
      fp fmt hu hunit_lt_one hlognormal hlogRound with
    ⟨epsLog, hepsLog, hlog, hlogHat, hposLog⟩
  exact
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound
      (fp := fp) (x := x) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (X := X)
      hepsLog hlog hlogHat hposLog hvalid3 hx0 hyhat0 hx_radius
      hdelta_u hsmall

/-- Source-function form of the finite-normal rounded-exp/log Algorithm 2
`3.5u` bridge.  This rewrites the exact comparison target from
`g(exp x)` to the Chapter 1 function `(exp x - 1) / x`. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal_algorithm1Exact
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (hvalid3 : gammaValid fp 3)
    (hx0 : x ≠ 0)
    (hyhat0 : Real.exp x * (1 + delta) ≠ 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1Algorithm1Exact x)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * ((Real.exp X - 1) +
          (1 + (Real.exp X - 1)) * fp.u) ^ 2 +
          (((Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u) / 2 +
            3 * ((Real.exp X - 1) +
              (1 + (Real.exp X - 1)) * fp.u) ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  have hbase :=
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal
      (fp := fp) (fmt := fmt) (x := x) (delta := delta)
      (logHat := logHat) (X := X)
      hu hunit_lt_one hxnormal hlognormal hyhatRound hlogRound hvalid3
      hx0 hyhat0 hx_radius hsmall
  simpa [expm1LogRatio_exp_eq_algorithm1Exact_of_ne_zero hx0] using hbase

/-- Unit-roundoff-radius version of the local Algorithm 2 `3.5u` bridge.  If
the local distances `|y-1|` and `|yhat-1|` are both bounded by `u`, the
remaining slow-ratio tail is explicitly second order:
`((25/2)u^2 + 3u^3)(1+gamma_3)`. -/
noncomputable def expm1Algorithm2ThreePointFiveUnitBound (fp : FPModel) : ℝ :=
  (7 / 2 : ℝ) * fp.u +
    (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
    (fp.u / 2) * gamma fp 3 +
    (((25 / 2 : ℝ) * fp.u ^ 2 + 3 * fp.u ^ 3) *
      (1 + gamma fp 3))

/-- Scalar `gamma_3` envelope used to interpret the local Algorithm 2
`3.5u` bound as a function of the unit roundoff variable. -/
noncomputable def expm1Algorithm2Gamma3Scalar (u : ℝ) : ℝ :=
  ((3 : ℝ) * u) / (1 - (3 : ℝ) * u)

/-- Scalar form of `expm1Algorithm2ThreePointFiveUnitBound`, with the unit
roundoff exposed as the variable `u`. -/
noncomputable def expm1Algorithm2ThreePointFiveUnitBoundScalar (u : ℝ) : ℝ :=
  (7 / 2 : ℝ) * u +
    (((3 : ℝ) * u) ^ 2) / (1 - (3 : ℝ) * u) +
    (u / 2) * expm1Algorithm2Gamma3Scalar u +
    (((25 / 2 : ℝ) * u ^ 2 + 3 * u ^ 3) *
      (1 + expm1Algorithm2Gamma3Scalar u))

private noncomputable def expm1Algorithm2ThreePointFiveUnitBoundScalarCore
    (u : ℝ) : ℝ :=
  (7 / 2 : ℝ) +
    ((9 : ℝ) * u) / (1 - (3 : ℝ) * u) +
    expm1Algorithm2Gamma3Scalar u / 2 +
    (((25 / 2 : ℝ) * u + 3 * u ^ 2) *
      (1 + expm1Algorithm2Gamma3Scalar u))

/-- The model-indexed local `3.5u` bound is exactly the scalar envelope
evaluated at the model's unit roundoff. -/
theorem expm1Algorithm2ThreePointFiveUnitBound_eq_scalar (fp : FPModel) :
    expm1Algorithm2ThreePointFiveUnitBound fp =
      expm1Algorithm2ThreePointFiveUnitBoundScalar fp.u := by
  simp [expm1Algorithm2ThreePointFiveUnitBound,
    expm1Algorithm2ThreePointFiveUnitBoundScalar,
    expm1Algorithm2Gamma3Scalar, gamma]

private theorem expm1Algorithm2ThreePointFiveUnitBoundScalar_eq_mul_core
    (u : ℝ) :
    expm1Algorithm2ThreePointFiveUnitBoundScalar u =
      u * expm1Algorithm2ThreePointFiveUnitBoundScalarCore u := by
  simp [expm1Algorithm2ThreePointFiveUnitBoundScalar,
    expm1Algorithm2ThreePointFiveUnitBoundScalarCore,
    expm1Algorithm2Gamma3Scalar, div_eq_mul_inv]
  ring

private theorem expm1Algorithm2Gamma3Scalar_continuousAt_zero :
    ContinuousAt expm1Algorithm2Gamma3Scalar 0 := by
  unfold expm1Algorithm2Gamma3Scalar
  have hlin : ContinuousAt (fun u : ℝ => 1 - (3 : ℝ) * u) 0 := by
    exact continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  simpa [div_eq_mul_inv] using
    ((continuousAt_const.mul continuousAt_id).mul (hlin.inv₀ (by norm_num)))

private theorem expm1Algorithm2ThreePointFiveUnitBoundScalarCore_continuousAt_zero :
    ContinuousAt expm1Algorithm2ThreePointFiveUnitBoundScalarCore 0 := by
  have hden : ContinuousAt (fun u : ℝ => 1 - (3 : ℝ) * u) 0 := by
    exact continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hinv : ContinuousAt (fun u : ℝ => (1 - (3 : ℝ) * u)⁻¹) 0 :=
    hden.inv₀ (by norm_num)
  have hterm2 :
      ContinuousAt (fun u : ℝ => ((9 : ℝ) * u) / (1 - (3 : ℝ) * u)) 0 := by
    simpa [div_eq_mul_inv] using
      ((continuousAt_const.mul continuousAt_id).mul hinv)
  have hterm3 :
      ContinuousAt (fun u : ℝ => expm1Algorithm2Gamma3Scalar u / 2) 0 := by
    simpa [div_eq_mul_inv] using
      (expm1Algorithm2Gamma3Scalar_continuousAt_zero.mul continuousAt_const)
  have hpoly :
      ContinuousAt (fun u : ℝ => (25 / 2 : ℝ) * u + 3 * u ^ 2) 0 := by
    have hsq : ContinuousAt (fun u : ℝ => u ^ 2) 0 := by
      simpa [pow_two] using (continuousAt_id.mul continuousAt_id :
        ContinuousAt (fun u : ℝ => u * u) 0)
    exact (continuousAt_const.mul continuousAt_id).add
      (continuousAt_const.mul hsq)
  have honePlus :
      ContinuousAt (fun u : ℝ => 1 + expm1Algorithm2Gamma3Scalar u) 0 :=
    continuousAt_const.add expm1Algorithm2Gamma3Scalar_continuousAt_zero
  have hterm4 :
      ContinuousAt
        (fun u : ℝ => ((25 / 2 : ℝ) * u + 3 * u ^ 2) *
          (1 + expm1Algorithm2Gamma3Scalar u)) 0 :=
    hpoly.mul honePlus
  exact ((continuousAt_const.add hterm2).add hterm3).add hterm4

/-- Literal Landau form of the local Algorithm 2 bound: the named scalar
envelope behind the source's `3.5u` estimate is `O(u)` as `u -> 0`. This is an
interpretation theorem for the local envelope, not a concrete exp/log routine
instantiation. -/
theorem expm1Algorithm2ThreePointFiveUnitBoundScalar_isBigO :
    (fun u : ℝ => expm1Algorithm2ThreePointFiveUnitBoundScalar u)
      =O[𝓝 0] (fun u : ℝ => u) := by
  have hId : (fun u : ℝ => u) =O[𝓝 0] (fun u : ℝ => u) :=
    Asymptotics.isBigO_refl (fun u : ℝ => u) (𝓝 0)
  have hCore :
      (fun u : ℝ => expm1Algorithm2ThreePointFiveUnitBoundScalarCore u)
        =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    expm1Algorithm2ThreePointFiveUnitBoundScalarCore_continuousAt_zero.tendsto.isBigO_one ℝ
  have hMul :
      (fun u : ℝ => u * expm1Algorithm2ThreePointFiveUnitBoundScalarCore u)
        =O[𝓝 0] (fun u : ℝ => u) := by
    simpa using hId.mul hCore
  exact hMul.congr_left
    (fun u => (expm1Algorithm2ThreePointFiveUnitBoundScalar_eq_mul_core u).symm)

/-- The compact local Algorithm 2 unit-radius bound is non-vacuous: when the
unit roundoff is zero, the whole displayed right-hand side vanishes. -/
theorem expm1Algorithm2ThreePointFiveUnitBound_eq_zero_of_u_eq_zero
    (fp : FPModel) (hu : fp.u = 0) :
    expm1Algorithm2ThreePointFiveUnitBound fp = 0 := by
  simp [expm1Algorithm2ThreePointFiveUnitBound, gamma, hu]

theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_abs_bounds
    (fp : FPModel) {y delta logHat epsLog yAbs yhatAbs deltaAbs : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs)
    (hdeltaAbs_le_u : deltaAbs ≤ fp.u)
    (hyAbs_le_u : yAbs ≤ fp.u)
    (hyhatAbs_le_u : yhatAbs ≤ fp.u) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (((25 / 2 : ℝ) * fp.u ^ 2 + 3 * fp.u ^ 3) *
          (1 + gamma fp 3)) := by
  have hu_le_third : fp.u ≤ (1 / 3 : ℝ) := by
    have h := hvalid3
    unfold gammaValid at h
    norm_num at h
    linarith
  have hbase :=
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_bound_of_abs_bounds
      (fp := fp) (y := y) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (yAbs := yAbs) (yhatAbs := yhatAbs)
      (deltaAbs := deltaAbs) (r := fp.u)
      hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 hy hyhat hdelta
      hyAbs_nonneg hyhatAbs_nonneg hdeltaAbs_nonneg hdeltaAbs_le_u
      hyAbs_le_u hyhatAbs_le_u hu_le_third
  calc
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
        ≤ (7 / 2 : ℝ) * fp.u +
          (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
          (fp.u / 2) * gamma fp 3 +
          (2 * (6 * fp.u ^ 2 + (fp.u / 2 + 3 * fp.u ^ 2) * fp.u / 2)) *
            (1 + gamma fp 3) := hbase
    _ =
      (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (((25 / 2 : ℝ) * fp.u ^ 2 + 3 * fp.u ^ 3) *
          (1 + gamma fp 3)) := by
          ring

/-- Direct unit-bound version of the local Algorithm 2 `3.5u` bridge.  This is
the compact local theorem closest to the page-24 estimate: once the actual
local quantities satisfy `|y-1| <= u`, `|yhat-1| <= u`, and `|delta| <= u`,
the rounded Algorithm 2 core has the leading `3.5u` bound plus an explicit
second-order tail. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds
    (fp : FPModel) {y delta logHat epsLog : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hy_u : |y - 1| ≤ fp.u)
    (hyhat_u : |y * (1 + delta) - 1| ≤ fp.u)
    (hdelta_u : |delta| ≤ fp.u) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (((25 / 2 : ℝ) * fp.u ^ 2 + 3 * fp.u ^ 3) *
          (1 + gamma fp 3)) := by
  have hu_le_half : fp.u ≤ (1 / 2 : ℝ) := by
    have h := hvalid3
    unfold gammaValid at h
    norm_num at h
    linarith
  have hySmall : |y - 1| ≤ (1 / 2 : ℝ) := le_trans hy_u hu_le_half
  have hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ) :=
    le_trans hyhat_u hu_le_half
  exact
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_abs_bounds
      (fp := fp) (y := y) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (yAbs := fp.u) (yhatAbs := fp.u)
      (deltaAbs := fp.u)
      hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 hy_u hyhat_u hdelta_u
      fp.u_nonneg fp.u_nonneg fp.u_nonneg le_rfl le_rfl le_rfl

/-- Named-bound version of the compact local Algorithm 2 `3.5u` theorem.
This is the same inequality as
`expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds`,
but with the bulky right-hand side packaged as
`expm1Algorithm2ThreePointFiveUnitBound`. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_unit_bound_of_unit_bounds
    (fp : FPModel) {y delta logHat epsLog : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hy_u : |y - 1| ≤ fp.u)
    (hyhat_u : |y * (1 + delta) - 1| ≤ fp.u)
    (hdelta_u : |delta| ≤ fp.u) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ expm1Algorithm2ThreePointFiveUnitBound fp := by
  simpa [expm1Algorithm2ThreePointFiveUnitBound] using
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds
      (fp := fp) (y := y) (delta := delta) (logHat := logHat)
      (epsLog := epsLog)
      hg hepsLog hlog hlogHat hposLog hvalid3
      hy0 hyhat0 hy_u hyhat_u hdelta_u

/-- Normalized-remainder version of the local Algorithm 2 `3.5u` bridge.  A
future interval or machine-specific proof can now supply only
`S <= rem*|g(y)|`, where `S` is the explicit primitive slow-ratio remainder,
and reuse this theorem directly. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_normalized_remainder_of_abs_bounds
    (fp : FPModel) {y delta logHat epsLog yAbs yhatAbs deltaAbs rem : ℝ}
    (hg : expm1LogRatio y ≠ 0)
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (y * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hySmall : |y - 1| ≤ (1 / 2 : ℝ))
    (hyhatSmall : |y * (1 + delta) - 1| ≤ (1 / 2 : ℝ))
    (hy0 : y ≠ 1) (hyhat0 : y * (1 + delta) ≠ 1)
    (hy : |y - 1| ≤ yAbs)
    (hyhat : |y * (1 + delta) - 1| ≤ yhatAbs)
    (hdelta : |delta| ≤ deltaAbs)
    (hyAbs_nonneg : 0 ≤ yAbs)
    (hyhatAbs_nonneg : 0 ≤ yhatAbs)
    (hdeltaAbs_nonneg : 0 ≤ deltaAbs)
    (hdeltaAbs_le_u : deltaAbs ≤ fp.u)
    (hrem :
      expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs ≤
        rem * |expm1LogRatio y|) :
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        rem * (1 + gamma fp 3) := by
  let S := expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs
  let g := expm1LogRatio y
  have hlocal :=
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds
      (fp := fp) (y := y) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (yAbs := yAbs) (yhatAbs := yhatAbs)
      (deltaAbs := deltaAbs)
      hg hepsLog hlog hlogHat hposLog hvalid3
      hySmall hyhatSmall hy0 hyhat0 hy hyhat hdelta
      hyAbs_nonneg hyhatAbs_nonneg hdeltaAbs_nonneg hdeltaAbs_le_u
  have hden_pos : 0 < |g| := abs_pos.mpr (by simpa [g] using hg)
  have hrem_div : S / |g| ≤ rem := by
    have hrem' : S ≤ rem * |g| := by simpa [S, g] using hrem
    calc
      S / |g| ≤ (rem * |g|) / |g| :=
        div_le_div_of_nonneg_right hrem' (le_of_lt hden_pos)
      _ = rem := by field_simp [hden_pos.ne']
  have hfactor_nonneg : 0 ≤ 1 + gamma fp 3 := by
    have hgamma_nonneg : 0 ≤ gamma fp 3 := gamma_nonneg fp hvalid3
    linarith
  have htail :
      (S / |g|) * (1 + gamma fp 3) ≤ rem * (1 + gamma fp 3) :=
    mul_le_mul_of_nonneg_right hrem_div hfactor_nonneg
  calc
    relError
        (expm1Algorithm2RoundedCore fp (y * (1 + delta)) logHat)
        (expm1LogRatio y)
        ≤ (7 / 2 : ℝ) * fp.u +
          (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
          (fp.u / 2) * gamma fp 3 +
          (S / |g|) * (1 + gamma fp 3) := by
            simpa [S, g] using hlocal
    _ ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        rem * (1 + gamma fp 3) := by
          linarith

end NumStability
