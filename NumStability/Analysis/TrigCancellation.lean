-- Analysis/TrigCancellation.lean
--
-- Exact trigonometric cancellation algebra for Higham Chapter 1, Section 1.7.

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

/-!
# Trigonometric Cancellation Algebra

Higham Chapter 1, Section 1.7 uses `1 - cos x` to illustrate cancellation and
the stable exact rewrite `2 * sin (x/2)^2`.  This file records the exact
real-arithmetic identity, the supplied-error comparison of the two evaluation
paths, and finite round-to-even wrappers for the trigonometric outputs under
finite-normal hypotheses.  It also records the exact cancellation-avoiding
rewrites from Problem 1.3.
-/

/-- Exact half-angle rewrite behind the stable evaluation of `1 - cos x`. -/
theorem one_sub_cos_eq_two_sin_sq_half (x : ℝ) :
    1 - Real.cos x = 2 * (Real.sin (x / 2)) ^ 2 := by
  rw [Real.sin_sq_eq_half_sub]
  rw [show 2 * (x / 2) = x by ring]
  ring

/-- Consequently, the exact expression `1 - cos x` is nonnegative. -/
theorem one_sub_cos_nonneg_exact (x : ℝ) :
    0 ≤ 1 - Real.cos x := by
  rw [one_sub_cos_eq_two_sin_sq_half]
  exact mul_nonneg (by norm_num) (sq_nonneg _)

-- ============================================================
-- Higham §1.7 scaled target and cancellation-amplification bounds
-- ============================================================

/-- The scaled target `f(x) = (1 - cos x) / x^2` from the cancellation
example.  Lean's total division makes the value at `x = 0` equal to `0`;
the source discussion uses `x != 0`. -/
noncomputable def trigCancellationExactScaled (x : ℝ) : ℝ :=
  (1 - Real.cos x) / x ^ 2

/-- Direct scaled path when a cosine approximation `c` has already been
supplied. -/
noncomputable def trigCancellationDirectScaledFromCos (x c : ℝ) : ℝ :=
  (1 - c) / x ^ 2

/-- Cancellation-avoiding scaled path when an approximation to `sin (x/2)` has
already been supplied. -/
noncomputable def trigCancellationRewriteScaledFromSinHalf (x s : ℝ) : ℝ :=
  2 * s ^ 2 / x ^ 2

/-- The scaled target is nonnegative. -/
theorem trigCancellationExactScaled_nonneg (x : ℝ) :
    0 ≤ trigCancellationExactScaled x := by
  exact div_nonneg (one_sub_cos_nonneg_exact x) (sq_nonneg x)

/-- Higham's upper range fact for the cancellation example: the scaled target
is at most `1/2`. -/
theorem trigCancellationExactScaled_le_half (x : ℝ) :
    trigCancellationExactScaled x ≤ (1 : ℝ) / 2 := by
  by_cases hx : x = 0
  · simp [trigCancellationExactScaled, hx]
  · have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hnum : 1 - Real.cos x ≤ x ^ 2 / 2 := by
      have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
      linarith
    have hdiv := div_le_div_of_nonneg_right hnum (sq_nonneg x)
    have hsimp : (x ^ 2 / 2) / x ^ 2 = (1 : ℝ) / 2 := by
      field_simp [ne_of_gt hx2pos]
    simpa [trigCancellationExactScaled, hsimp] using hdiv

/-- For nonzero `x`, the scaled target is strictly below `1/2`. -/
theorem trigCancellationExactScaled_lt_half (x : ℝ) (hx : x ≠ 0) :
    trigCancellationExactScaled x < (1 : ℝ) / 2 := by
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hnum : 1 - Real.cos x < x ^ 2 / 2 := by
    have hcos := Real.one_sub_sq_div_two_lt_cos (x := x) hx
    linarith
  have hdiv := div_lt_div_of_pos_right hnum hx2pos
  have hsimp : (x ^ 2 / 2) / x ^ 2 = (1 : ℝ) / 2 := by
    field_simp [ne_of_gt hx2pos]
  simpa [trigCancellationExactScaled, hsimp] using hdiv

/-- The lower bound is strict whenever the cosine value is not exactly `1`. -/
theorem trigCancellationExactScaled_pos_of_cos_ne_one (x : ℝ)
    (hx : x ≠ 0) (hcos : Real.cos x ≠ 1) :
    0 < trigCancellationExactScaled x := by
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hcos_lt : Real.cos x < 1 :=
    lt_of_le_of_ne (Real.cos_le_one x) hcos
  have hnum : 0 < 1 - Real.cos x := by linarith
  exact div_pos hnum hx2pos

/-- A perturbation of the supplied cosine is divided by `x^2` in the direct
scaled formula.  This is the precise cancellation-amplification mechanism in
§1.7. -/
theorem trigCancellationDirectScaledFromCos_abs_error_le
    (x c eta : ℝ) (hx : x ≠ 0) (_heta : 0 ≤ eta)
    (hc : |c - Real.cos x| ≤ eta) :
    |trigCancellationDirectScaledFromCos x c - trigCancellationExactScaled x| ≤
      eta / x ^ 2 := by
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hdiff :
      trigCancellationDirectScaledFromCos x c - trigCancellationExactScaled x =
        (Real.cos x - c) / x ^ 2 := by
    unfold trigCancellationDirectScaledFromCos trigCancellationExactScaled
    rw [← sub_div]
    congr 1
    ring
  have hc' : |Real.cos x - c| ≤ eta := by
    simpa [abs_sub_comm] using hc
  rw [hdiff, abs_div, abs_of_nonneg (sq_nonneg x)]
  exact div_le_div_of_nonneg_right hc' (le_of_lt hx2pos)

/-- Squaring a supplied scalar with absolute error `eta` incurs a first-order
factor proportional to the exact scalar plus a quadratic `eta^2` term. -/
theorem sq_abs_error_le_of_abs_sub_le (s t eta : ℝ)
    (heta : 0 ≤ eta) (hst : |s - t| ≤ eta) :
    |s ^ 2 - t ^ 2| ≤ eta * (2 * |t| + eta) := by
  have hsum : |s + t| ≤ eta + 2 * |t| := by
    have hrewrite : s + t = (s - t) + 2 * t := by ring
    calc
      |s + t| = |(s - t) + 2 * t| := by rw [hrewrite]
      _ ≤ |s - t| + |2 * t| := abs_add_le _ _
      _ ≤ eta + 2 * |t| := by
        have htwo : |(2 : ℝ) * t| = 2 * |t| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        rw [htwo]
        linarith
  have hprod :
      |s - t| * |s + t| ≤ eta * (eta + 2 * |t|) :=
    mul_le_mul hst hsum (abs_nonneg _) heta
  calc
    |s ^ 2 - t ^ 2| = |(s - t) * (s + t)| := by
      congr 1
      ring
    _ = |s - t| * |s + t| := abs_mul _ _
    _ ≤ eta * (eta + 2 * |t|) := hprod
    _ = eta * (2 * |t| + eta) := by ring

/-- The cancellation-avoiding half-angle path has an absolute-error bound
driven by the supplied sine-half error rather than by subtracting two nearly
equal numbers. -/
theorem trigCancellationRewriteScaledFromSinHalf_abs_error_le
    (x s eta : ℝ) (hx : x ≠ 0) (heta : 0 ≤ eta)
    (hs : |s - Real.sin (x / 2)| ≤ eta) :
    |trigCancellationRewriteScaledFromSinHalf x s -
        trigCancellationExactScaled x| ≤
      (2 * eta * (2 * |Real.sin (x / 2)| + eta)) / x ^ 2 := by
  let t : ℝ := Real.sin (x / 2)
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hsq : |s ^ 2 - t ^ 2| ≤ eta * (2 * |t| + eta) := by
    exact sq_abs_error_le_of_abs_sub_le s t eta heta (by simpa [t] using hs)
  have hdiff :
      trigCancellationRewriteScaledFromSinHalf x s -
          trigCancellationExactScaled x =
        (2 * (s ^ 2 - t ^ 2)) / x ^ 2 := by
    unfold trigCancellationRewriteScaledFromSinHalf trigCancellationExactScaled
    rw [one_sub_cos_eq_two_sin_sq_half x]
    change 2 * s ^ 2 / x ^ 2 - 2 * t ^ 2 / x ^ 2 =
      2 * (s ^ 2 - t ^ 2) / x ^ 2
    rw [← sub_div]
    congr 1
    ring
  have hmul : 2 * |s ^ 2 - t ^ 2| ≤ 2 * (eta * (2 * |t| + eta)) :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  rw [hdiff, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg x)]
  have hdiv := div_le_div_of_nonneg_right hmul (sq_nonneg x)
  simpa [t, mul_assoc] using hdiv

/-- If the sine-half approximation budget is small enough, the rewritten
scaled formula is no worse than a direct-path cosine-error budget. -/
theorem trigCancellationRewriteScaledFromSinHalf_abs_error_le_direct_cos_bound
    (x s etaSin etaCos : ℝ) (hx : x ≠ 0) (hetaSin : 0 ≤ etaSin)
    (hs : |s - Real.sin (x / 2)| ≤ etaSin)
    (hbudget :
      2 * etaSin * (2 * |Real.sin (x / 2)| + etaSin) ≤ etaCos) :
    |trigCancellationRewriteScaledFromSinHalf x s -
        trigCancellationExactScaled x| ≤ etaCos / x ^ 2 := by
  have hrew :=
    trigCancellationRewriteScaledFromSinHalf_abs_error_le
      x s etaSin hx hetaSin hs
  have hscale :
      (2 * etaSin * (2 * |Real.sin (x / 2)| + etaSin)) / x ^ 2 ≤
        etaCos / x ^ 2 :=
    div_le_div_of_nonneg_right hbudget (sq_nonneg x)
  exact le_trans hrew hscale

-- ============================================================
-- Higham §1.7 finite round-to-even trigonometric routine wrappers
-- ============================================================

/-- Finite round-to-even cosine output for the direct `1 - cos x` path. -/
noncomputable def trigCancellationFiniteRoundToEvenCos
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  fmt.finiteRoundToEven (Real.cos x)

/-- Finite round-to-even sine-half output for the cancellation-avoiding path. -/
noncomputable def trigCancellationFiniteRoundToEvenSinHalf
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  fmt.finiteRoundToEven (Real.sin (x / 2))

/-- Direct scaled path using a finite round-to-even cosine output. -/
noncomputable def trigCancellationDirectScaledFiniteRoundToEvenCos
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  trigCancellationDirectScaledFromCos x
    (trigCancellationFiniteRoundToEvenCos fmt x)

/-- Cancellation-avoiding scaled path using a finite round-to-even sine-half
output. -/
noncomputable def trigCancellationRewriteScaledFiniteRoundToEvenSinHalf
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  trigCancellationRewriteScaledFromSinHalf x
    (trigCancellationFiniteRoundToEvenSinHalf fmt x)

/-- Finite-normal round-to-even cosine supplies the direct-path absolute-error
budget consumed by the §1.7 cancellation-amplification theorem. -/
theorem trigCancellationFiniteRoundToEvenCos_abs_error_le
    (fmt : FloatingPointFormat) (x : ℝ)
    (hcosnormal : fmt.finiteNormalRange (Real.cos x)) :
    |trigCancellationFiniteRoundToEvenCos fmt x - Real.cos x| ≤
      fmt.unitRoundoff * |Real.cos x| := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hcosnormal with
    ⟨delta, _hround, hdelta, hwit⟩
  have hrel :
      trigCancellationFiniteRoundToEvenCos fmt x =
        Real.cos x * (1 + delta) := by
    simpa [trigCancellationFiniteRoundToEvenCos, signedRelErrorWitness]
      using hwit
  have hdiff :
      trigCancellationFiniteRoundToEvenCos fmt x - Real.cos x =
        Real.cos x * delta := by
    rw [hrel]
    ring
  calc
    |trigCancellationFiniteRoundToEvenCos fmt x - Real.cos x|
        = |Real.cos x| * |delta| := by
          rw [hdiff, abs_mul]
    _ = |delta| * |Real.cos x| := by ring
    _ ≤ fmt.unitRoundoff * |Real.cos x| :=
        mul_le_mul_of_nonneg_right (le_of_lt hdelta) (abs_nonneg _)

/-- Finite-normal round-to-even sine-half supplies the cancellation-avoiding
path's absolute-error budget. -/
theorem trigCancellationFiniteRoundToEvenSinHalf_abs_error_le
    (fmt : FloatingPointFormat) (x : ℝ)
    (hsinnormal : fmt.finiteNormalRange (Real.sin (x / 2))) :
    |trigCancellationFiniteRoundToEvenSinHalf fmt x - Real.sin (x / 2)| ≤
      fmt.unitRoundoff * |Real.sin (x / 2)| := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hsinnormal with
    ⟨delta, _hround, hdelta, hwit⟩
  have hrel :
      trigCancellationFiniteRoundToEvenSinHalf fmt x =
        Real.sin (x / 2) * (1 + delta) := by
    simpa [trigCancellationFiniteRoundToEvenSinHalf, signedRelErrorWitness]
      using hwit
  have hdiff :
      trigCancellationFiniteRoundToEvenSinHalf fmt x - Real.sin (x / 2) =
        Real.sin (x / 2) * delta := by
    rw [hrel]
    ring
  calc
    |trigCancellationFiniteRoundToEvenSinHalf fmt x - Real.sin (x / 2)|
        = |Real.sin (x / 2)| * |delta| := by
          rw [hdiff, abs_mul]
    _ = |delta| * |Real.sin (x / 2)| := by ring
    _ ≤ fmt.unitRoundoff * |Real.sin (x / 2)| :=
        mul_le_mul_of_nonneg_right (le_of_lt hdelta) (abs_nonneg _)

/-- Direct scaled §1.7 error bound specialized to finite round-to-even cosine. -/
theorem trigCancellationDirectScaledFiniteRoundToEvenCos_abs_error_le
    (fmt : FloatingPointFormat) (x : ℝ) (hx : x ≠ 0)
    (hcosnormal : fmt.finiteNormalRange (Real.cos x)) :
    |trigCancellationDirectScaledFiniteRoundToEvenCos fmt x -
        trigCancellationExactScaled x| ≤
      (fmt.unitRoundoff * |Real.cos x|) / x ^ 2 := by
  exact
    trigCancellationDirectScaledFromCos_abs_error_le
      x (trigCancellationFiniteRoundToEvenCos fmt x)
      (fmt.unitRoundoff * |Real.cos x|) hx
      (mul_nonneg fmt.unitRoundoff_nonneg (abs_nonneg _))
      (trigCancellationFiniteRoundToEvenCos_abs_error_le fmt x hcosnormal)

/-- Cancellation-avoiding scaled §1.7 error bound specialized to finite
round-to-even sine-half. -/
theorem trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le
    (fmt : FloatingPointFormat) (x : ℝ) (hx : x ≠ 0)
    (hsinnormal : fmt.finiteNormalRange (Real.sin (x / 2))) :
    |trigCancellationRewriteScaledFiniteRoundToEvenSinHalf fmt x -
        trigCancellationExactScaled x| ≤
      (2 * (fmt.unitRoundoff * |Real.sin (x / 2)|) *
          (2 * |Real.sin (x / 2)| +
            fmt.unitRoundoff * |Real.sin (x / 2)|)) / x ^ 2 := by
  exact
    trigCancellationRewriteScaledFromSinHalf_abs_error_le
      x (trigCancellationFiniteRoundToEvenSinHalf fmt x)
      (fmt.unitRoundoff * |Real.sin (x / 2)|) hx
      (mul_nonneg fmt.unitRoundoff_nonneg (abs_nonneg _))
      (trigCancellationFiniteRoundToEvenSinHalf_abs_error_le fmt x hsinnormal)

/-- Finite round-to-even version of the source's direct-vs-rewritten
comparison criterion. -/
theorem trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le_direct_cos_bound
    (fmt : FloatingPointFormat) (x : ℝ) (hx : x ≠ 0)
    (hsinnormal : fmt.finiteNormalRange (Real.sin (x / 2)))
    (hbudget :
      2 * (fmt.unitRoundoff * |Real.sin (x / 2)|) *
          (2 * |Real.sin (x / 2)| +
            fmt.unitRoundoff * |Real.sin (x / 2)|) ≤
        fmt.unitRoundoff * |Real.cos x|) :
    |trigCancellationRewriteScaledFiniteRoundToEvenSinHalf fmt x -
        trigCancellationExactScaled x| ≤
      (fmt.unitRoundoff * |Real.cos x|) / x ^ 2 := by
  exact
    trigCancellationRewriteScaledFromSinHalf_abs_error_le_direct_cos_bound
      x (trigCancellationFiniteRoundToEvenSinHalf fmt x)
      (fmt.unitRoundoff * |Real.sin (x / 2)|)
      (fmt.unitRoundoff * |Real.cos x|) hx
      (mul_nonneg fmt.unitRoundoff_nonneg (abs_nonneg _))
      (trigCancellationFiniteRoundToEvenSinHalf_abs_error_le fmt x hsinnormal)
      hbudget

-- ============================================================
-- Higham Problem 1.3 cancellation-avoiding rewrites
-- ============================================================

/-- Problem 1.3(1): rationalize `sqrt(1+x)-1` near `x = 0`. -/
theorem problem_1_3_sqrt_one_add_sub_one (x : ℝ) (hx : 0 ≤ x + 1) :
    Real.sqrt (x + 1) - 1 = x / (Real.sqrt (x + 1) + 1) := by
  have hden : Real.sqrt (x + 1) + 1 ≠ 0 := by
    have hs : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
    linarith
  rw [eq_div_iff hden]
  have hs : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt hx
  calc
    (Real.sqrt (x + 1) - 1) * (Real.sqrt (x + 1) + 1)
        = Real.sqrt (x + 1) ^ 2 - 1 := by ring
    _ = x := by
      rw [hs]
      ring

/-- Problem 1.3(2): rewrite `sin x - sin y` when `x ≈ y`. -/
theorem problem_1_3_sin_sub_sin (x y : ℝ) :
    Real.sin x - Real.sin y =
      2 * Real.cos ((x + y) / 2) * Real.sin ((x - y) / 2) := by
  rw [Real.sin_sub_sin]
  ring

/-- Problem 1.3(3): factor `x^2-y^2` when `x ≈ y`. -/
theorem problem_1_3_sq_sub_sq (x y : ℝ) :
    x ^ 2 - y ^ 2 = (x - y) * (x + y) := by
  ring

/-- Problem 1.3(4): rewrite `(1-cos x)/sin x` near `x = 0`. -/
theorem problem_1_3_one_sub_cos_div_sin (x : ℝ)
    (hsin : Real.sin x ≠ 0) (hcos : 1 + Real.cos x ≠ 0) :
    (1 - Real.cos x) / Real.sin x = Real.sin x / (1 + Real.cos x) := by
  field_simp [hsin, hcos]
  have h : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    have hmain := Real.sin_sq_add_cos_sq x
    linarith
  rw [h]
  ring

/-- Problem 1.3(5): first exact radicand rewrite for the law-of-cosines
expression when `a ≈ b` and `theta` is small. -/
theorem problem_1_3_lawOfCosines_radicand_sub_rewrite (a b theta : ℝ) :
    a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta =
      (a - b) ^ 2 + 2 * a * b * (1 - Real.cos theta) := by
  ring

/-- Problem 1.3(5): half-angle radicand rewrite for the law-of-cosines
expression when `a ≈ b` and `theta` is small. -/
theorem problem_1_3_lawOfCosines_radicand_halfAngle (a b theta : ℝ) :
    a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta =
      (a - b) ^ 2 + 4 * a * b * (Real.sin (theta / 2)) ^ 2 := by
  calc
    a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta
        = (a - b) ^ 2 + 2 * a * b * (1 - Real.cos theta) := by
      ring
    _ = (a - b) ^ 2 + 4 * a * b * (Real.sin (theta / 2)) ^ 2 := by
      rw [one_sub_cos_eq_two_sin_sq_half theta]
      ring

/-- Problem 1.3(5): square-root form of the law-of-cosines half-angle rewrite. -/
theorem problem_1_3_lawOfCosines_sqrt_halfAngle (a b theta : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta) =
      Real.sqrt ((a - b) ^ 2 + 4 * a * b * (Real.sin (theta / 2)) ^ 2) := by
  congr 1
  exact problem_1_3_lawOfCosines_radicand_halfAngle a b theta

-- ============================================================
-- Higham §1.7 displayed ten-significant-figure example
-- ============================================================

/-- The input `x = 1.2 * 10^{-5}` from the Chapter 1 cancellation example. -/
noncomputable def trigCancellationExampleX : ℝ :=
  (12 : ℝ) / 1000000

/-- The displayed ten-significant-figure cosine approximation
`c = 0.9999999999`. -/
noncomputable def trigCancellationExampleCos10 : ℝ :=
  (9999999999 : ℝ) / 10000000000

/-- The displayed ten-significant-figure sine-half approximation
`sin(x/2) ≈ 0.0000060000`. -/
noncomputable def trigCancellationExampleSinHalf10 : ℝ :=
  (6 : ℝ) / 1000000

/-- The direct cancellation path `(1 - c) / x^2` for the displayed decimal data. -/
noncomputable def trigCancellationDirectScaled : ℝ :=
  (1 - trigCancellationExampleCos10) / trigCancellationExampleX ^ 2

/-- The rewritten path `2*s^2 / x^2` for the displayed decimal data. -/
noncomputable def trigCancellationRewriteScaled : ℝ :=
  2 * trigCancellationExampleSinHalf10 ^ 2 / trigCancellationExampleX ^ 2

/-- In the displayed example, the direct formula gives `25/36 = 0.6944...`. -/
theorem trigCancellationDirectScaled_eq :
    trigCancellationDirectScaled = (25 : ℝ) / 36 := by
  norm_num [trigCancellationDirectScaled, trigCancellationExampleCos10,
    trigCancellationExampleX]

/-- The displayed direct result is not the correct limiting value `1/2`. -/
theorem trigCancellationDirectScaled_ne_half :
    trigCancellationDirectScaled ≠ (1 : ℝ) / 2 := by
  rw [trigCancellationDirectScaled_eq]
  norm_num

/-- In the displayed example, the rewritten sine-half formula gives `1/2`. -/
theorem trigCancellationRewriteScaled_eq_half :
    trigCancellationRewriteScaled = (1 : ℝ) / 2 := by
  norm_num [trigCancellationRewriteScaled, trigCancellationExampleSinHalf10,
    trigCancellationExampleX]

end NumStability
