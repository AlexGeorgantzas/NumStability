import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.OuterProduct
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.Rounding
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.Analysis.Stability
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Analysis.Summation.Signs
import NumStability.FloatingPoint.Model

namespace NumStability

/-!
# IncreasingPrecision

Extracted without change from IncreasingPrecision.
-/

/-- The exact function `x + a*sin(b*x)` from Higham §1.13. -/
noncomputable def increasingPrecisionSinExample (x a b : ℝ) : ℝ :=
  x + a * Real.sin (b * x)
/-- The source amplitude `a = 10^{-8}` in Higham §1.13's sine example. -/
noncomputable def increasingPrecisionSinExampleScale : ℝ :=
  1 / (10 : ℝ) ^ 8
/-- The source frequency `b = 2^{24}` in Higham §1.13's sine example. -/
noncomputable def increasingPrecisionSinExampleFrequency : ℝ :=
  (2 : ℝ) ^ 24
/-- The source instance `x + 10^{-8} sin(2^{24} x)` from Higham §1.13. -/
noncomputable def increasingPrecisionSinExampleSource (x : ℝ) : ℝ :=
  increasingPrecisionSinExample x increasingPrecisionSinExampleScale
    increasingPrecisionSinExampleFrequency
/-- The sine-example perturbation has magnitude at most the amplitude. -/
theorem increasingPrecisionSinExample_perturbation_abs_le
    (x a b : ℝ) :
    |increasingPrecisionSinExample x a b - x| ≤ |a| := by
  rw [show increasingPrecisionSinExample x a b - x =
      a * Real.sin (b * x) by
    simp [increasingPrecisionSinExample]]
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg a) (Real.abs_sin_le_one (b * x))
/-- In the source instance, the exact perturbation from `x` is at most
`10^{-8}` in absolute value. -/
theorem increasingPrecisionSinExampleSource_perturbation_abs_le
    (x : ℝ) :
    |increasingPrecisionSinExampleSource x - x| ≤ 1 / (10 : ℝ) ^ 8 := by
  have h :=
    increasingPrecisionSinExample_perturbation_abs_le x
      increasingPrecisionSinExampleScale increasingPrecisionSinExampleFrequency
  have hscale_nonneg : 0 ≤ 1 / (10 : ℝ) ^ 8 := by norm_num
  simpa [increasingPrecisionSinExampleSource, increasingPrecisionSinExampleScale,
    increasingPrecisionSinExampleFrequency, abs_of_nonneg hscale_nonneg] using h
/-- If a finite value is strictly closer to the source than every other finite
value, the finite round-to-even selector returns it.  This is a compact
certificate interface for plateau-style examples. -/
theorem finiteRoundToEven_eq_of_strict_closest
    {fmt : FloatingPointFormat} {source base : ℝ}
    (hbase : fmt.finiteSystem base)
    (hstrict : ∀ z : ℝ, fmt.finiteSystem z → z ≠ base →
      |source - base| < |source - z|) :
    fmt.finiteRoundToEven source = base := by
  have hround := fmt.finiteRoundToEven_nearestRoundingToFinite source
  by_contra hne
  have hfin : fmt.finiteSystem (fmt.finiteRoundToEven source) :=
    FloatingPointFormat.nearestRoundingIn_mem hround
  have hlt :=
    hstrict (fmt.finiteRoundToEven source) hfin hne
  have hle :=
    FloatingPointFormat.nearestRoundingIn_minimal hround hbase
  linarith
/-- A spacing certificate for the §1.13 sine example.  If the base point `x`
is finite and every other finite-format number is more than twice the amplitude
away from `x`, then rounding `x + a*sin(b*x)` returns `x`. -/
theorem increasingPrecisionSinExample_finiteRoundToEven_eq_base_of_two_abs_scale_lt_spacing
    (fmt : FloatingPointFormat) {x a b : ℝ}
    (hxfin : fmt.finiteSystem x)
    (hspacing : ∀ z : ℝ, fmt.finiteSystem z → z ≠ x →
      2 * |a| < |z - x|) :
    fmt.finiteRoundToEven (increasingPrecisionSinExample x a b) = x := by
  apply finiteRoundToEven_eq_of_strict_closest hxfin
  intro z hz hzx
  have hpert :=
    increasingPrecisionSinExample_perturbation_abs_le x a b
  have htri :
      |z - x| ≤
        |z - increasingPrecisionSinExample x a b| +
          |increasingPrecisionSinExample x a b - x| := by
    calc
      |z - x| =
          |(z - increasingPrecisionSinExample x a b) +
            (increasingPrecisionSinExample x a b - x)| := by ring_nf
      _ ≤ |z - increasingPrecisionSinExample x a b| +
            |increasingPrecisionSinExample x a b - x| := abs_add_le _ _
  have hsep := hspacing z hz hzx
  have hsrcz_gt_z : |a| < |z - increasingPrecisionSinExample x a b| := by
    linarith
  have hsrcz_gt : |a| < |increasingPrecisionSinExample x a b - z| := by
    simpa [abs_sub_comm] using hsrcz_gt_z
  exact lt_of_le_of_lt hpert hsrcz_gt
/-- Source-instance spacing certificate for Higham's
`x + 10^{-8} sin(2^24*x)` example.  A point whose finite-format neighbors are
all farther than `2*10^{-8}` rounds back to the unperturbed `x`; the remaining
machine-specific plateau work is therefore the local spacing certificate, not
an enumeration of inputs. -/
theorem increasingPrecisionSinExampleSource_finiteRoundToEven_eq_base_of_spacing
    (fmt : FloatingPointFormat) {x : ℝ}
    (hxfin : fmt.finiteSystem x)
    (hspacing : ∀ z : ℝ, fmt.finiteSystem z → z ≠ x →
      2 / (10 : ℝ) ^ 8 < |z - x|) :
    fmt.finiteRoundToEven (increasingPrecisionSinExampleSource x) = x := by
  apply increasingPrecisionSinExample_finiteRoundToEven_eq_base_of_two_abs_scale_lt_spacing
    fmt hxfin
  intro z hz hzx
  have h := hspacing z hz hzx
  simpa [increasingPrecisionSinExampleSource, increasingPrecisionSinExampleScale,
    increasingPrecisionSinExampleFrequency] using h
/-- The branch variable
`y = abs(3*(x-0.5)-0.5)/25` from Higham §1.13. -/
noncomputable def increasingPrecisionExampleY (x : ℝ) : ℝ :=
  |3 * (x - 1 / 2) - 1 / 2| / 25
/-- The exact-arithmetic version of the §1.13 branch computation. -/
noncomputable def increasingPrecisionExampleExactZ (x : ℝ) : ℝ :=
  let y := increasingPrecisionExampleY x
  if y = 0 then 1 else (Real.exp y - 1) / y
/-- The else-branch result when the computed exponential value is supplied
separately.  This isolates the modeled fact used in the text: a tiny nonzero
`y` can have `exp(y)` rounded to `1`. -/
noncomputable def increasingPrecisionExampleElseWithExpHat
    (y expHat : ℝ) : ℝ :=
  (expHat - 1) / y
/-- In exact arithmetic, the branch variable is zero at `x = 2/3`. -/
theorem increasingPrecisionExampleY_two_thirds_eq_zero :
    increasingPrecisionExampleY (2 / 3) = 0 := by
  unfold increasingPrecisionExampleY
  norm_num
/-- Away from the exact source input `x = 2/3`, the branch variable is nonzero.
This is the exact condition that forces the contrived §1.13 computation into
the else branch when the stored input is not exactly `2/3`. -/
theorem increasingPrecisionExampleY_ne_zero_of_ne_two_thirds {x : ℝ}
    (hx : x ≠ 2 / 3) :
    increasingPrecisionExampleY x ≠ 0 := by
  unfold increasingPrecisionExampleY
  intro hzero
  have harg : 3 * (x - 1 / 2) - 1 / 2 = 0 := by
    have hmul := congrArg (fun t : ℝ => t * 25) hzero
    norm_num [div_eq_mul_inv] at hmul
    exact hmul
  apply hx
  linarith
/-- Away from `x = 2/3`, the §1.13 branch variable is strictly positive. -/
theorem increasingPrecisionExampleY_pos_of_ne_two_thirds {x : ℝ}
    (hx : x ≠ 2 / 3) :
    0 < increasingPrecisionExampleY x := by
  have hnonneg : 0 ≤ increasingPrecisionExampleY x := by
    unfold increasingPrecisionExampleY
    exact div_nonneg (abs_nonneg _) (by norm_num)
  have hne := increasingPrecisionExampleY_ne_zero_of_ne_two_thirds hx
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)
/-- Hence the exact-arithmetic branch computation returns `1` at `x = 2/3`. -/
theorem increasingPrecisionExampleExactZ_two_thirds_eq_one :
    increasingPrecisionExampleExactZ (2 / 3) = 1 := by
  unfold increasingPrecisionExampleExactZ
  rw [increasingPrecisionExampleY_two_thirds_eq_zero]
  simp
/-- If the else branch is taken and the exponential evaluation rounds to `1`,
the modeled returned value is `0`. -/
theorem increasingPrecisionExampleElseWithExpHat_one_eq_zero (y : ℝ) :
    increasingPrecisionExampleElseWithExpHat y 1 = 0 := by
  simp [increasingPrecisionExampleElseWithExpHat]
/-- Relative to the exact value `1`, the modeled else-branch value `0` has
relative error `1`. -/
theorem increasingPrecisionExampleElse_relError_one_of_expHat_one {y : ℝ}
    (_hy : y ≠ 0) :
    relError (increasingPrecisionExampleElseWithExpHat y 1) 1 = 1 := by
  simp [increasingPrecisionExampleElseWithExpHat, relError]
/-- Two modeled precision runs can both have no beneficial accuracy change in
the contrived §1.13 example.  If each run enters the else branch with nonzero
`y` and its supplied exponential evaluation is `1`, then both returned values
are `0`, and both have relative error `1` against the exact value
`f(2/3) = 1`.  This is the abstract bridge behind the source's single/double
Fortran observation; it does not derive those supplied exponential values from
a machine model. -/
theorem increasingPrecisionExampleElse_two_precision_failure_of_expHat_one
    {yLow yHigh : ℝ} (hLow : yLow ≠ 0) (hHigh : yHigh ≠ 0) :
    increasingPrecisionExampleElseWithExpHat yLow 1 = 0 ∧
    increasingPrecisionExampleElseWithExpHat yHigh 1 = 0 ∧
    relError (increasingPrecisionExampleElseWithExpHat yLow 1)
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 ∧
    relError (increasingPrecisionExampleElseWithExpHat yHigh 1)
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 := by
  constructor
  · exact increasingPrecisionExampleElseWithExpHat_one_eq_zero yLow
  constructor
  · exact increasingPrecisionExampleElseWithExpHat_one_eq_zero yHigh
  constructor
  · rw [increasingPrecisionExampleExactZ_two_thirds_eq_one]
    exact increasingPrecisionExampleElse_relError_one_of_expHat_one hLow
  · rw [increasingPrecisionExampleExactZ_two_thirds_eq_one]
    exact increasingPrecisionExampleElse_relError_one_of_expHat_one hHigh
/-- A source-shaped version of
`increasingPrecisionExampleElse_two_precision_failure_of_expHat_one`: if two
stored inputs both miss the exact value `2/3`, their branch variables are
nonzero, so the supplied `exp(y)`-rounds-to-`1` model makes both precision runs
return `0` with relative error `1` against the exact value `f(2/3)=1`. -/
theorem increasingPrecisionExampleElse_two_precision_failure_of_stored_inputs_expHat_one
    {xLow xHigh : ℝ} (hLow : xLow ≠ 2 / 3) (hHigh : xHigh ≠ 2 / 3) :
    increasingPrecisionExampleElseWithExpHat (increasingPrecisionExampleY xLow) 1 = 0 ∧
    increasingPrecisionExampleElseWithExpHat (increasingPrecisionExampleY xHigh) 1 = 0 ∧
    relError
      (increasingPrecisionExampleElseWithExpHat (increasingPrecisionExampleY xLow) 1)
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 ∧
    relError
      (increasingPrecisionExampleElseWithExpHat (increasingPrecisionExampleY xHigh) 1)
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 := by
  exact increasingPrecisionExampleElse_two_precision_failure_of_expHat_one
    (increasingPrecisionExampleY_ne_zero_of_ne_two_thirds hLow)
    (increasingPrecisionExampleY_ne_zero_of_ne_two_thirds hHigh)
/-- At the next dyadic exponent the universal `1/(7*2^t)` lower bound is already
below the source amplitude.  This records the sharp arithmetic scale behind the
source phrase "less than about 20". -/
theorem increasingPrecision_one_seventh_binary_grid_lower_bound_lt_scale_at_twenty_four :
    1 / (7 * (2 : ℝ) ^ 24) < increasingPrecisionSinExampleScale := by
  norm_num [increasingPrecisionSinExampleScale]

end NumStability
