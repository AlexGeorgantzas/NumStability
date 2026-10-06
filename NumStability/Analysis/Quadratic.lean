-- Analysis/Quadratic.lean
--
-- Exact quadratic-equation algebra for Higham Chapter 1, Section 1.8.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.Rounding

namespace NumStability

/-!
# Quadratic Equation Algebra

Higham Chapter 1, Section 1.8 uses the quadratic formula to illustrate
cancellation and the standard stable recovery of the second root from
`x₁ * x₂ = c / a`.  This file records the exact algebraic foundation; the
floating-point stability analysis of the competing formulas is a separate
algorithm-level obligation.
-/

/-- Quadratic polynomial evaluation `a*x^2 + b*x + c`. -/
noncomputable def quadraticEval (a b c x : ℝ) : ℝ :=
  a * x ^ 2 + b * x + c

/-- Quadratic discriminant `b^2 - 4*a*c`. -/
noncomputable def quadraticDiscriminant (a b c : ℝ) : ℝ :=
  b ^ 2 - 4 * a * c

/-- Rounded discriminant path `fl(fl(b*b) - fl(fl(4*a)*c))`.

This records the arithmetic path used before the square root in the standard
quadratic formula. -/
noncomputable def flQuadraticDiscriminant (fp : FPModel) (a b c : ℝ) : ℝ :=
  fp.fl_sub (fp.fl_mul b b) (fp.fl_mul (fp.fl_mul 4 a) c)

/-- Explicit absolute-error radius for the rounded discriminant path
`fl(fl(b*b) - fl(fl(4*a)*c))`. -/
noncomputable def flQuadraticDiscriminantAbsErrorBound
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  |b * b| * fp.u +
    |(4 * a) * c| * (2 * fp.u + fp.u ^ 2) +
      fp.u * (|b * b| * (1 + fp.u) +
        |(4 * a) * c| * (1 + fp.u) ^ 2)

/-- The `+` quadratic-formula root using a supplied square root of the
discriminant. -/
noncomputable def quadraticRootPlus (a b _c s : ℝ) : ℝ :=
  (-b + s) / (2 * a)

/-- The `-` quadratic-formula root using a supplied square root of the
discriminant. -/
noncomputable def quadraticRootMinus (a b _c s : ℝ) : ℝ :=
  (-b - s) / (2 * a)

/-- Numerator of the `+` quadratic-formula branch. -/
noncomputable def quadraticRootPlusNumerator (b s : ℝ) : ℝ :=
  -b + s

/-- Numerator of the `-` quadratic-formula branch. -/
noncomputable def quadraticRootMinusNumerator (b s : ℝ) : ℝ :=
  -b - s

/-- The source-recommended exact branch: choose the larger-magnitude root by the
sign of `b`, using the `-` branch for `b >= 0` and the `+` branch for `b < 0`. -/
noncomputable def quadraticRootLargeByBSign (a b c s : ℝ) : ℝ :=
  if 0 ≤ b then quadraticRootMinus a b c s else quadraticRootPlus a b c s

/-- The companion branch to `quadraticRootLargeByBSign`. -/
noncomputable def quadraticRootSmallByBSign (a b c s : ℝ) : ℝ :=
  if 0 ≤ b then quadraticRootPlus a b c s else quadraticRootMinus a b c s

/-- The midpoint of the two quadratic-formula roots, `-b/(2a)`.  In the
small-discriminant regime the two real roots cluster around this value. -/
noncomputable def quadraticRootMidpoint (a b : ℝ) : ℝ :=
  -b / (2 * a)

/-- Rounded recovery of one quadratic root from the other by the product
relation `x₁*x₂ = c/a`: compute `fl(c / fl(a*xhat))`. -/
noncomputable def flQuadraticRecoveredRootFromOther
    (fp : FPModel) (a c xhat : ℝ) : ℝ :=
  fp.fl_div c (fp.fl_mul a xhat)

/-- Rounded `+` branch of the quadratic formula when the square-root value has
already been supplied: compute `fl(fl(-b + s) / fl(2*a))`. -/
noncomputable def flQuadraticRootPlusFromSqrt
    (fp : FPModel) (a b s : ℝ) : ℝ :=
  fp.fl_div (fp.fl_add (-b) s) (fp.fl_mul 2 a)

/-- Rounded `-` branch of the quadratic formula when the square-root value has
already been supplied: compute `fl(fl(-b - s) / fl(2*a))`. -/
noncomputable def flQuadraticRootMinusFromSqrt
    (fp : FPModel) (a b s : ℝ) : ℝ :=
  fp.fl_div (fp.fl_sub (-b) s) (fp.fl_mul 2 a)

/-- Rounded `+` branch of the quadratic formula with the square-root operation
instantiated by the ambient floating-point model.  The discriminant itself is
still the exact real expression `b^2 - 4*a*c`; this definition charges only the
modelled square-root operation and the subsequent branch arithmetic. -/
noncomputable def flQuadraticRootPlusComputedSqrt
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticRootPlusFromSqrt fp a b (fp.fl_sqrt (quadraticDiscriminant a b c))

/-- Rounded `-` branch of the quadratic formula with the square-root operation
instantiated by the ambient floating-point model. -/
noncomputable def flQuadraticRootMinusComputedSqrt
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticRootMinusFromSqrt fp a b (fp.fl_sqrt (quadraticDiscriminant a b c))

/-- Rounded `+` branch of the quadratic formula with the discriminant formed
by the rounded operation trace before applying the modelled square root. -/
noncomputable def flQuadraticRootPlusRoundedDiscriminantSqrt
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticRootPlusFromSqrt fp a b
    (fp.fl_sqrt (flQuadraticDiscriminant fp a b c))

/-- Rounded `-` branch of the quadratic formula with rounded discriminant and
then modelled square root. -/
noncomputable def flQuadraticRootMinusRoundedDiscriminantSqrt
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticRootMinusFromSqrt fp a b
    (fp.fl_sqrt (flQuadraticDiscriminant fp a b c))

/-- Combined square-root input radius for the path that forms the discriminant
with `flQuadraticDiscriminant` and then applies `fp.fl_sqrt`. -/
noncomputable def flQuadraticRoundedDiscriminantSqrtInputErrorBound
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  |Real.sqrt (flQuadraticDiscriminant fp a b c)| * fp.u +
    Real.sqrt (flQuadraticDiscriminantAbsErrorBound fp a b c)

/-- Combined square-root input radius for a mixed-precision path: form the
discriminant with `discFp`, then take the square root with `rootFp`. -/
noncomputable def flQuadraticMixedDiscriminantSqrtInputErrorBound
    (discFp rootFp : FPModel) (a b c : ℝ) : ℝ :=
  |Real.sqrt (flQuadraticDiscriminant discFp a b c)| * rootFp.u +
    Real.sqrt (flQuadraticDiscriminantAbsErrorBound discFp a b c)

/-- Mixed-precision `+` branch: evaluate `b^2 - 4*a*c` using `discFp`, then
take the square root and rounded quadratic-formula branch using `rootFp`. -/
noncomputable def flQuadraticRootPlusMixedDiscriminantSqrt
    (discFp rootFp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticRootPlusFromSqrt rootFp a b
    (rootFp.fl_sqrt (flQuadraticDiscriminant discFp a b c))

/-- Mixed-precision `-` branch: evaluate `b^2 - 4*a*c` using `discFp`, then
take the square root and rounded quadratic-formula branch using `rootFp`. -/
noncomputable def flQuadraticRootMinusMixedDiscriminantSqrt
    (discFp rootFp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticRootMinusFromSqrt rootFp a b
    (rootFp.fl_sqrt (flQuadraticDiscriminant discFp a b c))

/-- Absolute-error radius for the rounded-discriminant/square-root `+` branch. -/
noncomputable def flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticRoundedDiscriminantSqrtInputErrorBound fp a b c / (2 * |a|) +
    (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
        flQuadraticRoundedDiscriminantSqrtInputErrorBound fp a b c / (2 * |a|)) *
      gamma fp 3

/-- Absolute-error radius for the rounded-discriminant/square-root `-` branch. -/
noncomputable def flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticRoundedDiscriminantSqrtInputErrorBound fp a b c / (2 * |a|) +
    (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
        flQuadraticRoundedDiscriminantSqrtInputErrorBound fp a b c / (2 * |a|)) *
      gamma fp 3

/-- Absolute-error radius for the mixed-precision discriminant/square-root `+`
branch.  The discriminant error uses `discFp.u`; the square-root and branch
rounding use `rootFp.u`. -/
noncomputable def flQuadraticMixedDiscriminantSqrtRootPlusAbsErrorBound
    (discFp rootFp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticMixedDiscriminantSqrtInputErrorBound discFp rootFp a b c /
      (2 * |a|) +
    (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
        flQuadraticMixedDiscriminantSqrtInputErrorBound discFp rootFp a b c /
          (2 * |a|)) *
      gamma rootFp 3

/-- Absolute-error radius for the mixed-precision discriminant/square-root `-`
branch. -/
noncomputable def flQuadraticMixedDiscriminantSqrtRootMinusAbsErrorBound
    (discFp rootFp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticMixedDiscriminantSqrtInputErrorBound discFp rootFp a b c /
      (2 * |a|) +
    (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
        flQuadraticMixedDiscriminantSqrtInputErrorBound discFp rootFp a b c /
          (2 * |a|)) *
      gamma rootFp 3

/-- Source-recommended rounded larger-magnitude root: use the `-` branch when
`b >= 0` and the `+` branch when `b < 0`, after forming the rounded
discriminant and modelled square root. -/
noncomputable def flQuadraticRootLargeByBSignRoundedDiscriminantSqrt
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  if 0 ≤ b then
    flQuadraticRootMinusRoundedDiscriminantSqrt fp a b c
  else
    flQuadraticRootPlusRoundedDiscriminantSqrt fp a b c

/-- Source-recommended rounded companion root: compute the larger-magnitude
branch by sign of `b`, then recover the other root from `x₁*x₂ = c/a`. -/
noncomputable def flQuadraticRootSmallByBSignRoundedDiscriminantSqrt
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  flQuadraticRecoveredRootFromOther fp a c
    (flQuadraticRootLargeByBSignRoundedDiscriminantSqrt fp a b c)

/-- The rounded sign-of-`b` quadratic-root pair. -/
noncomputable def flQuadraticRootsByBSignRoundedDiscriminantSqrt
    (fp : FPModel) (a b c : ℝ) : ℝ × ℝ :=
  (flQuadraticRootLargeByBSignRoundedDiscriminantSqrt fp a b c,
    flQuadraticRootSmallByBSignRoundedDiscriminantSqrt fp a b c)

/-- Branch-selected absolute-error radius for the rounded larger-magnitude
root. -/
noncomputable def flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  if 0 ≤ b then
    flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c
  else
    flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c

/-- Absolute-error radius for the rounded recovered companion root after the
sign-of-`b` larger-root choice. -/
noncomputable def flQuadraticRoundedDiscriminantSqrtRootSmallRecoveryAbsErrorBound
    (fp : FPModel) (a b c : ℝ) : ℝ :=
  if 0 ≤ b then
    |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| *
        flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c /
        (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| -
          flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c) +
      (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
          |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| *
            flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c /
            (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| -
              flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c)) *
        gamma fp 2
  else
    |quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| *
        flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c /
        (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| -
          flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c) +
      (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
          |quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| *
            flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c /
            (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| -
              flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c)) *
        gamma fp 2

/-- Exact local-factor expansion of the rounded discriminant path
`fl(fl(b*b) - fl(fl(4*a)*c))`.  This charges the two products forming `4*a*c`,
the product `b*b`, and the final subtraction, while leaving later square-root
and branch-selection propagation to separate theorems. -/
theorem flQuadraticDiscriminant_expansion
    (fp : FPModel) (a b c : ℝ) :
    ∃ δbb δ4a δ4ac δsub : ℝ,
      |δbb| ≤ fp.u ∧ |δ4a| ≤ fp.u ∧ |δ4ac| ≤ fp.u ∧ |δsub| ≤ fp.u ∧
      flQuadraticDiscriminant fp a b c =
        ((b * b) * (1 + δbb) -
            (((4 * a) * (1 + δ4a)) * c) * (1 + δ4ac)) *
          (1 + δsub) := by
  obtain ⟨δbb, hδbb, hbb⟩ := fp.model_mul b b
  obtain ⟨δ4a, hδ4a, h4a⟩ := fp.model_mul 4 a
  obtain ⟨δ4ac, hδ4ac, h4ac⟩ := fp.model_mul (fp.fl_mul 4 a) c
  obtain ⟨δsub, hδsub, hsub⟩ :=
    fp.model_sub (fp.fl_mul b b) (fp.fl_mul (fp.fl_mul 4 a) c)
  refine ⟨δbb, δ4a, δ4ac, δsub, hδbb, hδ4a, hδ4ac, hδsub, ?_⟩
  rw [flQuadraticDiscriminant, hsub, hbb, h4ac, h4a]

/-- Absolute-error bound for the rounded discriminant path
`fl(fl(b*b) - fl(fl(4*a)*c))`.

The first term charges `b*b`, the second charges the two products in `4*a*c`,
and the last term charges the final subtraction against the rounded operands.
-/
theorem flQuadraticDiscriminant_abs_error_le
    (fp : FPModel) (a b c : ℝ) :
    |flQuadraticDiscriminant fp a b c - quadraticDiscriminant a b c| ≤
      |b * b| * fp.u +
        |(4 * a) * c| * (2 * fp.u + fp.u ^ 2) +
          fp.u * (|b * b| * (1 + fp.u) +
            |(4 * a) * c| * (1 + fp.u) ^ 2) := by
  obtain ⟨δbb, δ4a, δ4ac, δsub, hδbb, hδ4a, hδ4ac, hδsub, hdisc⟩ :=
    flQuadraticDiscriminant_expansion fp a b c
  let B : ℝ := b * b
  let C : ℝ := (4 * a) * c
  let p : ℝ := B * (1 + δbb)
  let q : ℝ := (((4 * a) * (1 + δ4a)) * c) * (1 + δ4ac)
  have hq_factor : q = C * (1 + δ4a) * (1 + δ4ac) := by
    dsimp [q, C]
    ring
  have hdisc' :
      flQuadraticDiscriminant fp a b c =
        (p - q) * (1 + δsub) := by
    simpa [p, q, B] using hdisc
  have hquad :
      quadraticDiscriminant a b c = B - C := by
    dsimp [quadraticDiscriminant, B, C]
    ring
  have hpb : |p - B| ≤ |B| * fp.u := by
    have hdiff : p - B = B * δbb := by
      dsimp [p]
      ring
    rw [hdiff, abs_mul]
    exact mul_le_mul_of_nonneg_left hδbb (abs_nonneg B)
  have hfactor_abs :
      |(1 + δ4a) * (1 + δ4ac) - 1| ≤ 2 * fp.u + fp.u ^ 2 := by
    have hfactor :
        (1 + δ4a) * (1 + δ4ac) - 1 =
          δ4a + δ4ac + δ4a * δ4ac := by
      ring
    have htri :
        |δ4a + δ4ac + δ4a * δ4ac| ≤
          |δ4a| + |δ4ac| + |δ4a * δ4ac| := by
      calc
        |δ4a + δ4ac + δ4a * δ4ac| =
            |(δ4a + δ4ac) + δ4a * δ4ac| := by ring
        _ ≤ |δ4a + δ4ac| + |δ4a * δ4ac| :=
            abs_add_le (δ4a + δ4ac) (δ4a * δ4ac)
        _ ≤ |δ4a| + |δ4ac| + |δ4a * δ4ac| := by
            nlinarith [abs_add_le δ4a δ4ac]
    calc
      |(1 + δ4a) * (1 + δ4ac) - 1| =
          |δ4a + δ4ac + δ4a * δ4ac| := by rw [hfactor]
      _ ≤ |δ4a| + |δ4ac| + |δ4a * δ4ac| := htri
      _ = |δ4a| + |δ4ac| + |δ4a| * |δ4ac| := by rw [abs_mul]
      _ ≤ 2 * fp.u + fp.u ^ 2 := by
          nlinarith [hδ4a, hδ4ac, abs_nonneg δ4a, abs_nonneg δ4ac,
            fp.u_nonneg]
  have hqc : |q - C| ≤ |C| * (2 * fp.u + fp.u ^ 2) := by
    have hdiff : q - C = C * ((1 + δ4a) * (1 + δ4ac) - 1) := by
      rw [hq_factor]
      ring
    rw [hdiff, abs_mul]
    exact mul_le_mul_of_nonneg_left hfactor_abs (abs_nonneg C)
  have hδbb_factor : |1 + δbb| ≤ 1 + fp.u := by
    calc
      |1 + δbb| ≤ |(1 : ℝ)| + |δbb| := abs_add_le 1 δbb
      _ ≤ 1 + fp.u := by
          norm_num
          exact hδbb
  have hδ4a_factor : |1 + δ4a| ≤ 1 + fp.u := by
    calc
      |1 + δ4a| ≤ |(1 : ℝ)| + |δ4a| := abs_add_le 1 δ4a
      _ ≤ 1 + fp.u := by
          norm_num
          exact hδ4a
  have hδ4ac_factor : |1 + δ4ac| ≤ 1 + fp.u := by
    calc
      |1 + δ4ac| ≤ |(1 : ℝ)| + |δ4ac| := abs_add_le 1 δ4ac
      _ ≤ 1 + fp.u := by
          norm_num
          exact hδ4ac
  have hp_abs : |p| ≤ |B| * (1 + fp.u) := by
    dsimp [p]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hδbb_factor (abs_nonneg B)
  have hq_abs : |q| ≤ |C| * (1 + fp.u) ^ 2 := by
    have hu1 : 0 ≤ 1 + fp.u := by nlinarith [fp.u_nonneg]
    have hq_abs_eq :
        |q| = |C| * |1 + δ4a| * |1 + δ4ac| := by
      rw [hq_factor, abs_mul, abs_mul]
    have hfirst :
        |C| * |1 + δ4a| ≤ |C| * (1 + fp.u) :=
      mul_le_mul_of_nonneg_left hδ4a_factor (abs_nonneg C)
    have hsecond :
        |C| * |1 + δ4a| * |1 + δ4ac| ≤
          |C| * (1 + fp.u) * |1 + δ4ac| :=
      mul_le_mul_of_nonneg_right hfirst (abs_nonneg (1 + δ4ac))
    have hthird :
        |C| * (1 + fp.u) * |1 + δ4ac| ≤
          |C| * (1 + fp.u) * (1 + fp.u) :=
      mul_le_mul_of_nonneg_left hδ4ac_factor
        (mul_nonneg (abs_nonneg C) hu1)
    calc
      |q| = |C| * |1 + δ4a| * |1 + δ4ac| := hq_abs_eq
      _ ≤ |C| * (1 + fp.u) * |1 + δ4ac| := hsecond
      _ ≤ |C| * (1 + fp.u) * (1 + fp.u) := hthird
      _ = |C| * (1 + fp.u) ^ 2 := by ring
  have hpq_abs :
      |p - q| ≤ |B| * (1 + fp.u) + |C| * (1 + fp.u) ^ 2 := by
    calc
      |p - q| ≤ |p| + |q| := abs_sub p q
      _ ≤ |B| * (1 + fp.u) + |C| * (1 + fp.u) ^ 2 :=
          add_le_add hp_abs hq_abs
  have hsubterm :
      |δsub * (p - q)| ≤
        fp.u * (|B| * (1 + fp.u) + |C| * (1 + fp.u) ^ 2) := by
    rw [abs_mul]
    have hrhs_nonneg :
        0 ≤ |B| * (1 + fp.u) + |C| * (1 + fp.u) ^ 2 := by
      have hu1 : 0 ≤ 1 + fp.u := by nlinarith [fp.u_nonneg]
      exact add_nonneg
        (mul_nonneg (abs_nonneg B) hu1)
        (mul_nonneg (abs_nonneg C) (sq_nonneg (1 + fp.u)))
    exact mul_le_mul hδsub hpq_abs (abs_nonneg (p - q)) fp.u_nonneg
  have hsplit :
      (p - q) * (1 + δsub) - (B - C) =
        (p - B) - (q - C) + δsub * (p - q) := by
    ring
  calc
    |flQuadraticDiscriminant fp a b c - quadraticDiscriminant a b c| =
        |(p - q) * (1 + δsub) - (B - C)| := by
          rw [hdisc', hquad]
    _ = |(p - B) - (q - C) + δsub * (p - q)| := by rw [hsplit]
    _ ≤ |(p - B) - (q - C)| + |δsub * (p - q)| :=
        abs_add_le ((p - B) - (q - C)) (δsub * (p - q))
    _ ≤ (|p - B| + |q - C|) + |δsub * (p - q)| := by
        nlinarith [abs_sub (p - B) (q - C)]
    _ ≤ |B| * fp.u + |C| * (2 * fp.u + fp.u ^ 2) +
        fp.u * (|B| * (1 + fp.u) + |C| * (1 + fp.u) ^ 2) := by
        nlinarith [hpb, hqc, hsubterm]
    _ = |b * b| * fp.u +
        |(4 * a) * c| * (2 * fp.u + fp.u ^ 2) +
          fp.u * (|b * b| * (1 + fp.u) +
            |(4 * a) * c| * (1 + fp.u) ^ 2) := by
          rfl

/-- The explicit rounded-discriminant error radius is nonnegative. -/
theorem flQuadraticDiscriminantAbsErrorBound_nonneg
    (fp : FPModel) (a b c : ℝ) :
    0 ≤ flQuadraticDiscriminantAbsErrorBound fp a b c := by
  have hquad : 0 ≤ 2 * fp.u + fp.u ^ 2 := by
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hu1 : 0 ≤ 1 + fp.u := by nlinarith [fp.u_nonneg]
  have hfirst : 0 ≤ |b * b| * fp.u :=
    mul_nonneg (abs_nonneg _) fp.u_nonneg
  have hsecond : 0 ≤ |(4 * a) * c| * (2 * fp.u + fp.u ^ 2) :=
    mul_nonneg (abs_nonneg _) hquad
  have hinner :
      0 ≤ |b * b| * (1 + fp.u) + |(4 * a) * c| * (1 + fp.u) ^ 2 :=
    add_nonneg
      (mul_nonneg (abs_nonneg _) hu1)
      (mul_nonneg (abs_nonneg _) (sq_nonneg (1 + fp.u)))
  have hthird :
      0 ≤ fp.u *
        (|b * b| * (1 + fp.u) + |(4 * a) * c| * (1 + fp.u) ^ 2) :=
    mul_nonneg fp.u_nonneg hinner
  unfold flQuadraticDiscriminantAbsErrorBound
  exact add_nonneg (add_nonneg hfirst hsecond) hthird

/-- Polynomial form of the rounded-discriminant error radius, exposing its
monotonic dependence on the unit roundoff. -/
theorem flQuadraticDiscriminantAbsErrorBound_eq_poly
    (fp : FPModel) (a b c : ℝ) :
    flQuadraticDiscriminantAbsErrorBound fp a b c =
      (2 * |b * b| + 3 * |(4 * a) * c|) * fp.u +
        (|b * b| + 3 * |(4 * a) * c|) * fp.u ^ 2 +
          |(4 * a) * c| * fp.u ^ 3 := by
  unfold flQuadraticDiscriminantAbsErrorBound
  ring

/-- If the discriminant arithmetic has no larger unit roundoff, then the named
absolute-error radius for forming `b^2 - 4*a*c` is no larger. -/
theorem flQuadraticDiscriminantAbsErrorBound_le_of_u_le
    (fpSmall fpLarge : FPModel) (a b c : ℝ)
    (hu : fpSmall.u ≤ fpLarge.u) :
    flQuadraticDiscriminantAbsErrorBound fpSmall a b c ≤
      flQuadraticDiscriminantAbsErrorBound fpLarge a b c := by
  let B : ℝ := |b * b|
  let C : ℝ := |(4 * a) * c|
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact abs_nonneg _
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact abs_nonneg _
  have h2 : fpSmall.u ^ 2 ≤ fpLarge.u ^ 2 :=
    pow_le_pow_left₀ fpSmall.u_nonneg hu 2
  have h3 : fpSmall.u ^ 3 ≤ fpLarge.u ^ 3 :=
    pow_le_pow_left₀ fpSmall.u_nonneg hu 3
  calc
    flQuadraticDiscriminantAbsErrorBound fpSmall a b c =
        (2 * B + 3 * C) * fpSmall.u +
          (B + 3 * C) * fpSmall.u ^ 2 + C * fpSmall.u ^ 3 := by
            simpa [B, C] using
              flQuadraticDiscriminantAbsErrorBound_eq_poly fpSmall a b c
    _ ≤ (2 * B + 3 * C) * fpLarge.u +
          (B + 3 * C) * fpLarge.u ^ 2 + C * fpLarge.u ^ 3 := by
            nlinarith [hB_nonneg, hC_nonneg, fpSmall.u_nonneg,
              fpLarge.u_nonneg, hu, h2, h3]
    _ = flQuadraticDiscriminantAbsErrorBound fpLarge a b c := by
            simpa [B, C] using
              (flQuadraticDiscriminantAbsErrorBound_eq_poly fpLarge a b c).symm

/-- Higham §1.8's "use higher precision for `b^2 - 4*a*c`" principle at the
error-radius level: if `discFp` simulates a higher precision than `workingFp`,
its rounded-discriminant absolute-error radius is no larger than the working
precision radius for the same arithmetic path. -/
theorem flQuadraticDiscriminantAbsErrorBound_le_of_simulatesHigherPrecision
    (workingFp discFp : FPModel) (a b c : ℝ)
    (hsim : SimulatesHigherPrecision
      (PrecisionMeasure.ofFPModel workingFp)
      (PrecisionMeasure.ofFPModel discFp)) :
    flQuadraticDiscriminantAbsErrorBound discFp a b c ≤
      flQuadraticDiscriminantAbsErrorBound workingFp a b c := by
  exact flQuadraticDiscriminantAbsErrorBound_le_of_u_le
    discFp workingFp a b c (le_of_lt hsim)

/-- Named-radius form of `flQuadraticDiscriminant_abs_error_le`. -/
theorem flQuadraticDiscriminant_abs_error_le_bound
    (fp : FPModel) (a b c : ℝ) :
    |flQuadraticDiscriminant fp a b c - quadraticDiscriminant a b c| ≤
      flQuadraticDiscriminantAbsErrorBound fp a b c := by
  simpa [flQuadraticDiscriminantAbsErrorBound] using
    flQuadraticDiscriminant_abs_error_le fp a b c

/-- If the exact discriminant dominates the rounded-discriminant absolute-error
radius, then the rounded discriminant is nonnegative and may be passed to
`FPModel.model_sqrt`. -/
theorem flQuadraticDiscriminant_nonneg_of_abs_error_bound_le
    (fp : FPModel) (a b c : ℝ)
    (hsep : flQuadraticDiscriminantAbsErrorBound fp a b c ≤
      quadraticDiscriminant a b c) :
    0 ≤ flQuadraticDiscriminant fp a b c := by
  have herr := flQuadraticDiscriminant_abs_error_le_bound fp a b c
  have hlower :
      -flQuadraticDiscriminantAbsErrorBound fp a b c ≤
        flQuadraticDiscriminant fp a b c - quadraticDiscriminant a b c :=
    (abs_le.mp herr).1
  nlinarith

/-- The `+` quadratic-formula value is a root whenever `s^2` is the
discriminant. -/
theorem quadraticRootPlus_is_root (a b c s : ℝ)
    (ha : a ≠ 0) (hs : s ^ 2 = quadraticDiscriminant a b c) :
    quadraticEval a b c (quadraticRootPlus a b c s) = 0 := by
  unfold quadraticEval quadraticRootPlus quadraticDiscriminant at *
  field_simp [ha]
  nlinarith

/-- The `-` quadratic-formula value is a root whenever `s^2` is the
discriminant. -/
theorem quadraticRootMinus_is_root (a b c s : ℝ)
    (ha : a ≠ 0) (hs : s ^ 2 = quadraticDiscriminant a b c) :
    quadraticEval a b c (quadraticRootMinus a b c s) = 0 := by
  unfold quadraticEval quadraticRootMinus quadraticDiscriminant at *
  field_simp [ha]
  nlinarith

/-- The two quadratic-formula roots have sum `-b/a`. -/
theorem quadratic_roots_sum (a b c s : ℝ) (ha : a ≠ 0) :
    quadraticRootPlus a b c s + quadraticRootMinus a b c s = -b / a := by
  unfold quadraticRootPlus quadraticRootMinus
  field_simp [ha]
  ring

/-- Distance from the `+` quadratic-formula branch to the midpoint
`-b/(2a)`. -/
theorem quadraticRootPlus_sub_midpoint_abs_eq (a b c s : ℝ) (ha : a ≠ 0) :
    |quadraticRootPlus a b c s - quadraticRootMidpoint a b| =
      |s| / (2 * |a|) := by
  have hden_abs : |2 * a| = 2 * |a| := by
    rw [abs_mul]
    norm_num
  have hdiff :
      quadraticRootPlus a b c s - quadraticRootMidpoint a b = s / (2 * a) := by
    unfold quadraticRootPlus quadraticRootMidpoint
    field_simp [ha]
    ring
  rw [hdiff, abs_div, hden_abs]

/-- Distance from the `-` quadratic-formula branch to the midpoint
`-b/(2a)`. -/
theorem quadraticRootMinus_sub_midpoint_abs_eq (a b c s : ℝ) (ha : a ≠ 0) :
    |quadraticRootMinus a b c s - quadraticRootMidpoint a b| =
      |s| / (2 * |a|) := by
  have hden_abs : |2 * a| = 2 * |a| := by
    rw [abs_mul]
    norm_num
  have hdiff :
      quadraticRootMinus a b c s - quadraticRootMidpoint a b = -(s / (2 * a)) := by
    unfold quadraticRootMinus quadraticRootMidpoint
    field_simp [ha]
    ring
  rw [hdiff, abs_neg, abs_div, hden_abs]

/-- The exact separation between the two quadratic-formula branches is
`|s|/|a|`. -/
theorem quadraticRootSeparation_abs_eq (a b c s : ℝ) (ha : a ≠ 0) :
    |quadraticRootPlus a b c s - quadraticRootMinus a b c s| =
      |s| / |a| := by
  have hdiff :
      quadraticRootPlus a b c s - quadraticRootMinus a b c s = s / a := by
    unfold quadraticRootPlus quadraticRootMinus
    field_simp [ha]
    ring
  rw [hdiff, abs_div]

/-- If the discriminant is bounded by `eta`, then the two real roots cluster
around `-b/(2a)` with radius `sqrt(eta)/(2|a|)`, and their mutual separation is
at most `sqrt(eta)/|a|`.  This is the exact small-discriminant substrate behind
Higham §1.8's warning that nearly equal roots cannot be separated accurately
after cancellation in `b^2 - 4*a*c`. -/
theorem quadraticRoots_near_midpoint_of_discriminant_le
    (a b c eta : ℝ) (ha : a ≠ 0)
    (_hdisc : 0 ≤ quadraticDiscriminant a b c)
    (_heta : 0 ≤ eta)
    (hDeta : quadraticDiscriminant a b c ≤ eta) :
    |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c)) -
        quadraticRootMidpoint a b| ≤ Real.sqrt eta / (2 * |a|) ∧
      |quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c)) -
          quadraticRootMidpoint a b| ≤ Real.sqrt eta / (2 * |a|) ∧
        |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c)) -
            quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
          Real.sqrt eta / |a| := by
  have hsqrt_le : |Real.sqrt (quadraticDiscriminant a b c)| ≤ Real.sqrt eta := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hDeta
  have hden2_nonneg : 0 ≤ 2 * |a| := by
    nlinarith [abs_nonneg a]
  have hden_nonneg : 0 ≤ |a| := abs_nonneg a
  constructor
  · rw [quadraticRootPlus_sub_midpoint_abs_eq a b c
      (Real.sqrt (quadraticDiscriminant a b c)) ha]
    exact div_le_div_of_nonneg_right hsqrt_le hden2_nonneg
  constructor
  · rw [quadraticRootMinus_sub_midpoint_abs_eq a b c
      (Real.sqrt (quadraticDiscriminant a b c)) ha]
    exact div_le_div_of_nonneg_right hsqrt_le hden2_nonneg
  · rw [quadraticRootSeparation_abs_eq a b c
      (Real.sqrt (quadraticDiscriminant a b c)) ha]
    exact div_le_div_of_nonneg_right hsqrt_le hden_nonneg

/-- If the rounded-discriminant separation guard fails, then the exact
discriminant lies below the existing rounded-discriminant error radius.  For
real roots, this gives a cluster certificate around `-b/(2a)` rather than a
separated-root accuracy theorem. -/
theorem quadraticRoots_near_midpoint_of_discriminant_guard_failure
    (fp : FPModel) (a b c : ℝ) (ha : a ≠ 0)
    (hdisc : 0 ≤ quadraticDiscriminant a b c)
    (hguardFail :
      ¬ flQuadraticDiscriminantAbsErrorBound fp a b c ≤
          quadraticDiscriminant a b c) :
    |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c)) -
        quadraticRootMidpoint a b| ≤
        Real.sqrt (flQuadraticDiscriminantAbsErrorBound fp a b c) / (2 * |a|) ∧
      |quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c)) -
          quadraticRootMidpoint a b| ≤
          Real.sqrt (flQuadraticDiscriminantAbsErrorBound fp a b c) / (2 * |a|) ∧
        |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c)) -
            quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
          Real.sqrt (flQuadraticDiscriminantAbsErrorBound fp a b c) / |a| := by
  have hE_nonneg :
      0 ≤ flQuadraticDiscriminantAbsErrorBound fp a b c :=
    flQuadraticDiscriminantAbsErrorBound_nonneg fp a b c
  have hDleE :
      quadraticDiscriminant a b c ≤ flQuadraticDiscriminantAbsErrorBound fp a b c :=
    le_of_lt (not_le.mp hguardFail)
  exact
    quadraticRoots_near_midpoint_of_discriminant_le
      a b c (flQuadraticDiscriminantAbsErrorBound fp a b c)
      ha hdisc hE_nonneg hDleE

/-- The two quadratic-formula roots have product `c/a` whenever `s^2` is the
discriminant. -/
theorem quadratic_roots_product (a b c s : ℝ)
    (ha : a ≠ 0) (hs : s ^ 2 = quadraticDiscriminant a b c) :
    quadraticRootPlus a b c s * quadraticRootMinus a b c s = c / a := by
  unfold quadraticRootPlus quadraticRootMinus quadraticDiscriminant at *
  field_simp [ha]
  nlinarith

/-- If the `+` root is nonzero, the `-` root can be recovered from the product
relation `x₊ * x₋ = c/a` as `c/(a*x₊)`.  This is the exact algebra behind
Higham §1.8's stable second-root recovery. -/
theorem quadraticRootMinus_eq_c_div_a_mul_rootPlus (a b c s : ℝ)
    (ha : a ≠ 0) (hs : s ^ 2 = quadraticDiscriminant a b c)
    (hplus : quadraticRootPlus a b c s ≠ 0) :
    quadraticRootMinus a b c s = c / (a * quadraticRootPlus a b c s) := by
  have hprod := quadratic_roots_product a b c s ha hs
  have hden : a * quadraticRootPlus a b c s ≠ 0 :=
    mul_ne_zero ha hplus
  calc
    quadraticRootMinus a b c s
        = (quadraticRootPlus a b c s * quadraticRootMinus a b c s) /
            quadraticRootPlus a b c s := by
              field_simp [hplus]
    _ = (c / a) / quadraticRootPlus a b c s := by
          rw [hprod]
    _ = c / (a * quadraticRootPlus a b c s) := by
          field_simp [ha, hplus, hden]

/-- If the `-` root is nonzero, the `+` root can be recovered from the product
relation `x₊ * x₋ = c/a` as `c/(a*x₋)`. -/
theorem quadraticRootPlus_eq_c_div_a_mul_rootMinus (a b c s : ℝ)
    (ha : a ≠ 0) (hs : s ^ 2 = quadraticDiscriminant a b c)
    (hminus : quadraticRootMinus a b c s ≠ 0) :
    quadraticRootPlus a b c s = c / (a * quadraticRootMinus a b c s) := by
  have hprod := quadratic_roots_product a b c s ha hs
  have hden : a * quadraticRootMinus a b c s ≠ 0 :=
    mul_ne_zero ha hminus
  calc
    quadraticRootPlus a b c s
        = (quadraticRootPlus a b c s * quadraticRootMinus a b c s) /
            quadraticRootMinus a b c s := by
              field_simp [hminus]
    _ = (c / a) / quadraticRootMinus a b c s := by
          rw [hprod]
    _ = c / (a * quadraticRootMinus a b c s) := by
          field_simp [ha, hminus, hden]

/-! ## Exact branch-choice and cancellation comparisons -/

/-- For `b >= 0`, the source-safe `-` numerator has magnitude `|b| + s`. -/
theorem quadraticRootMinusNumerator_abs_eq_abs_b_add_s_of_b_nonneg
    (b s : ℝ) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    |quadraticRootMinusNumerator b s| = |b| + s := by
  unfold quadraticRootMinusNumerator
  rw [abs_of_nonpos (by linarith), abs_of_nonneg hb]
  ring

/-- For `b <= 0`, the source-safe `+` numerator has magnitude `|b| + s`. -/
theorem quadraticRootPlusNumerator_abs_eq_abs_b_add_s_of_b_nonpos
    (b s : ℝ) (hb : b ≤ 0) (hs : 0 ≤ s) :
    |quadraticRootPlusNumerator b s| = |b| + s := by
  unfold quadraticRootPlusNumerator
  rw [abs_of_nonneg (by linarith), abs_of_nonpos hb]

/-- If `b >= 0` and the supplied square root is close to `b`, the `+`
numerator is correspondingly small: this is the cancellation side of the
source discussion. -/
theorem quadraticRootPlusNumerator_abs_le_of_b_nonneg_s_close
    (b s eta : ℝ) (_hb : 0 ≤ b) (hclose : |s - b| ≤ eta) :
    |quadraticRootPlusNumerator b s| ≤ eta := by
  simpa [quadraticRootPlusNumerator, sub_eq_add_neg, add_comm] using hclose

/-- If `b <= 0` and the supplied square root is close to `|b| = -b`, the `-`
numerator is the cancellation-prone one. -/
theorem quadraticRootMinusNumerator_abs_le_of_b_nonpos_s_close
    (b s eta : ℝ) (_hb : b ≤ 0) (hclose : |s + b| ≤ eta) :
    |quadraticRootMinusNumerator b s| ≤ eta := by
  have hnum : quadraticRootMinusNumerator b s = -(s + b) := by
    unfold quadraticRootMinusNumerator
    ring
  calc
    |quadraticRootMinusNumerator b s| = |s + b| := by rw [hnum, abs_neg]
    _ ≤ eta := hclose

/-- For nonnegative `b`, the `-` branch is at least as large in absolute value
as the `+` branch. -/
theorem quadraticRootPlus_abs_le_rootMinus_of_b_nonneg
    (a b c s : ℝ) (ha : a ≠ 0) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    |quadraticRootPlus a b c s| ≤ |quadraticRootMinus a b c s| := by
  unfold quadraticRootPlus quadraticRootMinus
  rw [abs_div, abs_div]
  have hden_pos : 0 < |2 * a| := by
    exact abs_pos.mpr (mul_ne_zero (by norm_num) ha)
  have hnum : |-b + s| ≤ |-b - s| := by
    have hsafe : |-b - s| = b + s := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have hcancel : |-b + s| ≤ b + s := by
      calc
        |-b + s| = |s + -b| := by ring_nf
        _ ≤ |s| + |-b| := abs_add_le _ _
        _ = s + b := by rw [abs_of_nonneg hs, abs_neg, abs_of_nonneg hb]
        _ = b + s := by ring
    simpa [hsafe] using hcancel
  exact div_le_div_of_nonneg_right hnum hden_pos.le

/-- For nonpositive `b`, the `+` branch is at least as large in absolute value
as the `-` branch. -/
theorem quadraticRootMinus_abs_le_rootPlus_of_b_nonpos
    (a b c s : ℝ) (ha : a ≠ 0) (hb : b ≤ 0) (hs : 0 ≤ s) :
    |quadraticRootMinus a b c s| ≤ |quadraticRootPlus a b c s| := by
  unfold quadraticRootPlus quadraticRootMinus
  rw [abs_div, abs_div]
  have hden_pos : 0 < |2 * a| := by
    exact abs_pos.mpr (mul_ne_zero (by norm_num) ha)
  have hnum : |-b - s| ≤ |-b + s| := by
    have hsafe : |-b + s| = -b + s := by
      rw [abs_of_nonneg (by linarith)]
    have hcancel : |-b - s| ≤ -b + s := by
      calc
        |-b - s| = |-b + -s| := by ring_nf
        _ ≤ |-b| + |-s| := abs_add_le _ _
        _ = -b + s := by rw [abs_neg, abs_of_nonpos hb, abs_neg, abs_of_nonneg hs]
    simpa [hsafe] using hcancel
  exact div_le_div_of_nonneg_right hnum hden_pos.le

/-- The sign-of-`b` branch selector chooses a root whose absolute value is at
least that of the companion branch. -/
theorem quadraticRootSmallByBSign_abs_le_largeByBSign
    (a b c s : ℝ) (ha : a ≠ 0) (hs : 0 ≤ s) :
    |quadraticRootSmallByBSign a b c s| ≤
      |quadraticRootLargeByBSign a b c s| := by
  unfold quadraticRootSmallByBSign quadraticRootLargeByBSign
  by_cases hb : 0 ≤ b
  · simp [hb, quadraticRootPlus_abs_le_rootMinus_of_b_nonneg a b c s ha hb hs]
  · have hb_nonpos : b ≤ 0 := le_of_not_ge hb
    simp [hb, quadraticRootMinus_abs_le_rootPlus_of_b_nonpos a b c s ha hb_nonpos hs]

/-! ## Floating-point recovery micro-kernel -/

/-- If a numerator, denominator, and final division have one local rounding
factor each, the resulting rounded quotient is the exact quotient multiplied by
one Higham `γ₃` factor. -/
theorem flRoundedQuotient_rel_error_le_gamma3
    (fp : FPModel) (num den numHat denHat : ℝ)
    (hden : den ≠ 0)
    (hnum : ∃ δ : ℝ, |δ| ≤ fp.u ∧ numHat = num * (1 + δ))
    (hdenHat : ∃ δ : ℝ, |δ| ≤ fp.u ∧ denHat = den * (1 + δ))
    (h3 : gammaValid fp 3) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 3 ∧
      fp.fl_div numHat denHat = (num / den) * (1 + θ) := by
  rcases hnum with ⟨δn, hδn, hnum_eq⟩
  rcases hdenHat with ⟨δd, hδd, hden_eq⟩
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by decide : 1 ≤ 3) h3
  have hu_lt_one : fp.u < 1 := by
    unfold gammaValid at h1
    simpa using h1
  have hδd_pos : 0 < 1 + δd := by
    linarith [neg_abs_le δd, hδd, hu_lt_one]
  have hdenHat_ne : denHat ≠ 0 := by
    rw [hden_eq]
    exact mul_ne_zero hden hδd_pos.ne'
  obtain ⟨δq, hδq, hdiv⟩ := fp.model_div numHat denHat hdenHat_ne
  let δ : Fin 3 → ℝ := fun i => if i = 0 then δn else if i = 1 then δd else δq
  let neg : Fin 3 → Bool := fun i => i = 1
  have hδ : ∀ i : Fin 3, |δ i| ≤ fp.u := by
    intro i
    fin_cases i <;> simp [δ, hδn, hδd, hδq]
  obtain ⟨θ, hθ, hprod⟩ := prod_signed_error_bound fp 3 δ neg hδ h3
  refine ⟨θ, hθ, ?_⟩
  have hprod' : (1 + δn) * (1 / (1 + δd)) * (1 + δq) = 1 + θ := by
    simpa [δ, neg, Fin.prod_univ_three] using hprod
  rw [hdiv, hnum_eq, hden_eq]
  calc
    (num * (1 + δn) / (den * (1 + δd))) * (1 + δq)
        = (num / den) * ((1 + δn) * (1 / (1 + δd)) * (1 + δq)) := by
          field_simp [hden, hδd_pos.ne']
    _ = (num / den) * (1 + θ) := by rw [hprod']

/-- The rounded `+` quadratic-formula branch with a supplied exact square root
has one relative `γ₃` factor around the exact `+` root.  The theorem does not
charge the computation of `s` itself. -/
theorem flQuadraticRootPlusFromSqrt_rel_error_le_gamma3
    (fp : FPModel) (a b c s : ℝ) (ha : a ≠ 0) (h3 : gammaValid fp 3) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 3 ∧
      flQuadraticRootPlusFromSqrt fp a b s =
        quadraticRootPlus a b c s * (1 + θ) := by
  have hden : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  apply flRoundedQuotient_rel_error_le_gamma3 fp (-b + s) (2 * a)
  · exact hden
  · exact fp.model_add (-b) s
  · exact fp.model_mul 2 a
  · exact h3

/-- The rounded `-` quadratic-formula branch with a supplied exact square root
has one relative `γ₃` factor around the exact `-` root.  The theorem does not
charge the computation of `s` itself. -/
theorem flQuadraticRootMinusFromSqrt_rel_error_le_gamma3
    (fp : FPModel) (a b c s : ℝ) (ha : a ≠ 0) (h3 : gammaValid fp 3) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 3 ∧
      flQuadraticRootMinusFromSqrt fp a b s =
        quadraticRootMinus a b c s * (1 + θ) := by
  have hden : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  apply flRoundedQuotient_rel_error_le_gamma3 fp (-b - s) (2 * a)
  · exact hden
  · exact fp.model_sub (-b) s
  · exact fp.model_mul 2 a
  · exact h3

/-- Exact sensitivity of the `+` quadratic-formula branch to perturbing the
supplied square-root value. -/
theorem quadraticRootPlus_sqrt_perturb_eq (a b c s eps : ℝ) (ha : a ≠ 0) :
    quadraticRootPlus a b c (s * (1 + eps)) - quadraticRootPlus a b c s =
      s * eps / (2 * a) := by
  unfold quadraticRootPlus
  field_simp [ha]
  ring

/-- Exact sensitivity of the `-` quadratic-formula branch to perturbing the
supplied square-root value. -/
theorem quadraticRootMinus_sqrt_perturb_eq (a b c s eps : ℝ) (ha : a ≠ 0) :
    quadraticRootMinus a b c (s * (1 + eps)) - quadraticRootMinus a b c s =
      -(s * eps / (2 * a)) := by
  unfold quadraticRootMinus
  field_simp [ha]
  ring

/-- Absolute perturbation bound for the `+` branch under a relative square-root
error. -/
theorem quadraticRootPlus_sqrt_perturb_abs_le_of_abs_eps_le
    (a b c s eps eta : ℝ) (ha : a ≠ 0) (_heta : 0 ≤ eta)
    (heps : |eps| ≤ eta) :
    |quadraticRootPlus a b c (s * (1 + eps)) - quadraticRootPlus a b c s| ≤
      |s| * eta / (2 * |a|) := by
  have hden_abs : |2 * a| = 2 * |a| := by
    rw [abs_mul]
    norm_num
  have hden_nonneg : 0 ≤ 2 * |a| := by
    nlinarith [abs_nonneg a]
  calc
    |quadraticRootPlus a b c (s * (1 + eps)) - quadraticRootPlus a b c s| =
        |s * eps / (2 * a)| := by
          rw [quadraticRootPlus_sqrt_perturb_eq a b c s eps ha]
    _ = |s| * |eps| / (2 * |a|) := by
          rw [abs_div, abs_mul, hden_abs]
    _ ≤ |s| * eta / (2 * |a|) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left heps (abs_nonneg s)) hden_nonneg

/-- Absolute perturbation bound for the `-` branch under a relative square-root
error. -/
theorem quadraticRootMinus_sqrt_perturb_abs_le_of_abs_eps_le
    (a b c s eps eta : ℝ) (ha : a ≠ 0) (_heta : 0 ≤ eta)
    (heps : |eps| ≤ eta) :
    |quadraticRootMinus a b c (s * (1 + eps)) - quadraticRootMinus a b c s| ≤
      |s| * eta / (2 * |a|) := by
  have hden_abs : |2 * a| = 2 * |a| := by
    rw [abs_mul]
    norm_num
  have hden_nonneg : 0 ≤ 2 * |a| := by
    nlinarith [abs_nonneg a]
  calc
    |quadraticRootMinus a b c (s * (1 + eps)) - quadraticRootMinus a b c s| =
        |-(s * eps / (2 * a))| := by
          rw [quadraticRootMinus_sqrt_perturb_eq a b c s eps ha]
    _ = |s| * |eps| / (2 * |a|) := by
          rw [abs_neg, abs_div, abs_mul, hden_abs]
    _ ≤ |s| * eta / (2 * |a|) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left heps (abs_nonneg s)) hden_nonneg

/-- Exact sensitivity of the `+` quadratic-formula branch to an absolute
perturbation of the supplied square-root value. -/
theorem quadraticRootPlus_sqrt_abs_perturb_eq (a b c s shat : ℝ)
    (ha : a ≠ 0) :
    quadraticRootPlus a b c shat - quadraticRootPlus a b c s =
      (shat - s) / (2 * a) := by
  unfold quadraticRootPlus
  field_simp [ha]
  ring

/-- Exact sensitivity of the `-` quadratic-formula branch to an absolute
perturbation of the supplied square-root value. -/
theorem quadraticRootMinus_sqrt_abs_perturb_eq (a b c s shat : ℝ)
    (ha : a ≠ 0) :
    quadraticRootMinus a b c shat - quadraticRootMinus a b c s =
      (s - shat) / (2 * a) := by
  unfold quadraticRootMinus
  field_simp [ha]
  ring

/-- Absolute perturbation bound for the `+` branch under an absolute
square-root input error. -/
theorem quadraticRootPlus_sqrt_abs_perturb_abs_le_of_abs_sub_le
    (a b c s shat eta : ℝ) (ha : a ≠ 0) (_heta : 0 ≤ eta)
    (hshat : |shat - s| ≤ eta) :
    |quadraticRootPlus a b c shat - quadraticRootPlus a b c s| ≤
      eta / (2 * |a|) := by
  have hden_abs : |2 * a| = 2 * |a| := by
    rw [abs_mul]
    norm_num
  have hden_pos : 0 < 2 * |a| := by
    have ha_abs : 0 < |a| := abs_pos.mpr ha
    nlinarith
  calc
    |quadraticRootPlus a b c shat - quadraticRootPlus a b c s| =
        |(shat - s) / (2 * a)| := by
          rw [quadraticRootPlus_sqrt_abs_perturb_eq a b c s shat ha]
    _ = |shat - s| / (2 * |a|) := by
          rw [abs_div, hden_abs]
    _ ≤ eta / (2 * |a|) :=
          div_le_div_of_nonneg_right hshat hden_pos.le

/-- Absolute perturbation bound for the `-` branch under an absolute
square-root input error. -/
theorem quadraticRootMinus_sqrt_abs_perturb_abs_le_of_abs_sub_le
    (a b c s shat eta : ℝ) (ha : a ≠ 0) (_heta : 0 ≤ eta)
    (hshat : |shat - s| ≤ eta) :
    |quadraticRootMinus a b c shat - quadraticRootMinus a b c s| ≤
      eta / (2 * |a|) := by
  have hden_abs : |2 * a| = 2 * |a| := by
    rw [abs_mul]
    norm_num
  have hden_pos : 0 < 2 * |a| := by
    have ha_abs : 0 < |a| := abs_pos.mpr ha
    nlinarith
  calc
    |quadraticRootMinus a b c shat - quadraticRootMinus a b c s| =
        |(s - shat) / (2 * a)| := by
          rw [quadraticRootMinus_sqrt_abs_perturb_eq a b c s shat ha]
    _ = |s - shat| / (2 * |a|) := by
          rw [abs_div, hden_abs]
    _ = |shat - s| / (2 * |a|) := by
          rw [abs_sub_comm]
    _ ≤ eta / (2 * |a|) :=
          div_le_div_of_nonneg_right hshat hden_pos.le

/-- If the square-root value is supplied with relative error `epsSqrt`, the
rounded `+` branch has an explicit absolute-error bound around the branch that
uses the exact square-root value.  This charges the computed square-root input
through `epsSqrt` and the subsequent add/multiply/divide path through
`gamma fp 3`; it still does not instantiate a concrete IEEE square-root
routine or overflow/underflow guards. -/
theorem flQuadraticRootPlusWithSqrtRelError_abs_error_le
    (fp : FPModel) (a b c s shat epsSqrt : ℝ)
    (ha : a ≠ 0) (h3 : gammaValid fp 3)
    (hshat : shat = s * (1 + epsSqrt))
    (hepsSqrt : |epsSqrt| ≤ fp.u) :
    |flQuadraticRootPlusFromSqrt fp a b shat - quadraticRootPlus a b c s| ≤
      |s| * fp.u / (2 * |a|) +
        (|quadraticRootPlus a b c s| + |s| * fp.u / (2 * |a|)) * gamma fp 3 := by
  let q := quadraticRootPlus a b c s
  let qhat := quadraticRootPlus a b c shat
  let err := |s| * fp.u / (2 * |a|)
  have hden_pos : 0 < 2 * |a| := by
    have ha_abs : 0 < |a| := abs_pos.mpr ha
    nlinarith
  have herr_nonneg : 0 ≤ err := by
    exact div_nonneg (mul_nonneg (abs_nonneg s) fp.u_nonneg) hden_pos.le
  have hqdiff : |qhat - q| ≤ err := by
    dsimp [qhat, q, err]
    rw [hshat]
    exact quadraticRootPlus_sqrt_perturb_abs_le_of_abs_eps_le
      a b c s epsSqrt fp.u ha fp.u_nonneg hepsSqrt
  obtain ⟨θ, hθ, hfl⟩ :=
    flQuadraticRootPlusFromSqrt_rel_error_le_gamma3 fp a b c shat ha h3
  have hqhat_abs : |qhat| ≤ |q| + err := by
    have hsplit : q + (qhat - q) = qhat := by ring
    calc
      |qhat| = |q + (qhat - q)| := by rw [hsplit]
      _ ≤ |q| + |qhat - q| := abs_add_le q (qhat - q)
      _ ≤ |q| + err := add_le_add (le_refl |q|) hqdiff
  have hmulθ : |qhat * θ| ≤ (|q| + err) * gamma fp 3 := by
    rw [abs_mul]
    exact mul_le_mul hqhat_abs hθ (abs_nonneg θ)
      (add_nonneg (abs_nonneg q) herr_nonneg)
  have hsplit :
      qhat * (1 + θ) - q = (qhat - q) + qhat * θ := by ring
  calc
    |flQuadraticRootPlusFromSqrt fp a b shat - quadraticRootPlus a b c s| =
        |qhat * (1 + θ) - q| := by
          rw [hfl]
    _ = |(qhat - q) + qhat * θ| := by rw [hsplit]
    _ ≤ |qhat - q| + |qhat * θ| := abs_add_le (qhat - q) (qhat * θ)
    _ ≤ err + (|q| + err) * gamma fp 3 := add_le_add hqdiff hmulθ
    _ = |s| * fp.u / (2 * |a|) +
        (|quadraticRootPlus a b c s| + |s| * fp.u / (2 * |a|)) * gamma fp 3 := by
          rfl

/-- If the square-root value is supplied with relative error `epsSqrt`, the
rounded `-` branch has an explicit absolute-error bound around the branch that
uses the exact square-root value. -/
theorem flQuadraticRootMinusWithSqrtRelError_abs_error_le
    (fp : FPModel) (a b c s shat epsSqrt : ℝ)
    (ha : a ≠ 0) (h3 : gammaValid fp 3)
    (hshat : shat = s * (1 + epsSqrt))
    (hepsSqrt : |epsSqrt| ≤ fp.u) :
    |flQuadraticRootMinusFromSqrt fp a b shat - quadraticRootMinus a b c s| ≤
      |s| * fp.u / (2 * |a|) +
        (|quadraticRootMinus a b c s| + |s| * fp.u / (2 * |a|)) * gamma fp 3 := by
  let q := quadraticRootMinus a b c s
  let qhat := quadraticRootMinus a b c shat
  let err := |s| * fp.u / (2 * |a|)
  have hden_pos : 0 < 2 * |a| := by
    have ha_abs : 0 < |a| := abs_pos.mpr ha
    nlinarith
  have herr_nonneg : 0 ≤ err := by
    exact div_nonneg (mul_nonneg (abs_nonneg s) fp.u_nonneg) hden_pos.le
  have hqdiff : |qhat - q| ≤ err := by
    dsimp [qhat, q, err]
    rw [hshat]
    exact quadraticRootMinus_sqrt_perturb_abs_le_of_abs_eps_le
      a b c s epsSqrt fp.u ha fp.u_nonneg hepsSqrt
  obtain ⟨θ, hθ, hfl⟩ :=
    flQuadraticRootMinusFromSqrt_rel_error_le_gamma3 fp a b c shat ha h3
  have hqhat_abs : |qhat| ≤ |q| + err := by
    have hsplit : q + (qhat - q) = qhat := by ring
    calc
      |qhat| = |q + (qhat - q)| := by rw [hsplit]
      _ ≤ |q| + |qhat - q| := abs_add_le q (qhat - q)
      _ ≤ |q| + err := add_le_add (le_refl |q|) hqdiff
  have hmulθ : |qhat * θ| ≤ (|q| + err) * gamma fp 3 := by
    rw [abs_mul]
    exact mul_le_mul hqhat_abs hθ (abs_nonneg θ)
      (add_nonneg (abs_nonneg q) herr_nonneg)
  have hsplit :
      qhat * (1 + θ) - q = (qhat - q) + qhat * θ := by ring
  calc
    |flQuadraticRootMinusFromSqrt fp a b shat - quadraticRootMinus a b c s| =
        |qhat * (1 + θ) - q| := by
          rw [hfl]
    _ = |(qhat - q) + qhat * θ| := by rw [hsplit]
    _ ≤ |qhat - q| + |qhat * θ| := abs_add_le (qhat - q) (qhat * θ)
    _ ≤ err + (|q| + err) * gamma fp 3 := add_le_add hqdiff hmulθ
    _ = |s| * fp.u / (2 * |a|) +
        (|quadraticRootMinus a b c s| + |s| * fp.u / (2 * |a|)) * gamma fp 3 := by
          rfl

/-- If the supplied square-root value is within an absolute error `eta` of the
reference value, the rounded `+` branch has an explicit absolute-error bound
around the branch using the reference value.  This is the non-relative input
bridge used when the available discriminant/square-root estimate is
`|shat - s| <= eta`. -/
theorem flQuadraticRootPlusFromSqrt_abs_input_error_le
    (fp : FPModel) (a b c s shat eta : ℝ)
    (ha : a ≠ 0) (h3 : gammaValid fp 3) (heta : 0 ≤ eta)
    (hshat : |shat - s| ≤ eta) :
    |flQuadraticRootPlusFromSqrt fp a b shat - quadraticRootPlus a b c s| ≤
      eta / (2 * |a|) +
        (|quadraticRootPlus a b c s| + eta / (2 * |a|)) * gamma fp 3 := by
  let q := quadraticRootPlus a b c s
  let qhat := quadraticRootPlus a b c shat
  let err := eta / (2 * |a|)
  have hden_pos : 0 < 2 * |a| := by
    have ha_abs : 0 < |a| := abs_pos.mpr ha
    nlinarith
  have herr_nonneg : 0 ≤ err := by
    exact div_nonneg heta hden_pos.le
  have hqdiff : |qhat - q| ≤ err := by
    dsimp [qhat, q, err]
    exact quadraticRootPlus_sqrt_abs_perturb_abs_le_of_abs_sub_le
      a b c s shat eta ha heta hshat
  obtain ⟨θ, hθ, hfl⟩ :=
    flQuadraticRootPlusFromSqrt_rel_error_le_gamma3 fp a b c shat ha h3
  have hqhat_abs : |qhat| ≤ |q| + err := by
    have hsplit : q + (qhat - q) = qhat := by ring
    calc
      |qhat| = |q + (qhat - q)| := by rw [hsplit]
      _ ≤ |q| + |qhat - q| := abs_add_le q (qhat - q)
      _ ≤ |q| + err := add_le_add (le_refl |q|) hqdiff
  have hmulθ : |qhat * θ| ≤ (|q| + err) * gamma fp 3 := by
    rw [abs_mul]
    exact mul_le_mul hqhat_abs hθ (abs_nonneg θ)
      (add_nonneg (abs_nonneg q) herr_nonneg)
  have hsplit :
      qhat * (1 + θ) - q = (qhat - q) + qhat * θ := by ring
  calc
    |flQuadraticRootPlusFromSqrt fp a b shat - quadraticRootPlus a b c s| =
        |qhat * (1 + θ) - q| := by
          rw [hfl]
    _ = |(qhat - q) + qhat * θ| := by rw [hsplit]
    _ ≤ |qhat - q| + |qhat * θ| := abs_add_le (qhat - q) (qhat * θ)
    _ ≤ err + (|q| + err) * gamma fp 3 := add_le_add hqdiff hmulθ
    _ = eta / (2 * |a|) +
        (|quadraticRootPlus a b c s| + eta / (2 * |a|)) * gamma fp 3 := by
          rfl

/-- Absolute-input analogue for the rounded `-` quadratic-formula branch. -/
theorem flQuadraticRootMinusFromSqrt_abs_input_error_le
    (fp : FPModel) (a b c s shat eta : ℝ)
    (ha : a ≠ 0) (h3 : gammaValid fp 3) (heta : 0 ≤ eta)
    (hshat : |shat - s| ≤ eta) :
    |flQuadraticRootMinusFromSqrt fp a b shat - quadraticRootMinus a b c s| ≤
      eta / (2 * |a|) +
        (|quadraticRootMinus a b c s| + eta / (2 * |a|)) * gamma fp 3 := by
  let q := quadraticRootMinus a b c s
  let qhat := quadraticRootMinus a b c shat
  let err := eta / (2 * |a|)
  have hden_pos : 0 < 2 * |a| := by
    have ha_abs : 0 < |a| := abs_pos.mpr ha
    nlinarith
  have herr_nonneg : 0 ≤ err := by
    exact div_nonneg heta hden_pos.le
  have hqdiff : |qhat - q| ≤ err := by
    dsimp [qhat, q, err]
    exact quadraticRootMinus_sqrt_abs_perturb_abs_le_of_abs_sub_le
      a b c s shat eta ha heta hshat
  obtain ⟨θ, hθ, hfl⟩ :=
    flQuadraticRootMinusFromSqrt_rel_error_le_gamma3 fp a b c shat ha h3
  have hqhat_abs : |qhat| ≤ |q| + err := by
    have hsplit : q + (qhat - q) = qhat := by ring
    calc
      |qhat| = |q + (qhat - q)| := by rw [hsplit]
      _ ≤ |q| + |qhat - q| := abs_add_le q (qhat - q)
      _ ≤ |q| + err := add_le_add (le_refl |q|) hqdiff
  have hmulθ : |qhat * θ| ≤ (|q| + err) * gamma fp 3 := by
    rw [abs_mul]
    exact mul_le_mul hqhat_abs hθ (abs_nonneg θ)
      (add_nonneg (abs_nonneg q) herr_nonneg)
  have hsplit :
      qhat * (1 + θ) - q = (qhat - q) + qhat * θ := by ring
  calc
    |flQuadraticRootMinusFromSqrt fp a b shat - quadraticRootMinus a b c s| =
        |qhat * (1 + θ) - q| := by
          rw [hfl]
    _ = |(qhat - q) + qhat * θ| := by rw [hsplit]
    _ ≤ |qhat - q| + |qhat * θ| := abs_add_le (qhat - q) (qhat * θ)
    _ ≤ err + (|q| + err) * gamma fp 3 := add_le_add hqdiff hmulθ
    _ = eta / (2 * |a|) +
        (|quadraticRootMinus a b c s| + eta / (2 * |a|)) * gamma fp 3 := by
          rfl

/-- Square roots are Hölder-continuous with exponent `1/2` on the
nonnegative reals. -/
theorem abs_sqrt_sub_sqrt_le_sqrt_abs_sub (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  suffices hordered :
      ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → y ≤ x →
        |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| by
    rcases le_total y x with hxy | hyx
    · exact hordered hx hy hxy
    · have hswap := hordered hy hx hyx
      simpa [abs_sub_comm] using hswap
  intro x y hx hy hyx
  have hsqrt_le : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hyx
  have hdiff_nonneg : 0 ≤ Real.sqrt x - Real.sqrt y := sub_nonneg.mpr hsqrt_le
  have hxy_nonneg : 0 ≤ x - y := sub_nonneg.mpr hyx
  rw [abs_of_nonneg hdiff_nonneg, abs_of_nonneg hxy_nonneg]
  apply Real.le_sqrt_of_sq_le
  have hy_sqrt_nonneg : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hmul : (Real.sqrt y) ^ 2 ≤ Real.sqrt x * Real.sqrt y := by
    simpa [pow_two] using
      mul_le_mul_of_nonneg_right hsqrt_le hy_sqrt_nonneg
  have hsqx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsqy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  nlinarith [hmul, hsqx, hsqy]

/-- An absolute discriminant error gives a square-root input error bounded by
the square root of that discriminant error. -/
theorem quadraticSqrt_abs_error_le_of_discriminant_abs_error
    (D Dhat etaDisc : ℝ)
    (hD : 0 ≤ D) (hDhat : 0 ≤ Dhat) (_hetaDisc : 0 ≤ etaDisc)
    (hDerr : |Dhat - D| ≤ etaDisc) :
    |Real.sqrt Dhat - Real.sqrt D| ≤ Real.sqrt etaDisc := by
  exact (abs_sqrt_sub_sqrt_le_sqrt_abs_sub Dhat D hDhat hD).trans
    (Real.sqrt_le_sqrt hDerr)

/-- If the discriminant approximation has absolute error `etaDisc` and the
subsequent supplied square-root value has absolute error `etaSqrt`, the
rounded `+` branch has the corresponding propagated absolute-error bound. -/
theorem flQuadraticRootPlusFromSqrt_discriminant_abs_error_le
    (fp : FPModel) (a b c Dhat shat etaDisc etaSqrt : ℝ)
    (ha : a ≠ 0) (h3 : gammaValid fp 3)
    (hdisc : 0 ≤ quadraticDiscriminant a b c) (hDhat : 0 ≤ Dhat)
    (hetaDisc : 0 ≤ etaDisc) (hetaSqrt : 0 ≤ etaSqrt)
    (hDerr : |Dhat - quadraticDiscriminant a b c| ≤ etaDisc)
    (hsqrt : |shat - Real.sqrt Dhat| ≤ etaSqrt) :
    |flQuadraticRootPlusFromSqrt fp a b shat -
        quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      (etaSqrt + Real.sqrt etaDisc) / (2 * |a|) +
        (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
            (etaSqrt + Real.sqrt etaDisc) / (2 * |a|)) *
          gamma fp 3 := by
  let D := quadraticDiscriminant a b c
  let eta := etaSqrt + Real.sqrt etaDisc
  have heta : 0 ≤ eta := by
    exact add_nonneg hetaSqrt (Real.sqrt_nonneg etaDisc)
  have hsqrt_disc :
      |Real.sqrt Dhat - Real.sqrt D| ≤ Real.sqrt etaDisc := by
    exact quadraticSqrt_abs_error_le_of_discriminant_abs_error
      D Dhat etaDisc hdisc hDhat hetaDisc (by simpa [D] using hDerr)
  have hshat :
      |shat - Real.sqrt D| ≤ eta := by
    have hsplit :
        shat - Real.sqrt D =
          (shat - Real.sqrt Dhat) + (Real.sqrt Dhat - Real.sqrt D) := by
      ring
    calc
      |shat - Real.sqrt D| =
          |(shat - Real.sqrt Dhat) + (Real.sqrt Dhat - Real.sqrt D)| := by
            rw [hsplit]
      _ ≤ |shat - Real.sqrt Dhat| + |Real.sqrt Dhat - Real.sqrt D| :=
            abs_add_le (shat - Real.sqrt Dhat) (Real.sqrt Dhat - Real.sqrt D)
      _ ≤ etaSqrt + Real.sqrt etaDisc := add_le_add hsqrt hsqrt_disc
  simpa [D, eta] using
    flQuadraticRootPlusFromSqrt_abs_input_error_le
      fp a b c (Real.sqrt D) shat eta ha h3 heta hshat

/-- Discriminant-error propagation for the rounded `-` branch. -/
theorem flQuadraticRootMinusFromSqrt_discriminant_abs_error_le
    (fp : FPModel) (a b c Dhat shat etaDisc etaSqrt : ℝ)
    (ha : a ≠ 0) (h3 : gammaValid fp 3)
    (hdisc : 0 ≤ quadraticDiscriminant a b c) (hDhat : 0 ≤ Dhat)
    (hetaDisc : 0 ≤ etaDisc) (hetaSqrt : 0 ≤ etaSqrt)
    (hDerr : |Dhat - quadraticDiscriminant a b c| ≤ etaDisc)
    (hsqrt : |shat - Real.sqrt Dhat| ≤ etaSqrt) :
    |flQuadraticRootMinusFromSqrt fp a b shat -
        quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      (etaSqrt + Real.sqrt etaDisc) / (2 * |a|) +
        (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
            (etaSqrt + Real.sqrt etaDisc) / (2 * |a|)) *
          gamma fp 3 := by
  let D := quadraticDiscriminant a b c
  let eta := etaSqrt + Real.sqrt etaDisc
  have heta : 0 ≤ eta := by
    exact add_nonneg hetaSqrt (Real.sqrt_nonneg etaDisc)
  have hsqrt_disc :
      |Real.sqrt Dhat - Real.sqrt D| ≤ Real.sqrt etaDisc := by
    exact quadraticSqrt_abs_error_le_of_discriminant_abs_error
      D Dhat etaDisc hdisc hDhat hetaDisc (by simpa [D] using hDerr)
  have hshat :
      |shat - Real.sqrt D| ≤ eta := by
    have hsplit :
        shat - Real.sqrt D =
          (shat - Real.sqrt Dhat) + (Real.sqrt Dhat - Real.sqrt D) := by
      ring
    calc
      |shat - Real.sqrt D| =
          |(shat - Real.sqrt Dhat) + (Real.sqrt Dhat - Real.sqrt D)| := by
            rw [hsplit]
      _ ≤ |shat - Real.sqrt Dhat| + |Real.sqrt Dhat - Real.sqrt D| :=
            abs_add_le (shat - Real.sqrt Dhat) (Real.sqrt Dhat - Real.sqrt D)
      _ ≤ etaSqrt + Real.sqrt etaDisc := add_le_add hsqrt hsqrt_disc
  simpa [D, eta] using
    flQuadraticRootMinusFromSqrt_abs_input_error_le
      fp a b c (Real.sqrt D) shat eta ha h3 heta hshat

/-- The rounded `+` branch using the rounded discriminant and then
`fp.fl_sqrt` has an explicit absolute-error bound around the exact branch.

The separation hypothesis says the exact discriminant is at least the
rounded-discriminant absolute-error radius; this supplies both the exact
nonnegativity and the rounded-discriminant nonnegativity needed by `sqrt`. -/
theorem flQuadraticRootPlusRoundedDiscriminantSqrt_abs_error_le
    (fp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0)
    (hsep : flQuadraticDiscriminantAbsErrorBound fp a b c ≤
      quadraticDiscriminant a b c)
    (h3 : gammaValid fp 3) :
    |flQuadraticRootPlusRoundedDiscriminantSqrt fp a b c -
        quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      flQuadraticRoundedDiscriminantSqrtInputErrorBound fp a b c / (2 * |a|) +
        (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
            flQuadraticRoundedDiscriminantSqrtInputErrorBound fp a b c / (2 * |a|)) *
          gamma fp 3 := by
  let Dhat := flQuadraticDiscriminant fp a b c
  let E := flQuadraticDiscriminantAbsErrorBound fp a b c
  let etaSqrt := |Real.sqrt Dhat| * fp.u
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact flQuadraticDiscriminantAbsErrorBound_nonneg fp a b c
  have hdisc : 0 ≤ quadraticDiscriminant a b c := by
    exact le_trans hE_nonneg hsep
  have hDhat : 0 ≤ Dhat := by
    dsimp [Dhat]
    exact flQuadraticDiscriminant_nonneg_of_abs_error_bound_le
      fp a b c hsep
  have hDerr : |Dhat - quadraticDiscriminant a b c| ≤ E := by
    dsimp [Dhat, E]
    exact flQuadraticDiscriminant_abs_error_le_bound fp a b c
  obtain ⟨epsSqrt, hepsSqrt, hsqrt⟩ := fp.model_sqrt Dhat hDhat
  have hetaSqrt : 0 ≤ etaSqrt := by
    exact mul_nonneg (abs_nonneg _) fp.u_nonneg
  have hsqrt_abs :
      |fp.fl_sqrt Dhat - Real.sqrt Dhat| ≤ etaSqrt := by
    have hdiff :
        Real.sqrt Dhat * (1 + epsSqrt) - Real.sqrt Dhat =
          Real.sqrt Dhat * epsSqrt := by
      ring
    calc
      |fp.fl_sqrt Dhat - Real.sqrt Dhat| =
          |Real.sqrt Dhat * epsSqrt| := by
            rw [hsqrt, hdiff]
      _ = |Real.sqrt Dhat| * |epsSqrt| := by rw [abs_mul]
      _ ≤ |Real.sqrt Dhat| * fp.u :=
          mul_le_mul_of_nonneg_left hepsSqrt (abs_nonneg _)
      _ = etaSqrt := rfl
  simpa [flQuadraticRootPlusRoundedDiscriminantSqrt,
    flQuadraticRoundedDiscriminantSqrtInputErrorBound, Dhat, E, etaSqrt] using
    flQuadraticRootPlusFromSqrt_discriminant_abs_error_le
      fp a b c Dhat (fp.fl_sqrt Dhat) E etaSqrt ha h3 hdisc hDhat
      hE_nonneg hetaSqrt hDerr hsqrt_abs

/-- Rounded-discriminant/square-root absolute-error bound for the `-` branch. -/
theorem flQuadraticRootMinusRoundedDiscriminantSqrt_abs_error_le
    (fp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0)
    (hsep : flQuadraticDiscriminantAbsErrorBound fp a b c ≤
      quadraticDiscriminant a b c)
    (h3 : gammaValid fp 3) :
    |flQuadraticRootMinusRoundedDiscriminantSqrt fp a b c -
        quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      flQuadraticRoundedDiscriminantSqrtInputErrorBound fp a b c / (2 * |a|) +
        (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
            flQuadraticRoundedDiscriminantSqrtInputErrorBound fp a b c / (2 * |a|)) *
          gamma fp 3 := by
  let Dhat := flQuadraticDiscriminant fp a b c
  let E := flQuadraticDiscriminantAbsErrorBound fp a b c
  let etaSqrt := |Real.sqrt Dhat| * fp.u
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact flQuadraticDiscriminantAbsErrorBound_nonneg fp a b c
  have hdisc : 0 ≤ quadraticDiscriminant a b c := by
    exact le_trans hE_nonneg hsep
  have hDhat : 0 ≤ Dhat := by
    dsimp [Dhat]
    exact flQuadraticDiscriminant_nonneg_of_abs_error_bound_le
      fp a b c hsep
  have hDerr : |Dhat - quadraticDiscriminant a b c| ≤ E := by
    dsimp [Dhat, E]
    exact flQuadraticDiscriminant_abs_error_le_bound fp a b c
  obtain ⟨epsSqrt, hepsSqrt, hsqrt⟩ := fp.model_sqrt Dhat hDhat
  have hetaSqrt : 0 ≤ etaSqrt := by
    exact mul_nonneg (abs_nonneg _) fp.u_nonneg
  have hsqrt_abs :
      |fp.fl_sqrt Dhat - Real.sqrt Dhat| ≤ etaSqrt := by
    have hdiff :
        Real.sqrt Dhat * (1 + epsSqrt) - Real.sqrt Dhat =
          Real.sqrt Dhat * epsSqrt := by
      ring
    calc
      |fp.fl_sqrt Dhat - Real.sqrt Dhat| =
          |Real.sqrt Dhat * epsSqrt| := by
            rw [hsqrt, hdiff]
      _ = |Real.sqrt Dhat| * |epsSqrt| := by rw [abs_mul]
      _ ≤ |Real.sqrt Dhat| * fp.u :=
          mul_le_mul_of_nonneg_left hepsSqrt (abs_nonneg _)
      _ = etaSqrt := rfl
  simpa [flQuadraticRootMinusRoundedDiscriminantSqrt,
    flQuadraticRoundedDiscriminantSqrtInputErrorBound, Dhat, E, etaSqrt] using
    flQuadraticRootMinusFromSqrt_discriminant_abs_error_le
      fp a b c Dhat (fp.fl_sqrt Dhat) E etaSqrt ha h3 hdisc hDhat
      hE_nonneg hetaSqrt hDerr hsqrt_abs

/-- Mixed-precision rounded-discriminant/square-root absolute-error bound for
the `+` branch.  The discriminant is evaluated by `discFp`, while the square
root and final branch arithmetic are evaluated by `rootFp`. -/
theorem flQuadraticRootPlusMixedDiscriminantSqrt_abs_error_le
    (discFp rootFp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0)
    (hsep : flQuadraticDiscriminantAbsErrorBound discFp a b c ≤
      quadraticDiscriminant a b c)
    (h3 : gammaValid rootFp 3) :
    |flQuadraticRootPlusMixedDiscriminantSqrt discFp rootFp a b c -
        quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      flQuadraticMixedDiscriminantSqrtRootPlusAbsErrorBound discFp rootFp a b c := by
  let Dhat := flQuadraticDiscriminant discFp a b c
  let E := flQuadraticDiscriminantAbsErrorBound discFp a b c
  let etaSqrt := |Real.sqrt Dhat| * rootFp.u
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact flQuadraticDiscriminantAbsErrorBound_nonneg discFp a b c
  have hdisc : 0 ≤ quadraticDiscriminant a b c := by
    exact le_trans hE_nonneg hsep
  have hDhat : 0 ≤ Dhat := by
    dsimp [Dhat]
    exact flQuadraticDiscriminant_nonneg_of_abs_error_bound_le
      discFp a b c hsep
  have hDerr : |Dhat - quadraticDiscriminant a b c| ≤ E := by
    dsimp [Dhat, E]
    exact flQuadraticDiscriminant_abs_error_le_bound discFp a b c
  obtain ⟨epsSqrt, hepsSqrt, hsqrt⟩ := rootFp.model_sqrt Dhat hDhat
  have hetaSqrt : 0 ≤ etaSqrt := by
    exact mul_nonneg (abs_nonneg _) rootFp.u_nonneg
  have hsqrt_abs :
      |rootFp.fl_sqrt Dhat - Real.sqrt Dhat| ≤ etaSqrt := by
    have hdiff :
        Real.sqrt Dhat * (1 + epsSqrt) - Real.sqrt Dhat =
          Real.sqrt Dhat * epsSqrt := by
      ring
    calc
      |rootFp.fl_sqrt Dhat - Real.sqrt Dhat| =
          |Real.sqrt Dhat * epsSqrt| := by
            rw [hsqrt, hdiff]
      _ = |Real.sqrt Dhat| * |epsSqrt| := by rw [abs_mul]
      _ ≤ |Real.sqrt Dhat| * rootFp.u :=
          mul_le_mul_of_nonneg_left hepsSqrt (abs_nonneg _)
      _ = etaSqrt := rfl
  simpa [flQuadraticRootPlusMixedDiscriminantSqrt,
    flQuadraticMixedDiscriminantSqrtRootPlusAbsErrorBound,
    flQuadraticMixedDiscriminantSqrtInputErrorBound, Dhat, E, etaSqrt] using
    flQuadraticRootPlusFromSqrt_discriminant_abs_error_le
      rootFp a b c Dhat (rootFp.fl_sqrt Dhat) E etaSqrt ha h3 hdisc hDhat
      hE_nonneg hetaSqrt hDerr hsqrt_abs

/-- Mixed-precision rounded-discriminant/square-root absolute-error bound for
the `-` branch. -/
theorem flQuadraticRootMinusMixedDiscriminantSqrt_abs_error_le
    (discFp rootFp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0)
    (hsep : flQuadraticDiscriminantAbsErrorBound discFp a b c ≤
      quadraticDiscriminant a b c)
    (h3 : gammaValid rootFp 3) :
    |flQuadraticRootMinusMixedDiscriminantSqrt discFp rootFp a b c -
        quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      flQuadraticMixedDiscriminantSqrtRootMinusAbsErrorBound discFp rootFp a b c := by
  let Dhat := flQuadraticDiscriminant discFp a b c
  let E := flQuadraticDiscriminantAbsErrorBound discFp a b c
  let etaSqrt := |Real.sqrt Dhat| * rootFp.u
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact flQuadraticDiscriminantAbsErrorBound_nonneg discFp a b c
  have hdisc : 0 ≤ quadraticDiscriminant a b c := by
    exact le_trans hE_nonneg hsep
  have hDhat : 0 ≤ Dhat := by
    dsimp [Dhat]
    exact flQuadraticDiscriminant_nonneg_of_abs_error_bound_le
      discFp a b c hsep
  have hDerr : |Dhat - quadraticDiscriminant a b c| ≤ E := by
    dsimp [Dhat, E]
    exact flQuadraticDiscriminant_abs_error_le_bound discFp a b c
  obtain ⟨epsSqrt, hepsSqrt, hsqrt⟩ := rootFp.model_sqrt Dhat hDhat
  have hetaSqrt : 0 ≤ etaSqrt := by
    exact mul_nonneg (abs_nonneg _) rootFp.u_nonneg
  have hsqrt_abs :
      |rootFp.fl_sqrt Dhat - Real.sqrt Dhat| ≤ etaSqrt := by
    have hdiff :
        Real.sqrt Dhat * (1 + epsSqrt) - Real.sqrt Dhat =
          Real.sqrt Dhat * epsSqrt := by
      ring
    calc
      |rootFp.fl_sqrt Dhat - Real.sqrt Dhat| =
          |Real.sqrt Dhat * epsSqrt| := by
            rw [hsqrt, hdiff]
      _ = |Real.sqrt Dhat| * |epsSqrt| := by rw [abs_mul]
      _ ≤ |Real.sqrt Dhat| * rootFp.u :=
          mul_le_mul_of_nonneg_left hepsSqrt (abs_nonneg _)
      _ = etaSqrt := rfl
  simpa [flQuadraticRootMinusMixedDiscriminantSqrt,
    flQuadraticMixedDiscriminantSqrtRootMinusAbsErrorBound,
    flQuadraticMixedDiscriminantSqrtInputErrorBound, Dhat, E, etaSqrt] using
    flQuadraticRootMinusFromSqrt_discriminant_abs_error_le
      rootFp a b c Dhat (rootFp.fl_sqrt Dhat) E etaSqrt ha h3 hdisc hDhat
      hE_nonneg hetaSqrt hDerr hsqrt_abs

/-- The rounded `+` quadratic-formula branch with the square root computed by
`fp.fl_sqrt` has an explicit absolute-error bound around the exact branch using
`sqrt(b^2 - 4*a*c)`.

This instantiates the local `FPModel.model_sqrt` contract for the square-root
operation.  The discriminant is still the exact real expression; rounded
formation of `b^2 - 4*a*c`, finite-range overflow/underflow guards, and
branch-selection/cancellation comparisons remain separate obligations. -/
theorem flQuadraticRootPlusComputedSqrt_abs_error_le
    (fp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0) (hdisc : 0 ≤ quadraticDiscriminant a b c)
    (h3 : gammaValid fp 3) :
    |flQuadraticRootPlusComputedSqrt fp a b c -
        quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      |Real.sqrt (quadraticDiscriminant a b c)| * fp.u / (2 * |a|) +
        (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
            |Real.sqrt (quadraticDiscriminant a b c)| * fp.u / (2 * |a|)) *
          gamma fp 3 := by
  obtain ⟨epsSqrt, hepsSqrt, hsqrt⟩ :=
    fp.model_sqrt (quadraticDiscriminant a b c) hdisc
  simpa [flQuadraticRootPlusComputedSqrt] using
    flQuadraticRootPlusWithSqrtRelError_abs_error_le
      fp a b c (Real.sqrt (quadraticDiscriminant a b c))
      (fp.fl_sqrt (quadraticDiscriminant a b c)) epsSqrt ha h3 hsqrt hepsSqrt

/-- The rounded `-` quadratic-formula branch with the square root computed by
`fp.fl_sqrt` has the analogous explicit absolute-error bound. -/
theorem flQuadraticRootMinusComputedSqrt_abs_error_le
    (fp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0) (hdisc : 0 ≤ quadraticDiscriminant a b c)
    (h3 : gammaValid fp 3) :
    |flQuadraticRootMinusComputedSqrt fp a b c -
        quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      |Real.sqrt (quadraticDiscriminant a b c)| * fp.u / (2 * |a|) +
        (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
            |Real.sqrt (quadraticDiscriminant a b c)| * fp.u / (2 * |a|)) *
          gamma fp 3 := by
  obtain ⟨epsSqrt, hepsSqrt, hsqrt⟩ :=
    fp.model_sqrt (quadraticDiscriminant a b c) hdisc
  simpa [flQuadraticRootMinusComputedSqrt] using
    flQuadraticRootMinusWithSqrtRelError_abs_error_le
      fp a b c (Real.sqrt (quadraticDiscriminant a b c))
      (fp.fl_sqrt (quadraticDiscriminant a b c)) epsSqrt ha h3 hsqrt hepsSqrt

/-- The rounded recovery step `fl(c / fl(a*xhat))` is a relative perturbation
of the exact recovery value `c/(a*xhat)` by at most `gamma fp 2`.

This proves the floating-point stability of the two-operation recovery
micro-kernel used in Higham §1.8 once the other root `xhat` has been supplied.
It does not by itself prove that `xhat` was computed accurately, nor does it
model overflow/underflow in the quadratic formula. -/
theorem flQuadraticRecoveredRootFromOther_rel_error_le_gamma2
    (fp : FPModel) (a c xhat : ℝ)
    (hden : a * xhat ≠ 0) (h2 : gammaValid fp 2) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 2 ∧
      flQuadraticRecoveredRootFromOther fp a c xhat =
        (c / (a * xhat)) * (1 + θ) := by
  obtain ⟨δm, hδm, hmul⟩ := fp.model_mul a xhat
  have hu_lt_one : fp.u < 1 := by
    unfold gammaValid at h2
    norm_num at h2
    nlinarith [fp.u_nonneg]
  have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
  have hδm_pos : 0 < 1 + δm := by
    nlinarith
  have hmul_ne : fp.fl_mul a xhat ≠ 0 := by
    rw [hmul]
    exact mul_ne_zero hden hδm_pos.ne'
  obtain ⟨δd, hδd, hdiv⟩ := fp.model_div c (fp.fl_mul a xhat) hmul_ne
  let θ : ℝ := (1 + δd) / (1 + δm) - 1
  refine ⟨θ, ?_, ?_⟩
  · have hθeq : θ = (δd - δm) / (1 + δm) := by
      dsimp [θ]
      field_simp [hδm_pos.ne']
      ring
    have hnum0 : |δd - δm| ≤ |δd| + |δm| := abs_sub δd δm
    have hnum : |δd - δm| ≤ 2 * fp.u := by
      nlinarith [hnum0, hδd, hδm]
    have hnum_nonneg : 0 ≤ |δd - δm| := abs_nonneg _
    have hden_lower : 1 - fp.u ≤ 1 + δm := by
      nlinarith [hδm_lower]
    have hden_lower_pos : 0 < 1 - fp.u := by
      nlinarith [hu_lt_one]
    have hfrac_den :
        |δd - δm| / (1 + δm) ≤ |δd - δm| / (1 - fp.u) :=
      div_le_div_of_nonneg_left hnum_nonneg hden_lower_pos hden_lower
    have hfrac_num :
        |δd - δm| / (1 - fp.u) ≤ (2 * fp.u) / (1 - fp.u) :=
      div_le_div_of_nonneg_right hnum hden_lower_pos.le
    have hden2_pos : 0 < 1 - 2 * fp.u := by
      unfold gammaValid at h2
      norm_num at h2
      linarith
    have hden_order : 1 - 2 * fp.u ≤ 1 - fp.u := by
      nlinarith [fp.u_nonneg]
    have hfrac_gamma :
        (2 * fp.u) / (1 - fp.u) ≤ (2 * fp.u) / (1 - 2 * fp.u) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) fp.u_nonneg) hden2_pos hden_order
    calc
      |θ| = |δd - δm| / (1 + δm) := by
        rw [hθeq, abs_div, abs_of_pos hδm_pos]
      _ ≤ |δd - δm| / (1 - fp.u) := hfrac_den
      _ ≤ (2 * fp.u) / (1 - fp.u) := hfrac_num
      _ ≤ gamma fp 2 := by
        simpa [gamma] using hfrac_gamma
  · dsimp [flQuadraticRecoveredRootFromOther]
    rw [hdiv, hmul]
    dsimp [θ]
    field_simp [hden, hδm_pos.ne']
    ring

/-- If a supplied root `xhat` is close enough to the exact companion root `x`,
then the rounded product-recovery step has an absolute-error bound around the
other exact root `y = c/(a*x)`.

The radius separates the input-root perturbation term from the final
two-operation recovery rounding term. -/
theorem flQuadraticRecoveredRootFromOther_abs_error_le_of_abs_error
    (fp : FPModel) (a c x y xhat eta : ℝ)
    (hy : y = c / (a * x))
    (ha : a ≠ 0) (hx : x ≠ 0)
    (hsep : eta < |x|)
    (hxhat_err : |xhat - x| ≤ eta)
    (h2 : gammaValid fp 2) :
    |flQuadraticRecoveredRootFromOther fp a c xhat - y| ≤
      |y| * eta / (|x| - eta) +
        (|y| + |y| * eta / (|x| - eta)) * gamma fp 2 := by
  have heta_nonneg : 0 ≤ eta := le_trans (abs_nonneg _) hxhat_err
  have hden_pos : 0 < |x| - eta := by linarith
  have hxhat_lower : |x| - eta ≤ |xhat| := by
    have htri : |x| ≤ |x - xhat| + |xhat| := by
      calc
        |x| = |(x - xhat) + xhat| := by ring_nf
        _ ≤ |x - xhat| + |xhat| := abs_add_le _ _
    have hxhat_err' : |x - xhat| ≤ eta := by
      simpa [abs_sub_comm] using hxhat_err
    linarith
  have hxhat_abs_pos : 0 < |xhat| := lt_of_lt_of_le hden_pos hxhat_lower
  have hxhat_ne : xhat ≠ 0 := (abs_pos.mp hxhat_abs_pos)
  have hrec_den : a * xhat ≠ 0 := mul_ne_zero ha hxhat_ne
  obtain ⟨θ, hθ, hrec⟩ :=
    flQuadraticRecoveredRootFromOther_rel_error_le_gamma2 fp a c xhat hrec_den h2
  let z : ℝ := c / (a * xhat)
  let B : ℝ := |y| * eta / (|x| - eta)
  have hdiff_eq : z - y = y * ((x - xhat) / xhat) := by
    dsimp [z]
    rw [hy]
    field_simp [ha, hx, hxhat_ne]
  have hratio : |(x - xhat) / xhat| ≤ eta / (|x| - eta) := by
    have hxhat_err' : |x - xhat| ≤ eta := by
      simpa [abs_sub_comm] using hxhat_err
    have hfirst : |x - xhat| / |xhat| ≤ eta / |xhat| :=
      div_le_div_of_nonneg_right hxhat_err' hxhat_abs_pos.le
    have hsecond : eta / |xhat| ≤ eta / (|x| - eta) :=
      div_le_div_of_nonneg_left heta_nonneg hden_pos hxhat_lower
    calc
      |(x - xhat) / xhat| = |x - xhat| / |xhat| := by rw [abs_div]
      _ ≤ eta / |xhat| := hfirst
      _ ≤ eta / (|x| - eta) := hsecond
  have hz_err : |z - y| ≤ B := by
    calc
      |z - y| = |y| * |(x - xhat) / xhat| := by
        rw [hdiff_eq, abs_mul]
      _ ≤ |y| * (eta / (|x| - eta)) :=
          mul_le_mul_of_nonneg_left hratio (abs_nonneg y)
      _ = B := by
        dsimp [B]
        ring
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg (abs_nonneg y) heta_nonneg) hden_pos.le
  have hz_abs : |z| ≤ |y| + B := by
    calc
      |z| = |y + (z - y)| := by ring_nf
      _ ≤ |y| + |z - y| := abs_add_le _ _
      _ ≤ |y| + B := by linarith
  have hgamma_nonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp h2
  have hz_theta :
      |z * θ| ≤ (|y| + B) * gamma fp 2 := by
    rw [abs_mul]
    exact mul_le_mul hz_abs hθ (abs_nonneg θ) (by linarith [abs_nonneg y, hB_nonneg])
  calc
    |flQuadraticRecoveredRootFromOther fp a c xhat - y|
        = |z * (1 + θ) - y| := by
            rw [hrec]
    _ = |(z - y) + z * θ| := by ring_nf
    _ ≤ |z - y| + |z * θ| := abs_add_le _ _
    _ ≤ B + (|y| + B) * gamma fp 2 := by
          exact add_le_add hz_err hz_theta
    _ = |y| * eta / (|x| - eta) +
        (|y| + |y| * eta / (|x| - eta)) * gamma fp 2 := by
          dsimp [B]

/-- Recover the `-` root from an approximate `+` root.  The theorem composes
the exact product identity with the rounded recovery micro-kernel. -/
theorem flQuadraticRecoveredRootMinusFromPlus_abs_error_le
    (fp : FPModel) (a b c s xhat eta : ℝ)
    (ha : a ≠ 0) (hs : s ^ 2 = quadraticDiscriminant a b c)
    (hplus : quadraticRootPlus a b c s ≠ 0)
    (hsep : eta < |quadraticRootPlus a b c s|)
    (hxhat_err : |xhat - quadraticRootPlus a b c s| ≤ eta)
    (h2 : gammaValid fp 2) :
    |flQuadraticRecoveredRootFromOther fp a c xhat -
        quadraticRootMinus a b c s| ≤
      |quadraticRootMinus a b c s| * eta /
          (|quadraticRootPlus a b c s| - eta) +
        (|quadraticRootMinus a b c s| +
            |quadraticRootMinus a b c s| * eta /
              (|quadraticRootPlus a b c s| - eta)) * gamma fp 2 := by
  exact
    flQuadraticRecoveredRootFromOther_abs_error_le_of_abs_error
      fp a c (quadraticRootPlus a b c s) (quadraticRootMinus a b c s)
      xhat eta
      (quadraticRootMinus_eq_c_div_a_mul_rootPlus a b c s ha hs hplus)
      ha hplus hsep hxhat_err h2

/-- Recover the `+` root from an approximate `-` root. -/
theorem flQuadraticRecoveredRootPlusFromMinus_abs_error_le
    (fp : FPModel) (a b c s xhat eta : ℝ)
    (ha : a ≠ 0) (hs : s ^ 2 = quadraticDiscriminant a b c)
    (hminus : quadraticRootMinus a b c s ≠ 0)
    (hsep : eta < |quadraticRootMinus a b c s|)
    (hxhat_err : |xhat - quadraticRootMinus a b c s| ≤ eta)
    (h2 : gammaValid fp 2) :
    |flQuadraticRecoveredRootFromOther fp a c xhat -
        quadraticRootPlus a b c s| ≤
      |quadraticRootPlus a b c s| * eta /
          (|quadraticRootMinus a b c s| - eta) +
        (|quadraticRootPlus a b c s| +
            |quadraticRootPlus a b c s| * eta /
              (|quadraticRootMinus a b c s| - eta)) * gamma fp 2 := by
  exact
    flQuadraticRecoveredRootFromOther_abs_error_le_of_abs_error
      fp a c (quadraticRootMinus a b c s) (quadraticRootPlus a b c s)
      xhat eta
      (quadraticRootPlus_eq_c_div_a_mul_rootMinus a b c s ha hs hminus)
      ha hminus hsep hxhat_err h2

/-- Recover the `-` root from the concrete rounded-discriminant/square-root
computed `+` branch, under the separation guard that keeps the supplied branch
nonzero. -/
theorem flQuadraticRecoveredRootMinusFromRoundedPlusDiscriminantSqrt_abs_error_le
    (fp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0)
    (hplus : quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c)) ≠ 0)
    (hdiscSep : flQuadraticDiscriminantAbsErrorBound fp a b c ≤
      quadraticDiscriminant a b c)
    (hbranchSep : flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c <
      |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))|)
    (h2 : gammaValid fp 2) (h3 : gammaValid fp 3) :
    |flQuadraticRecoveredRootFromOther fp a c
        (flQuadraticRootPlusRoundedDiscriminantSqrt fp a b c) -
        quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      |quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| *
          flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c /
          (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| -
            flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c) +
        (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
            |quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| *
              flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c /
              (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| -
                flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c)) *
          gamma fp 2 := by
  have hdisc : 0 ≤ quadraticDiscriminant a b c :=
    le_trans (flQuadraticDiscriminantAbsErrorBound_nonneg fp a b c) hdiscSep
  have hs : (Real.sqrt (quadraticDiscriminant a b c)) ^ 2 =
      quadraticDiscriminant a b c := Real.sq_sqrt hdisc
  have hbranch :
      |flQuadraticRootPlusRoundedDiscriminantSqrt fp a b c -
          quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
        flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c := by
    simpa [flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound] using
      flQuadraticRootPlusRoundedDiscriminantSqrt_abs_error_le fp a b c ha hdiscSep h3
  exact
    flQuadraticRecoveredRootMinusFromPlus_abs_error_le
      fp a b c (Real.sqrt (quadraticDiscriminant a b c))
      (flQuadraticRootPlusRoundedDiscriminantSqrt fp a b c)
      (flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c)
      ha hs hplus hbranchSep hbranch h2

/-- Recover the `+` root from the concrete rounded-discriminant/square-root
computed `-` branch. -/
theorem flQuadraticRecoveredRootPlusFromRoundedMinusDiscriminantSqrt_abs_error_le
    (fp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0)
    (hminus : quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c)) ≠ 0)
    (hdiscSep : flQuadraticDiscriminantAbsErrorBound fp a b c ≤
      quadraticDiscriminant a b c)
    (hbranchSep : flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c <
      |quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))|)
    (h2 : gammaValid fp 2) (h3 : gammaValid fp 3) :
    |flQuadraticRecoveredRootFromOther fp a c
        (flQuadraticRootMinusRoundedDiscriminantSqrt fp a b c) -
        quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
      |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| *
          flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c /
          (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| -
            flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c) +
        (|quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| +
            |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| *
              flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c /
              (|quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| -
                flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c)) *
          gamma fp 2 := by
  have hdisc : 0 ≤ quadraticDiscriminant a b c :=
    le_trans (flQuadraticDiscriminantAbsErrorBound_nonneg fp a b c) hdiscSep
  have hs : (Real.sqrt (quadraticDiscriminant a b c)) ^ 2 =
      quadraticDiscriminant a b c := Real.sq_sqrt hdisc
  have hbranch :
      |flQuadraticRootMinusRoundedDiscriminantSqrt fp a b c -
          quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| ≤
        flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c := by
    simpa [flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound] using
      flQuadraticRootMinusRoundedDiscriminantSqrt_abs_error_le fp a b c ha hdiscSep h3
  exact
    flQuadraticRecoveredRootPlusFromMinus_abs_error_le
      fp a b c (Real.sqrt (quadraticDiscriminant a b c))
      (flQuadraticRootMinusRoundedDiscriminantSqrt fp a b c)
      (flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c)
      ha hs hminus hbranchSep hbranch h2

/-- The rounded sign-of-`b` larger-root algorithm inherits the branch
absolute-error bound from the selected rounded-discriminant/square-root
branch. -/
theorem flQuadraticRootLargeByBSignRoundedDiscriminantSqrt_abs_error_le
    (fp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0)
    (hdiscSep : flQuadraticDiscriminantAbsErrorBound fp a b c ≤
      quadraticDiscriminant a b c)
    (h3 : gammaValid fp 3) :
    |flQuadraticRootLargeByBSignRoundedDiscriminantSqrt fp a b c -
        quadraticRootLargeByBSign a b c
          (Real.sqrt (quadraticDiscriminant a b c))| ≤
      flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound fp a b c := by
  by_cases hb : 0 ≤ b
  · simpa [flQuadraticRootLargeByBSignRoundedDiscriminantSqrt,
      quadraticRootLargeByBSign,
      flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound, hb] using
      flQuadraticRootMinusRoundedDiscriminantSqrt_abs_error_le
        fp a b c ha hdiscSep h3
  · simpa [flQuadraticRootLargeByBSignRoundedDiscriminantSqrt,
      quadraticRootLargeByBSign,
      flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound, hb] using
      flQuadraticRootPlusRoundedDiscriminantSqrt_abs_error_le
        fp a b c ha hdiscSep h3

/-- The rounded sign-of-`b` companion-root algorithm computes the
larger-magnitude branch and then recovers the other root with an explicit
absolute-error radius. -/
theorem flQuadraticRootSmallByBSignRoundedDiscriminantSqrt_abs_error_le
    (fp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0)
    (hdiscSep : flQuadraticDiscriminantAbsErrorBound fp a b c ≤
      quadraticDiscriminant a b c)
    (hlargeNonzero :
      quadraticRootLargeByBSign a b c
        (Real.sqrt (quadraticDiscriminant a b c)) ≠ 0)
    (hbranchSep :
      flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound fp a b c <
        |quadraticRootLargeByBSign a b c
          (Real.sqrt (quadraticDiscriminant a b c))|)
    (h2 : gammaValid fp 2) (h3 : gammaValid fp 3) :
    |flQuadraticRootSmallByBSignRoundedDiscriminantSqrt fp a b c -
        quadraticRootSmallByBSign a b c
          (Real.sqrt (quadraticDiscriminant a b c))| ≤
      flQuadraticRoundedDiscriminantSqrtRootSmallRecoveryAbsErrorBound fp a b c := by
  by_cases hb : 0 ≤ b
  · have hminus :
        quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c)) ≠ 0 := by
      simpa [quadraticRootLargeByBSign, hb] using hlargeNonzero
    have hsep :
        flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound fp a b c <
          |quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))| := by
      simpa [flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound,
        quadraticRootLargeByBSign, hb] using hbranchSep
    simpa [flQuadraticRootSmallByBSignRoundedDiscriminantSqrt,
      flQuadraticRootLargeByBSignRoundedDiscriminantSqrt,
      quadraticRootSmallByBSign,
      flQuadraticRoundedDiscriminantSqrtRootSmallRecoveryAbsErrorBound, hb] using
      flQuadraticRecoveredRootPlusFromRoundedMinusDiscriminantSqrt_abs_error_le
        fp a b c ha hminus hdiscSep hsep h2 h3
  · have hplus :
        quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c)) ≠ 0 := by
      simpa [quadraticRootLargeByBSign, hb] using hlargeNonzero
    have hsep :
        flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound fp a b c <
          |quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))| := by
      simpa [flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound,
        quadraticRootLargeByBSign, hb] using hbranchSep
    simpa [flQuadraticRootSmallByBSignRoundedDiscriminantSqrt,
      flQuadraticRootLargeByBSignRoundedDiscriminantSqrt,
      quadraticRootSmallByBSign,
      flQuadraticRoundedDiscriminantSqrtRootSmallRecoveryAbsErrorBound, hb] using
      flQuadraticRecoveredRootMinusFromRoundedPlusDiscriminantSqrt_abs_error_le
        fp a b c ha hplus hdiscSep hsep h2 h3

/-- Pair form of the rounded sign-of-`b` quadratic-root algorithm: the first
component is the larger-magnitude root selected by sign of `b`, and the second
component is the product-recovered companion root. -/
theorem flQuadraticRootsByBSignRoundedDiscriminantSqrt_abs_error_le
    (fp : FPModel) (a b c : ℝ)
    (ha : a ≠ 0)
    (hdiscSep : flQuadraticDiscriminantAbsErrorBound fp a b c ≤
      quadraticDiscriminant a b c)
    (hlargeNonzero :
      quadraticRootLargeByBSign a b c
        (Real.sqrt (quadraticDiscriminant a b c)) ≠ 0)
    (hbranchSep :
      flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound fp a b c <
        |quadraticRootLargeByBSign a b c
          (Real.sqrt (quadraticDiscriminant a b c))|)
    (h2 : gammaValid fp 2) (h3 : gammaValid fp 3) :
    |(flQuadraticRootsByBSignRoundedDiscriminantSqrt fp a b c).1 -
        quadraticRootLargeByBSign a b c
          (Real.sqrt (quadraticDiscriminant a b c))| ≤
        flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound fp a b c ∧
      |(flQuadraticRootsByBSignRoundedDiscriminantSqrt fp a b c).2 -
          quadraticRootSmallByBSign a b c
            (Real.sqrt (quadraticDiscriminant a b c))| ≤
        flQuadraticRoundedDiscriminantSqrtRootSmallRecoveryAbsErrorBound fp a b c := by
  constructor
  · simpa [flQuadraticRootsByBSignRoundedDiscriminantSqrt] using
      flQuadraticRootLargeByBSignRoundedDiscriminantSqrt_abs_error_le
        fp a b c ha hdiscSep h3
  · simpa [flQuadraticRootsByBSignRoundedDiscriminantSqrt] using
      flQuadraticRootSmallByBSignRoundedDiscriminantSqrt_abs_error_le
        fp a b c ha hdiscSep hlargeNonzero hbranchSep h2 h3

/-! ## Exact overflow/underflow scaling examples -/

/-- The coefficient scale `10^20` from Higham §1.8's overflow examples. -/
noncomputable def quadraticOverflowScale : ℝ := (10 : ℝ) ^ 20

private theorem ieeeDoubleFormat_minNormalMagnitude_le_one :
    FloatingPointFormat.minNormalMagnitude FloatingPointFormat.ieeeDoubleFormat ≤
      (1 : ℝ) := by
  rw [FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.betaR]
  norm_num
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

private theorem two_pow_137_le_ieeeDoubleFormat_maxFiniteMagnitude :
    (2 : ℝ) ^ (137 : ℕ) ≤
      FloatingPointFormat.maxFiniteMagnitude FloatingPointFormat.ieeeDoubleFormat := by
  rw [FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.betaR]
  have hfactor : (1 / 2 : ℝ) ≤ 1 - (2 : ℝ) ^ (-53 : ℤ) := by
    rw [zpow_neg]
    have hden : (2 : ℝ) ≤ (2 : ℝ) ^ (53 : ℕ) := by
      exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (53 : ℕ) ≠ 0)
    have hinv : 1 / ((2 : ℝ) ^ (53 : ℕ)) ≤ 1 / (2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
    norm_num at hinv ⊢
  have hpow : (2 : ℝ) ^ (137 : ℕ) ≤ (2 : ℝ) ^ (1023 : ℕ) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (137 : ℕ) ≤ 1023)
  have hhalf :
      (2 : ℝ) ^ (1023 : ℕ) =
        (2 : ℝ) ^ (1024 : ℕ) * (1 / 2 : ℝ) := by
    have h :
        (2 : ℝ) ^ (1024 : ℕ) = (2 : ℝ) ^ (1023 : ℕ) * 2 := by
      rw [show (1024 : ℕ) = 1023 + 1 by norm_num, pow_succ]
    rw [h, mul_assoc]
    rw [show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, mul_one]
  calc
    (2 : ℝ) ^ (137 : ℕ) ≤ (2 : ℝ) ^ (1023 : ℕ) := hpow
    _ = (2 : ℝ) ^ (1024 : ℕ) * (1 / 2 : ℝ) := hhalf
    _ ≤ (2 : ℝ) ^ (1024 : ℕ) * (1 - (2 : ℝ) ^ (-53 : ℤ)) := by
      exact mul_le_mul_of_nonneg_left hfactor (by positivity)

private theorem ieeeDoubleFormat_finiteNormalRange_of_one_le_abs_le_two_pow_137
    {x : ℝ} (hlo : (1 : ℝ) ≤ |x|)
    (hhi : |x| ≤ (2 : ℝ) ^ (137 : ℕ)) :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat x :=
  ⟨le_trans ieeeDoubleFormat_minNormalMagnitude_le_one hlo,
    le_trans hhi two_pow_137_le_ieeeDoubleFormat_maxFiniteMagnitude⟩

private theorem ieeeDoubleFormat_unitRoundoff_lt_one_eighth :
    FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat <
      (1 / 8 : ℝ) := by
  rw [FloatingPointFormat.ieeeDoubleFormat_unitRoundoff, zpow_neg]
  norm_num

private theorem ieeeDoubleFormat_unitRoundoff_lt_one_over_1024 :
    FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat <
      (1 / 1024 : ℝ) := by
  rw [FloatingPointFormat.ieeeDoubleFormat_unitRoundoff, zpow_neg]
  norm_num

private theorem one_add_delta_abs_bounds_of_abs_lt_one_eighth
    {δ : ℝ} (hδ : |δ| < (1 / 8 : ℝ)) :
    (7 / 8 : ℝ) ≤ |1 + δ| ∧ |1 + δ| ≤ (9 / 8 : ℝ) := by
  have hδ_hi : δ < (1 / 8 : ℝ) :=
    lt_of_le_of_lt (le_abs_self δ) hδ
  have hδ_lo : -(1 / 8 : ℝ) < δ := by
    have hneg : -δ < (1 / 8 : ℝ) :=
      lt_of_le_of_lt (neg_le_abs δ) hδ
    linarith
  have hpos : 0 ≤ 1 + δ := by linarith
  rw [abs_of_nonneg hpos]
  constructor <;> linarith

private theorem one_add_delta_bounds_of_abs_lt_one_over_1024
    {δ : ℝ} (hδ : |δ| < (1 / 1024 : ℝ)) :
    (1023 / 1024 : ℝ) ≤ 1 + δ ∧
      1 + δ ≤ (1025 / 1024 : ℝ) := by
  have hδ_hi : δ < (1 / 1024 : ℝ) :=
    lt_of_le_of_lt (le_abs_self δ) hδ
  have hδ_lo : -(1 / 1024 : ℝ) < δ := by
    have hneg : -δ < (1 / 1024 : ℝ) :=
      lt_of_le_of_lt (neg_le_abs δ) hδ
    linarith
  constructor <;> linarith

private theorem finiteNormalRange_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ} (hx : fmt.finiteNormalRange x) :
    ¬ fmt.finiteUnderflowRange x :=
  not_lt_of_ge hx.1

private theorem finiteNormalRange_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ} (hx : fmt.finiteNormalRange x) :
    ¬ fmt.finiteOverflowRange x :=
  not_lt_of_ge hx.2

/-- In the first displayed §1.8 overflow example, the standard quadratic
formula's `b*b` intermediate is outside the IEEE single finite range. -/
theorem quadraticOverflowExample_b_square_single_finiteOverflowRange :
    FloatingPointFormat.finiteOverflowRange FloatingPointFormat.ieeeSingleFormat
      ((-3 * quadraticOverflowScale) ^ 2) := by
  rw [FloatingPointFormat.finiteOverflowRange]
  rw [abs_of_nonneg (sq_nonneg _)]
  have hmax :
      FloatingPointFormat.maxFiniteMagnitude FloatingPointFormat.ieeeSingleFormat <
        (2 : ℝ) ^ (128 : ℕ) := by
    simpa [FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR] using
      (FloatingPointFormat.maxFiniteMagnitude_lt_beta_pow_emax
        FloatingPointFormat.ieeeSingleFormat)
  have hpow : (2 : ℝ) ^ (128 : ℕ) < (-3 * quadraticOverflowScale) ^ 2 := by
    unfold quadraticOverflowScale
    norm_num
  exact lt_trans hmax hpow

/-- In IEEE double finite-format range, the unscaled displayed overflow
example's `b*b` intermediate is a normal finite quantity.  This is the concrete
range side of Higham §1.8's instruction to evaluate the discriminant in double
precision, not a full IEEE operation/flag theorem. -/
theorem quadraticOverflowExample_b_square_double_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
      ((-3 * quadraticOverflowScale) ^ 2) := by
  apply ieeeDoubleFormat_finiteNormalRange_of_one_le_abs_le_two_pow_137
  · unfold quadraticOverflowScale
    norm_num
  · unfold quadraticOverflowScale
    norm_num

/-- In IEEE double finite-format range, the unscaled displayed overflow
example's `4*a` intermediate is a normal finite quantity. -/
theorem quadraticOverflowExample_four_a_double_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
      (4 * quadraticOverflowScale) := by
  apply ieeeDoubleFormat_finiteNormalRange_of_one_le_abs_le_two_pow_137
  · unfold quadraticOverflowScale
    norm_num
  · unfold quadraticOverflowScale
    norm_num

/-- In IEEE double finite-format range, the unscaled displayed overflow
example's `4*a*c` intermediate is a normal finite quantity. -/
theorem quadraticOverflowExample_four_ac_double_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
      (4 * quadraticOverflowScale * (2 * quadraticOverflowScale)) := by
  apply ieeeDoubleFormat_finiteNormalRange_of_one_le_abs_le_two_pow_137
  · unfold quadraticOverflowScale
    norm_num
  · unfold quadraticOverflowScale
    norm_num

/-- In IEEE double finite-format range, the unscaled displayed overflow
example's exact discriminant is a normal finite quantity. -/
theorem quadraticOverflowExample_discriminant_double_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
      (quadraticDiscriminant quadraticOverflowScale (-3 * quadraticOverflowScale)
        (2 * quadraticOverflowScale)) := by
  apply ieeeDoubleFormat_finiteNormalRange_of_one_le_abs_le_two_pow_137
  · unfold quadraticOverflowScale quadraticDiscriminant
    norm_num
  · unfold quadraticOverflowScale quadraticDiscriminant
    norm_num

/-- Bundle of the IEEE double finite-format range facts for the first displayed
§1.8 overflow example's unscaled discriminant path. -/
theorem quadraticOverflowExample_discriminant_path_double_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        ((-3 * quadraticOverflowScale) ^ 2) ∧
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (4 * quadraticOverflowScale * (2 * quadraticOverflowScale)) ∧
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (quadraticDiscriminant quadraticOverflowScale (-3 * quadraticOverflowScale)
          (2 * quadraticOverflowScale)) := by
  exact ⟨quadraticOverflowExample_b_square_double_finiteNormalRange,
    quadraticOverflowExample_four_ac_double_finiteNormalRange,
    quadraticOverflowExample_discriminant_double_finiteNormalRange⟩

/-- The actual IEEE-double finite round-to-even result of the displayed
example's `b*b` operation. -/
noncomputable def quadraticOverflowExample_b_square_doubleRounded : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp
    FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
    (-3 * quadraticOverflowScale) (-3 * quadraticOverflowScale)

/-- The actual IEEE-double finite round-to-even result of the displayed
example's `4*a` operation. -/
noncomputable def quadraticOverflowExample_four_a_doubleRounded : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp
    FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
    4 quadraticOverflowScale

/-- The actual IEEE-double finite round-to-even result of the displayed
example's rounded-intermediate `(fl(4*a))*c` operation. -/
noncomputable def quadraticOverflowExample_four_ac_doubleRounded : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp
    FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
    quadraticOverflowExample_four_a_doubleRounded (2 * quadraticOverflowScale)

/-- The actual IEEE-double finite round-to-even result of the displayed
example's rounded-intermediate discriminant subtraction. -/
noncomputable def quadraticOverflowExample_discriminant_doubleRounded : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp
    FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
    quadraticOverflowExample_b_square_doubleRounded
    quadraticOverflowExample_four_ac_doubleRounded

/-- Nearest/even double rounding of the displayed example's exact `b*b`
primitive is in the standard relative-error model.  This charges the exact
primitive result; it does not yet prove the whole rounded-intermediate
discriminant trace. -/
theorem quadraticOverflowExample_b_square_double_roundToEvenOp_standardModel :
    ∃ δ : ℝ,
      |δ| < FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        FloatingPointFormat.finiteRoundToEvenOp
            FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
            (-3 * quadraticOverflowScale) (-3 * quadraticOverflowScale) =
          ((-3 * quadraticOverflowScale) * (-3 * quadraticOverflowScale)) *
            (1 + δ) := by
  have hnorm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul (-3 * quadraticOverflowScale)
          (-3 * quadraticOverflowScale)) := by
    simpa [BasicOp.exact, pow_two] using
      quadraticOverflowExample_b_square_double_finiteNormalRange
  simpa [BasicOp.exact] using
    (FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := -3 * quadraticOverflowScale) (y := -3 * quadraticOverflowScale)
      hnorm)

/-- Nearest/even double rounding of the displayed example's exact `4*a`
primitive is in the standard relative-error model. -/
theorem quadraticOverflowExample_four_a_double_roundToEvenOp_standardModel :
    ∃ δ : ℝ,
      |δ| < FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        FloatingPointFormat.finiteRoundToEvenOp
            FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
            4 quadraticOverflowScale =
          (4 * quadraticOverflowScale) * (1 + δ) := by
  have hnorm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul 4 quadraticOverflowScale) := by
    simpa [BasicOp.exact] using
      quadraticOverflowExample_four_a_double_finiteNormalRange
  simpa [BasicOp.exact] using
    (FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := 4) (y := quadraticOverflowScale) hnorm)

/-- Nearest/even double rounding of the displayed example's exact `(4*a)*c`
primitive is in the standard relative-error model. -/
theorem quadraticOverflowExample_four_ac_double_roundToEvenOp_standardModel :
    ∃ δ : ℝ,
      |δ| < FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        FloatingPointFormat.finiteRoundToEvenOp
            FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
            (4 * quadraticOverflowScale) (2 * quadraticOverflowScale) =
          (4 * quadraticOverflowScale * (2 * quadraticOverflowScale)) *
            (1 + δ) := by
  have hnorm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul (4 * quadraticOverflowScale)
          (2 * quadraticOverflowScale)) := by
    simpa [BasicOp.exact] using
      quadraticOverflowExample_four_ac_double_finiteNormalRange
  simpa [BasicOp.exact] using
    (FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := 4 * quadraticOverflowScale)
      (y := 2 * quadraticOverflowScale) hnorm)

/-- Nearest/even double rounding of the displayed example's exact final
discriminant subtraction is in the standard relative-error model. -/
theorem quadraticOverflowExample_discriminant_sub_double_roundToEvenOp_standardModel :
    ∃ δ : ℝ,
      |δ| < FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        FloatingPointFormat.finiteRoundToEvenOp
            FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
            ((-3 * quadraticOverflowScale) ^ 2)
            (4 * quadraticOverflowScale * (2 * quadraticOverflowScale)) =
          (((-3 * quadraticOverflowScale) ^ 2) -
              (4 * quadraticOverflowScale * (2 * quadraticOverflowScale))) *
            (1 + δ) := by
  have hnorm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.sub ((-3 * quadraticOverflowScale) ^ 2)
          (4 * quadraticOverflowScale * (2 * quadraticOverflowScale))) := by
    simpa [BasicOp.exact, quadraticDiscriminant, pow_two, mul_assoc] using
      quadraticOverflowExample_discriminant_double_finiteNormalRange
  simpa [BasicOp.exact] using
    (FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := (-3 * quadraticOverflowScale) ^ 2)
      (y := 4 * quadraticOverflowScale * (2 * quadraticOverflowScale))
      hnorm)

/-- The IEEE nearest/even result for the displayed example's exact `b*b`
primitive has no exception flags in double finite-format range. -/
theorem quadraticOverflowExample_b_square_double_ieeeRoundToNearestEvenOpResult_noFlags :
    (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
      FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
      (-3 * quadraticOverflowScale) (-3 * quadraticOverflowScale)).noFlags := by
  have hnorm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul (-3 * quadraticOverflowScale)
          (-3 * quadraticOverflowScale)) := by
    simpa [BasicOp.exact, pow_two] using
      quadraticOverflowExample_b_square_double_finiteNormalRange
  exact
    FloatingPointFormat.ieeeRoundToNearestEvenOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := -3 * quadraticOverflowScale) (y := -3 * quadraticOverflowScale)
      (finiteNormalRange_not_finiteOverflowRange hnorm)
      (finiteNormalRange_not_finiteUnderflowRange hnorm)

/-- The IEEE nearest/even result for the displayed example's exact `4*a`
primitive has no exception flags in double finite-format range. -/
theorem quadraticOverflowExample_four_a_double_ieeeRoundToNearestEvenOpResult_noFlags :
    (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
      FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
      4 quadraticOverflowScale).noFlags := by
  have hnorm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul 4 quadraticOverflowScale) := by
    simpa [BasicOp.exact] using
      quadraticOverflowExample_four_a_double_finiteNormalRange
  exact
    FloatingPointFormat.ieeeRoundToNearestEvenOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := 4) (y := quadraticOverflowScale)
      (finiteNormalRange_not_finiteOverflowRange hnorm)
      (finiteNormalRange_not_finiteUnderflowRange hnorm)

/-- The IEEE nearest/even result for the displayed example's exact `(4*a)*c`
primitive has no exception flags in double finite-format range. -/
theorem quadraticOverflowExample_four_ac_double_ieeeRoundToNearestEvenOpResult_noFlags :
    (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
      FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
      (4 * quadraticOverflowScale) (2 * quadraticOverflowScale)).noFlags := by
  have hnorm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul (4 * quadraticOverflowScale)
          (2 * quadraticOverflowScale)) := by
    simpa [BasicOp.exact] using
      quadraticOverflowExample_four_ac_double_finiteNormalRange
  exact
    FloatingPointFormat.ieeeRoundToNearestEvenOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := 4 * quadraticOverflowScale)
      (y := 2 * quadraticOverflowScale)
      (finiteNormalRange_not_finiteOverflowRange hnorm)
      (finiteNormalRange_not_finiteUnderflowRange hnorm)

/-- The IEEE nearest/even result for the displayed example's exact final
discriminant subtraction has no exception flags in double finite-format range. -/
theorem quadraticOverflowExample_discriminant_sub_double_ieeeRoundToNearestEvenOpResult_noFlags :
    (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
      FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
      ((-3 * quadraticOverflowScale) ^ 2)
      (4 * quadraticOverflowScale * (2 * quadraticOverflowScale))).noFlags := by
  have hnorm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.sub ((-3 * quadraticOverflowScale) ^ 2)
          (4 * quadraticOverflowScale * (2 * quadraticOverflowScale))) := by
    simpa [BasicOp.exact, quadraticDiscriminant, pow_two, mul_assoc] using
      quadraticOverflowExample_discriminant_double_finiteNormalRange
  exact
    FloatingPointFormat.ieeeRoundToNearestEvenOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := (-3 * quadraticOverflowScale) ^ 2)
      (y := 4 * quadraticOverflowScale * (2 * quadraticOverflowScale))
      (finiteNormalRange_not_finiteOverflowRange hnorm)
      (finiteNormalRange_not_finiteUnderflowRange hnorm)

/-- Bundle of no-flag IEEE nearest/even facts for the displayed example's
exact double-precision primitive results.  The second multiplication is stated
with the exact `4*a` input; proving the fully rounded-intermediate trace remains
separate. -/
theorem quadraticOverflowExample_exact_discriminant_path_double_ieeeRoundToNearestEvenOpResult_noFlags :
    (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
        (-3 * quadraticOverflowScale) (-3 * quadraticOverflowScale)).noFlags ∧
      (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
        4 quadraticOverflowScale).noFlags ∧
      (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
        (4 * quadraticOverflowScale) (2 * quadraticOverflowScale)).noFlags ∧
      (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
        ((-3 * quadraticOverflowScale) ^ 2)
        (4 * quadraticOverflowScale * (2 * quadraticOverflowScale))).noFlags := by
  exact
    ⟨quadraticOverflowExample_b_square_double_ieeeRoundToNearestEvenOpResult_noFlags,
      quadraticOverflowExample_four_a_double_ieeeRoundToNearestEvenOpResult_noFlags,
      quadraticOverflowExample_four_ac_double_ieeeRoundToNearestEvenOpResult_noFlags,
      quadraticOverflowExample_discriminant_sub_double_ieeeRoundToNearestEvenOpResult_noFlags⟩

/-- The rounded-intermediate second product `fl(fl(4*a)*c)` for the displayed
§1.8 example remains in IEEE double normal finite range. -/
theorem quadraticOverflowExample_four_ac_doubleRounded_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
      (BasicOp.exact BasicOp.mul
        quadraticOverflowExample_four_a_doubleRounded
        (2 * quadraticOverflowScale)) := by
  rcases quadraticOverflowExample_four_a_double_roundToEvenOp_standardModel with
    ⟨δ4a, hδ4a, h4a⟩
  rw [BasicOp.exact, quadraticOverflowExample_four_a_doubleRounded, h4a]
  apply ieeeDoubleFormat_finiteNormalRange_of_one_le_abs_le_two_pow_137
  · have hδ' : |δ4a| < (1 / 8 : ℝ) :=
      lt_trans hδ4a ieeeDoubleFormat_unitRoundoff_lt_one_eighth
    have hbounds := one_add_delta_abs_bounds_of_abs_lt_one_eighth hδ'
    have hbase_pos : (0 : ℝ) ≤ 8 * quadraticOverflowScale ^ 2 := by
      unfold quadraticOverflowScale
      positivity
    have hrewrite :
        |((4 * quadraticOverflowScale) * (1 + δ4a)) *
          (2 * quadraticOverflowScale)| =
          8 * quadraticOverflowScale ^ 2 * |1 + δ4a| := by
      have hbase_abs :
          |8 * quadraticOverflowScale ^ 2| =
            8 * quadraticOverflowScale ^ 2 :=
        abs_of_nonneg hbase_pos
      rw [show ((4 * quadraticOverflowScale) * (1 + δ4a)) *
          (2 * quadraticOverflowScale) =
          (8 * quadraticOverflowScale ^ 2) * (1 + δ4a) by ring,
        abs_mul, hbase_abs]
    rw [hrewrite]
    calc
      (1 : ℝ) ≤ 7 * 10 ^ 40 := by norm_num
      _ = 8 * quadraticOverflowScale ^ 2 * (7 / 8 : ℝ) := by
          unfold quadraticOverflowScale
          norm_num
      _ ≤ 8 * quadraticOverflowScale ^ 2 * |1 + δ4a| :=
          mul_le_mul_of_nonneg_left hbounds.1 hbase_pos
  · have hδ' : |δ4a| < (1 / 8 : ℝ) :=
      lt_trans hδ4a ieeeDoubleFormat_unitRoundoff_lt_one_eighth
    have hbounds := one_add_delta_abs_bounds_of_abs_lt_one_eighth hδ'
    have hbase_pos : (0 : ℝ) ≤ 8 * quadraticOverflowScale ^ 2 := by
      unfold quadraticOverflowScale
      positivity
    have hrewrite :
        |((4 * quadraticOverflowScale) * (1 + δ4a)) *
          (2 * quadraticOverflowScale)| =
          8 * quadraticOverflowScale ^ 2 * |1 + δ4a| := by
      have hbase_abs :
          |8 * quadraticOverflowScale ^ 2| =
            8 * quadraticOverflowScale ^ 2 :=
        abs_of_nonneg hbase_pos
      rw [show ((4 * quadraticOverflowScale) * (1 + δ4a)) *
          (2 * quadraticOverflowScale) =
          (8 * quadraticOverflowScale ^ 2) * (1 + δ4a) by ring,
        abs_mul, hbase_abs]
    rw [hrewrite]
    calc
      8 * quadraticOverflowScale ^ 2 * |1 + δ4a| ≤
          8 * quadraticOverflowScale ^ 2 * (9 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hbounds.2 hbase_pos
      _ = 9 * 10 ^ 40 := by
          unfold quadraticOverflowScale
          norm_num
      _ ≤ (2 : ℝ) ^ (137 : ℕ) := by norm_num

/-- Nearest/even double rounding of the displayed example's rounded-input
second product `fl(4*a)*c` is in the standard relative-error model. -/
theorem quadraticOverflowExample_four_ac_doubleRounded_roundToEvenOp_standardModel :
    ∃ δ4a δ4ac : ℝ,
      |δ4a| < FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        |δ4ac| <
          FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        quadraticOverflowExample_four_a_doubleRounded =
          (4 * quadraticOverflowScale) * (1 + δ4a) ∧
        quadraticOverflowExample_four_ac_doubleRounded =
          (((4 * quadraticOverflowScale) * (1 + δ4a)) *
              (2 * quadraticOverflowScale)) * (1 + δ4ac) := by
  rcases quadraticOverflowExample_four_a_double_roundToEvenOp_standardModel with
    ⟨δ4a, hδ4a, h4a⟩
  have hnorm := quadraticOverflowExample_four_ac_doubleRounded_finiteNormalRange
  rcases
    (FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := quadraticOverflowExample_four_a_doubleRounded)
      (y := 2 * quadraticOverflowScale) hnorm) with
    ⟨δ4ac, hδ4ac, h4ac⟩
  refine ⟨δ4a, δ4ac, hδ4a, hδ4ac, ?_, ?_⟩
  · simpa [quadraticOverflowExample_four_a_doubleRounded] using h4a
  · rw [quadraticOverflowExample_four_ac_doubleRounded]
    calc
      FloatingPointFormat.finiteRoundToEvenOp
          FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
          quadraticOverflowExample_four_a_doubleRounded
          (2 * quadraticOverflowScale) =
          quadraticOverflowExample_four_a_doubleRounded *
            (2 * quadraticOverflowScale) * (1 + δ4ac) := by
            simpa [BasicOp.exact] using h4ac
      _ = (((4 * quadraticOverflowScale) * (1 + δ4a)) *
              (2 * quadraticOverflowScale)) * (1 + δ4ac) := by
            rw [quadraticOverflowExample_four_a_doubleRounded, h4a]

/-- The rounded-intermediate final subtraction
`fl(fl(b*b) - fl(fl(4*a)*c))` for the displayed §1.8 example remains in IEEE
double normal finite range before the final rounding is applied. -/
theorem quadraticOverflowExample_discriminant_sub_doubleRounded_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
      (BasicOp.exact BasicOp.sub
        quadraticOverflowExample_b_square_doubleRounded
        quadraticOverflowExample_four_ac_doubleRounded) := by
  rcases quadraticOverflowExample_b_square_double_roundToEvenOp_standardModel with
    ⟨δbb, hδbb, hbb⟩
  rcases quadraticOverflowExample_four_ac_doubleRounded_roundToEvenOp_standardModel with
    ⟨δ4a, δ4ac, hδ4a, hδ4ac, h4a, h4ac⟩
  rw [BasicOp.exact, quadraticOverflowExample_b_square_doubleRounded, hbb, h4ac]
  apply ieeeDoubleFormat_finiteNormalRange_of_one_le_abs_le_two_pow_137
  · have hδbb' : |δbb| < (1 / 1024 : ℝ) :=
      lt_trans hδbb ieeeDoubleFormat_unitRoundoff_lt_one_over_1024
    have hδ4a' : |δ4a| < (1 / 1024 : ℝ) :=
      lt_trans hδ4a ieeeDoubleFormat_unitRoundoff_lt_one_over_1024
    have hδ4ac' : |δ4ac| < (1 / 1024 : ℝ) :=
      lt_trans hδ4ac ieeeDoubleFormat_unitRoundoff_lt_one_over_1024
    have hbb_bounds :=
      one_add_delta_bounds_of_abs_lt_one_over_1024 hδbb'
    have h4a_bounds :=
      one_add_delta_bounds_of_abs_lt_one_over_1024 hδ4a'
    have h4ac_bounds :=
      one_add_delta_bounds_of_abs_lt_one_over_1024 hδ4ac'
    let T : ℝ := 9 * (1 + δbb) - 8 * ((1 + δ4a) * (1 + δ4ac))
    have h4a_nonneg : 0 ≤ 1 + δ4a := by nlinarith [h4a_bounds.1]
    have h4ac_nonneg : 0 ≤ 1 + δ4ac := by nlinarith [h4ac_bounds.1]
    have hprod_hi :
        (1 + δ4a) * (1 + δ4ac) ≤
          (1025 / 1024 : ℝ) * (1025 / 1024 : ℝ) :=
      mul_le_mul h4a_bounds.2 h4ac_bounds.2 h4ac_nonneg (by norm_num)
    have hT_lo : (1 / 2 : ℝ) ≤ T := by
      dsimp [T]
      nlinarith [hbb_bounds.1, hprod_hi]
    have hbase_pos : (0 : ℝ) ≤ quadraticOverflowScale ^ 2 := by
      positivity
    have hbaseT_nonneg : 0 ≤ quadraticOverflowScale ^ 2 * T :=
      mul_nonneg hbase_pos (by nlinarith [hT_lo])
    have hrewrite :
        ((-3 * quadraticOverflowScale) * (-3 * quadraticOverflowScale)) *
              (1 + δbb) -
            (((4 * quadraticOverflowScale) * (1 + δ4a)) *
              (2 * quadraticOverflowScale)) * (1 + δ4ac) =
          quadraticOverflowScale ^ 2 * T := by
      dsimp [T]
      ring
    rw [hrewrite, abs_of_nonneg hbaseT_nonneg]
    calc
      (1 : ℝ) ≤ quadraticOverflowScale ^ 2 * (1 / 2 : ℝ) := by
          unfold quadraticOverflowScale
          norm_num
      _ ≤ quadraticOverflowScale ^ 2 * T :=
          mul_le_mul_of_nonneg_left hT_lo hbase_pos
  · have hδbb' : |δbb| < (1 / 1024 : ℝ) :=
      lt_trans hδbb ieeeDoubleFormat_unitRoundoff_lt_one_over_1024
    have hδ4a' : |δ4a| < (1 / 1024 : ℝ) :=
      lt_trans hδ4a ieeeDoubleFormat_unitRoundoff_lt_one_over_1024
    have hδ4ac' : |δ4ac| < (1 / 1024 : ℝ) :=
      lt_trans hδ4ac ieeeDoubleFormat_unitRoundoff_lt_one_over_1024
    have hbb_bounds :=
      one_add_delta_bounds_of_abs_lt_one_over_1024 hδbb'
    have h4a_bounds :=
      one_add_delta_bounds_of_abs_lt_one_over_1024 hδ4a'
    have h4ac_bounds :=
      one_add_delta_bounds_of_abs_lt_one_over_1024 hδ4ac'
    let T : ℝ := 9 * (1 + δbb) - 8 * ((1 + δ4a) * (1 + δ4ac))
    have h4a_nonneg : 0 ≤ 1 + δ4a := by nlinarith [h4a_bounds.1]
    have hprod_lo :
        (1023 / 1024 : ℝ) * (1023 / 1024 : ℝ) ≤
          (1 + δ4a) * (1 + δ4ac) :=
      mul_le_mul h4a_bounds.1 h4ac_bounds.1 (by norm_num) h4a_nonneg
    have hT_hi : T ≤ (2 : ℝ) := by
      dsimp [T]
      nlinarith [hbb_bounds.2, hprod_lo]
    have hT_lo : (1 / 2 : ℝ) ≤ T := by
      have h4ac_nonneg : 0 ≤ 1 + δ4ac := by nlinarith [h4ac_bounds.1]
      have hprod_hi :
          (1 + δ4a) * (1 + δ4ac) ≤
            (1025 / 1024 : ℝ) * (1025 / 1024 : ℝ) :=
        mul_le_mul h4a_bounds.2 h4ac_bounds.2 h4ac_nonneg (by norm_num)
      dsimp [T]
      nlinarith [hbb_bounds.1, hprod_hi]
    have hbase_pos : (0 : ℝ) ≤ quadraticOverflowScale ^ 2 := by
      positivity
    have hbaseT_nonneg : 0 ≤ quadraticOverflowScale ^ 2 * T :=
      mul_nonneg hbase_pos (by nlinarith [hT_lo])
    have hrewrite :
        ((-3 * quadraticOverflowScale) * (-3 * quadraticOverflowScale)) *
              (1 + δbb) -
            (((4 * quadraticOverflowScale) * (1 + δ4a)) *
              (2 * quadraticOverflowScale)) * (1 + δ4ac) =
          quadraticOverflowScale ^ 2 * T := by
      dsimp [T]
      ring
    rw [hrewrite, abs_of_nonneg hbaseT_nonneg]
    calc
      quadraticOverflowScale ^ 2 * T ≤
          quadraticOverflowScale ^ 2 * (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hT_hi hbase_pos
      _ = 2 * 10 ^ 40 := by
          unfold quadraticOverflowScale
          norm_num
      _ ≤ (2 : ℝ) ^ (137 : ℕ) := by norm_num

/-- Bundle of the IEEE double finite-format range facts for the actual
rounded-intermediate discriminant path in the displayed §1.8 overflow example. -/
theorem quadraticOverflowExample_discriminant_path_doubleRounded_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul (-3 * quadraticOverflowScale)
          (-3 * quadraticOverflowScale)) ∧
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul 4 quadraticOverflowScale) ∧
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul
          quadraticOverflowExample_four_a_doubleRounded
          (2 * quadraticOverflowScale)) ∧
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.sub
          quadraticOverflowExample_b_square_doubleRounded
          quadraticOverflowExample_four_ac_doubleRounded) := by
  exact
    ⟨by
      simpa [BasicOp.exact, pow_two] using
        quadraticOverflowExample_b_square_double_finiteNormalRange,
      by
        simpa [BasicOp.exact] using
          quadraticOverflowExample_four_a_double_finiteNormalRange,
      quadraticOverflowExample_four_ac_doubleRounded_finiteNormalRange,
      quadraticOverflowExample_discriminant_sub_doubleRounded_finiteNormalRange⟩

/-- Nearest/even double rounding of the displayed example's rounded-input
final subtraction is in the standard relative-error model. -/
theorem quadraticOverflowExample_discriminant_sub_doubleRounded_roundToEvenOp_standardModel :
    ∃ δbb δ4a δ4ac δsub : ℝ,
      |δbb| < FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        |δ4a| <
          FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        |δ4ac| <
          FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        |δsub| <
          FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        quadraticOverflowExample_b_square_doubleRounded =
          ((-3 * quadraticOverflowScale) * (-3 * quadraticOverflowScale)) *
            (1 + δbb) ∧
        quadraticOverflowExample_four_a_doubleRounded =
          (4 * quadraticOverflowScale) * (1 + δ4a) ∧
        quadraticOverflowExample_four_ac_doubleRounded =
          (((4 * quadraticOverflowScale) * (1 + δ4a)) *
              (2 * quadraticOverflowScale)) * (1 + δ4ac) ∧
        quadraticOverflowExample_discriminant_doubleRounded =
          ((((-3 * quadraticOverflowScale) * (-3 * quadraticOverflowScale)) *
              (1 + δbb)) -
            ((((4 * quadraticOverflowScale) * (1 + δ4a)) *
              (2 * quadraticOverflowScale)) * (1 + δ4ac))) *
            (1 + δsub) := by
  rcases quadraticOverflowExample_b_square_double_roundToEvenOp_standardModel with
    ⟨δbb, hδbb, hbb⟩
  rcases quadraticOverflowExample_four_ac_doubleRounded_roundToEvenOp_standardModel with
    ⟨δ4a, δ4ac, hδ4a, hδ4ac, h4a, h4ac⟩
  have hnorm := quadraticOverflowExample_discriminant_sub_doubleRounded_finiteNormalRange
  rcases
    (FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := quadraticOverflowExample_b_square_doubleRounded)
      (y := quadraticOverflowExample_four_ac_doubleRounded) hnorm) with
    ⟨δsub, hδsub, hsub⟩
  refine ⟨δbb, δ4a, δ4ac, δsub, hδbb, hδ4a, hδ4ac, hδsub,
    ?_, h4a, h4ac, ?_⟩
  · simpa [quadraticOverflowExample_b_square_doubleRounded] using hbb
  · rw [quadraticOverflowExample_discriminant_doubleRounded]
    calc
      FloatingPointFormat.finiteRoundToEvenOp
          FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
          quadraticOverflowExample_b_square_doubleRounded
          quadraticOverflowExample_four_ac_doubleRounded =
          (quadraticOverflowExample_b_square_doubleRounded -
            quadraticOverflowExample_four_ac_doubleRounded) * (1 + δsub) := by
            simpa [BasicOp.exact] using hsub
      _ = ((((-3 * quadraticOverflowScale) * (-3 * quadraticOverflowScale)) *
              (1 + δbb)) -
            ((((4 * quadraticOverflowScale) * (1 + δ4a)) *
              (2 * quadraticOverflowScale)) * (1 + δ4ac))) *
            (1 + δsub) := by
            rw [quadraticOverflowExample_b_square_doubleRounded, hbb, h4ac]

/-- Fully rounded-intermediate nearest/even double trace for the displayed
§1.8 discriminant path.  This is the operational counterpart of
`fl(fl(b*b) - fl(fl(4*a)*c))` for the concrete overflow example. -/
theorem quadraticOverflowExample_discriminant_path_doubleRounded_roundToEvenOp_standardModel :
    ∃ δbb δ4a δ4ac δsub : ℝ,
      |δbb| < FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        |δ4a| <
          FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        |δ4ac| <
          FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        |δsub| <
          FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat ∧
        quadraticOverflowExample_b_square_doubleRounded =
          ((-3 * quadraticOverflowScale) * (-3 * quadraticOverflowScale)) *
            (1 + δbb) ∧
        quadraticOverflowExample_four_a_doubleRounded =
          (4 * quadraticOverflowScale) * (1 + δ4a) ∧
        quadraticOverflowExample_four_ac_doubleRounded =
          (((4 * quadraticOverflowScale) * (1 + δ4a)) *
              (2 * quadraticOverflowScale)) * (1 + δ4ac) ∧
        quadraticOverflowExample_discriminant_doubleRounded =
          ((((-3 * quadraticOverflowScale) * (-3 * quadraticOverflowScale)) *
              (1 + δbb)) -
            ((((4 * quadraticOverflowScale) * (1 + δ4a)) *
              (2 * quadraticOverflowScale)) * (1 + δ4ac))) *
            (1 + δsub) :=
  quadraticOverflowExample_discriminant_sub_doubleRounded_roundToEvenOp_standardModel

/-- The IEEE nearest/even result for the displayed example's rounded-input
second product has no exception flags in double finite-format range. -/
theorem quadraticOverflowExample_four_ac_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags :
    (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
      FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
      quadraticOverflowExample_four_a_doubleRounded
      (2 * quadraticOverflowScale)).noFlags := by
  have hnorm := quadraticOverflowExample_four_ac_doubleRounded_finiteNormalRange
  exact
    FloatingPointFormat.ieeeRoundToNearestEvenOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := quadraticOverflowExample_four_a_doubleRounded)
      (y := 2 * quadraticOverflowScale)
      (finiteNormalRange_not_finiteOverflowRange hnorm)
      (finiteNormalRange_not_finiteUnderflowRange hnorm)

/-- The IEEE nearest/even result for the displayed example's rounded-input
final discriminant subtraction has no exception flags in double finite-format
range. -/
theorem quadraticOverflowExample_discriminant_sub_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags :
    (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
      FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
      quadraticOverflowExample_b_square_doubleRounded
      quadraticOverflowExample_four_ac_doubleRounded).noFlags := by
  have hnorm :=
    quadraticOverflowExample_discriminant_sub_doubleRounded_finiteNormalRange
  exact
    FloatingPointFormat.ieeeRoundToNearestEvenOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := quadraticOverflowExample_b_square_doubleRounded)
      (y := quadraticOverflowExample_four_ac_doubleRounded)
      (finiteNormalRange_not_finiteOverflowRange hnorm)
      (finiteNormalRange_not_finiteUnderflowRange hnorm)

/-- Bundle of no-flag IEEE nearest/even facts for the displayed example's
actual rounded-intermediate double-precision discriminant path. -/
theorem quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags :
    (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
        (-3 * quadraticOverflowScale) (-3 * quadraticOverflowScale)).noFlags ∧
      (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
        4 quadraticOverflowScale).noFlags ∧
      (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
        quadraticOverflowExample_four_a_doubleRounded
        (2 * quadraticOverflowScale)).noFlags ∧
      (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
        quadraticOverflowExample_b_square_doubleRounded
        quadraticOverflowExample_four_ac_doubleRounded).noFlags := by
  exact
    ⟨quadraticOverflowExample_b_square_double_ieeeRoundToNearestEvenOpResult_noFlags,
      quadraticOverflowExample_four_a_double_ieeeRoundToNearestEvenOpResult_noFlags,
      quadraticOverflowExample_four_ac_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags,
      quadraticOverflowExample_discriminant_sub_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags⟩

/-- The value fields of the IEEE nearest/even no-flag operations agree with
the named finite round-to-even rounded-intermediate trace values. -/
theorem quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_toReal :
    (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
        (-3 * quadraticOverflowScale) (-3 * quadraticOverflowScale)).value.toReal? =
        some quadraticOverflowExample_b_square_doubleRounded ∧
      (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
        4 quadraticOverflowScale).value.toReal? =
        some quadraticOverflowExample_four_a_doubleRounded ∧
      (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
        quadraticOverflowExample_four_a_doubleRounded
        (2 * quadraticOverflowScale)).value.toReal? =
        some quadraticOverflowExample_four_ac_doubleRounded ∧
      (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
        FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
        quadraticOverflowExample_b_square_doubleRounded
        quadraticOverflowExample_four_ac_doubleRounded).value.toReal? =
        some quadraticOverflowExample_discriminant_doubleRounded := by
  have hb_norm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul (-3 * quadraticOverflowScale)
          (-3 * quadraticOverflowScale)) := by
    simpa [BasicOp.exact, pow_two] using
      quadraticOverflowExample_b_square_double_finiteNormalRange
  have h4a_norm :
      FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
        (BasicOp.exact BasicOp.mul 4 quadraticOverflowScale) := by
    simpa [BasicOp.exact] using
      quadraticOverflowExample_four_a_double_finiteNormalRange
  have h4ac_norm := quadraticOverflowExample_four_ac_doubleRounded_finiteNormalRange
  have hsub_norm :=
    quadraticOverflowExample_discriminant_sub_doubleRounded_finiteNormalRange
  exact
    ⟨by
      simpa [quadraticOverflowExample_b_square_doubleRounded] using
        (FloatingPointFormat.ieeeRoundToNearestEvenOpResult_toReal?_of_not_finiteOverflowRange
          (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
          (x := -3 * quadraticOverflowScale) (y := -3 * quadraticOverflowScale)
          (finiteNormalRange_not_finiteOverflowRange hb_norm)),
      by
        simpa [quadraticOverflowExample_four_a_doubleRounded] using
          (FloatingPointFormat.ieeeRoundToNearestEvenOpResult_toReal?_of_not_finiteOverflowRange
            (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
            (x := 4) (y := quadraticOverflowScale)
            (finiteNormalRange_not_finiteOverflowRange h4a_norm)),
      by
        simpa [quadraticOverflowExample_four_ac_doubleRounded] using
          (FloatingPointFormat.ieeeRoundToNearestEvenOpResult_toReal?_of_not_finiteOverflowRange
            (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
            (x := quadraticOverflowExample_four_a_doubleRounded)
            (y := 2 * quadraticOverflowScale)
            (finiteNormalRange_not_finiteOverflowRange h4ac_norm)),
      by
        simpa [quadraticOverflowExample_discriminant_doubleRounded] using
          (FloatingPointFormat.ieeeRoundToNearestEvenOpResult_toReal?_of_not_finiteOverflowRange
            (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
            (x := quadraticOverflowExample_b_square_doubleRounded)
            (y := quadraticOverflowExample_four_ac_doubleRounded)
            (finiteNormalRange_not_finiteOverflowRange hsub_norm))⟩

/-- Source-facing twice-precision trace for the displayed §1.8 overflow
example: the corresponding single-precision `b*b` primitive overflows the
finite range, while the double-precision rounded-intermediate discriminant
path has normal-range exact primitive results, no IEEE exception flags, and
value fields equal to the named finite round-to-even trace values. -/
theorem quadraticOverflowExample_singleOverflow_doubleRoundedDiscriminantTrace :
    FloatingPointFormat.finiteOverflowRange FloatingPointFormat.ieeeSingleFormat
        ((-3 * quadraticOverflowScale) ^ 2) ∧
      (FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
          (BasicOp.exact BasicOp.mul (-3 * quadraticOverflowScale)
            (-3 * quadraticOverflowScale)) ∧
        FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
          (BasicOp.exact BasicOp.mul 4 quadraticOverflowScale) ∧
        FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
          (BasicOp.exact BasicOp.mul
            quadraticOverflowExample_four_a_doubleRounded
            (2 * quadraticOverflowScale)) ∧
        FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeDoubleFormat
          (BasicOp.exact BasicOp.sub
            quadraticOverflowExample_b_square_doubleRounded
            quadraticOverflowExample_four_ac_doubleRounded)) ∧
      ((FloatingPointFormat.ieeeRoundToNearestEvenOpResult
          FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
          (-3 * quadraticOverflowScale) (-3 * quadraticOverflowScale)).noFlags ∧
        (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
          FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
          4 quadraticOverflowScale).noFlags ∧
        (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
          FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
          quadraticOverflowExample_four_a_doubleRounded
          (2 * quadraticOverflowScale)).noFlags ∧
        (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
          FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
          quadraticOverflowExample_b_square_doubleRounded
          quadraticOverflowExample_four_ac_doubleRounded).noFlags) ∧
      ((FloatingPointFormat.ieeeRoundToNearestEvenOpResult
          FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
          (-3 * quadraticOverflowScale) (-3 * quadraticOverflowScale)).value.toReal? =
          some quadraticOverflowExample_b_square_doubleRounded ∧
        (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
          FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
          4 quadraticOverflowScale).value.toReal? =
          some quadraticOverflowExample_four_a_doubleRounded ∧
        (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
          FloatingPointFormat.ieeeDoubleFormat BasicOp.mul
          quadraticOverflowExample_four_a_doubleRounded
          (2 * quadraticOverflowScale)).value.toReal? =
          some quadraticOverflowExample_four_ac_doubleRounded ∧
        (FloatingPointFormat.ieeeRoundToNearestEvenOpResult
          FloatingPointFormat.ieeeDoubleFormat BasicOp.sub
          quadraticOverflowExample_b_square_doubleRounded
          quadraticOverflowExample_four_ac_doubleRounded).value.toReal? =
          some quadraticOverflowExample_discriminant_doubleRounded) := by
  exact ⟨quadraticOverflowExample_b_square_single_finiteOverflowRange,
    quadraticOverflowExample_discriminant_path_doubleRounded_finiteNormalRange,
    quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags,
    quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_toReal⟩

/-- After dividing the first displayed overflow equation by `10^20`, the
`b*b` intermediate is an IEEE single normal-range value. -/
theorem quadraticOverflowExample_scaled_b_square_single_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeSingleFormat
      ((-3 : ℝ) ^ 2) := by
  apply FloatingPointFormat.normalizedSystem_finiteNormalRange
  refine ⟨false, 9437184, 4, ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.ieeeSingleFormat]
  · norm_num [FloatingPointFormat.exponentInRange,
      FloatingPointFormat.ieeeSingleFormat]
  · dsimp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
    norm_num [zpow_neg]

/-- After coefficient scaling, the `4*a*c` intermediate for `x^2 - 3*x + 2`
is an IEEE single normal-range value. -/
theorem quadraticOverflowExample_scaled_four_ac_single_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeSingleFormat
      (4 * (1 : ℝ) * 2) := by
  apply FloatingPointFormat.normalizedSystem_finiteNormalRange
  refine ⟨false, 8388608, 4, ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.ieeeSingleFormat]
  · norm_num [FloatingPointFormat.exponentInRange,
      FloatingPointFormat.ieeeSingleFormat]
  · dsimp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
    norm_num [zpow_neg]

/-- After coefficient scaling, the discriminant of `x^2 - 3*x + 2` is an IEEE
single normal-range value. -/
theorem quadraticOverflowExample_scaled_discriminant_single_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange FloatingPointFormat.ieeeSingleFormat
      (quadraticDiscriminant 1 (-3) 2) := by
  apply FloatingPointFormat.normalizedSystem_finiteNormalRange
  refine ⟨false, 8388608, 1, ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa, FloatingPointFormat.ieeeSingleFormat]
  · norm_num [FloatingPointFormat.exponentInRange,
      FloatingPointFormat.ieeeSingleFormat]
  · dsimp [quadraticDiscriminant, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.betaR]
    norm_num [zpow_neg]

/-- The displayed equation
`10^20*x^2 - 3*10^20*x + 2*10^20 = 0` has roots `1` and `2`. -/
theorem quadraticOverflowExample_roots :
    quadraticEval quadraticOverflowScale (-3 * quadraticOverflowScale)
        (2 * quadraticOverflowScale) 1 = 0 ∧
      quadraticEval quadraticOverflowScale (-3 * quadraticOverflowScale)
        (2 * quadraticOverflowScale) 2 = 0 := by
  constructor <;> unfold quadraticEval quadraticOverflowScale <;> norm_num

/-- The displayed equation
`10^-20*x^2 - 3*x + 2*10^20 = 0` has roots `10^20` and `2*10^20`. -/
theorem quadraticScaledOverflowExample_roots :
    quadraticEval (1 / quadraticOverflowScale) (-3)
        (2 * quadraticOverflowScale) quadraticOverflowScale = 0 ∧
      quadraticEval (1 / quadraticOverflowScale) (-3)
        (2 * quadraticOverflowScale) (2 * quadraticOverflowScale) = 0 := by
  constructor <;> unfold quadraticEval quadraticOverflowScale <;> norm_num

/-- The variable scaling `x = 10^20*y` transforms the second displayed
overflow example into the first equation in the variable `y`. -/
theorem quadraticScaledOverflowExample_variable_scaling (y : ℝ) :
    quadraticEval (1 / quadraticOverflowScale) (-3)
        (2 * quadraticOverflowScale) (quadraticOverflowScale * y) =
      quadraticEval quadraticOverflowScale (-3 * quadraticOverflowScale)
        (2 * quadraticOverflowScale) y := by
  unfold quadraticEval quadraticOverflowScale
  field_simp

/-- Real-square-root specialization of the `+` quadratic-formula root. -/
theorem quadraticRootPlus_real_sqrt_is_root (a b c : ℝ)
    (ha : a ≠ 0) (hdisc : 0 ≤ quadraticDiscriminant a b c) :
    quadraticEval a b c
        (quadraticRootPlus a b c (Real.sqrt (quadraticDiscriminant a b c))) = 0 :=
  quadraticRootPlus_is_root a b c _ ha (Real.sq_sqrt hdisc)

/-- Real-square-root specialization of the `-` quadratic-formula root. -/
theorem quadraticRootMinus_real_sqrt_is_root (a b c : ℝ)
    (ha : a ≠ 0) (hdisc : 0 ≤ quadraticDiscriminant a b c) :
    quadraticEval a b c
        (quadraticRootMinus a b c (Real.sqrt (quadraticDiscriminant a b c))) = 0 :=
  quadraticRootMinus_is_root a b c _ ha (Real.sq_sqrt hdisc)

end NumStability
