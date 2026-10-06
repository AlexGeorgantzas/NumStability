-- Analysis/Problem2_23.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.23.

import Mathlib.Algebra.Group.Nat.Even
import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2, Problem 2.23

Problem 2.23 asks what happens to `y = (x + x) - x` on a binary machine with
and without a guard digit.  This file records:

* the exact finite/guard-digit path, where the rounded operation sequence
  returns `x` when the doubling and final exact result stay in the finite
  system;
* the no-guard error-parameter formula from the Chapter 2 model;
* the binary mantissa description of the digit dropped by a no-guard
  same-sign subtraction after aligning `x` under `2*x`.
-/

/-- The ordinary finite round-to-even operation sequence for
`y = (x + x) - x`. -/
def problem2_23_guardDigitY (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.sub
    (fmt.finiteRoundToEvenOp BasicOp.add x x) x

/-- Guard-digit/exact finite path for Problem 2.23: if `x` and `x+x` stay in
the finite system, then `(x+x)-x` returns `x`. -/
theorem problem2_23_guardDigitY_eq_x_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x)
    (hxx : fmt.finiteSystem (x + x)) :
    problem2_23_guardDigitY fmt x = x := by
  have hadd :
      fmt.finiteRoundToEvenOp BasicOp.add x x = x + x := by
    simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.add) (x := x) (y := x) hxx)
  have hsub_fin : fmt.finiteSystem ((x + x) - x) := by
    convert hx using 1
    ring
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub (x + x) x = (x + x) - x := by
    simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := x + x) (y := x) hsub_fin)
  unfold problem2_23_guardDigitY
  rw [hadd, hsub]
  ring

/-- The no-guard operation sequence for `y = (x+x)-x`. -/
def problem2_23_noGuardY (fp : NoGuardFPModel) (x : ℝ) : ℝ :=
  fp.fl_sub (fp.fl_add x x) x

/-- In the abstract no-guard model, Problem 2.23 exposes all four additive
input perturbations from the two rounded operations. -/
theorem problem2_23_noGuardY_error_formula
    (fp : NoGuardFPModel) (x : ℝ) :
    ∃ α β γ η : ℝ,
      |α| ≤ fp.u ∧ |β| ≤ fp.u ∧ |γ| ≤ fp.u ∧ |η| ≤ fp.u ∧
        problem2_23_noGuardY fp x - x =
          x * (α + β + 2 * γ + α * γ + β * γ - η) := by
  rcases fp.model_add x x with ⟨α, β, hadd⟩
  rcases fp.model_sub (fp.fl_add x x) x with ⟨γ, η, hsub⟩
  refine
    ⟨α, β, γ, η, hadd.1, hadd.2.1, hsub.1, hsub.2.1, ?_⟩
  have hadd_value := noGuardAddWitness_value hadd
  have hsub_value := noGuardSubWitness_value hsub
  unfold problem2_23_noGuardY
  rw [hsub_value, hadd_value]
  ring

/-- Mantissa-level no-guard binary description.  After aligning `x` beneath
`2*x` and dropping the guard bit, the retained subtraction has scaled mantissa
`2 * (m - floor(m/2))`. -/
def problem2_23_binaryNoGuardScaledMantissa (m : ℕ) : ℕ :=
  2 * (m - m / 2)

/-- The no-guard binary mantissa result is the original mantissa plus the
dropped low bit. -/
theorem problem2_23_binaryNoGuardScaledMantissa_eq_add_mod_two
    (m : ℕ) :
    problem2_23_binaryNoGuardScaledMantissa m = m + m % 2 := by
  unfold problem2_23_binaryNoGuardScaledMantissa
  grind [Nat.mod_add_div]

/-- If the low mantissa bit is zero, the no-guard binary sequence still returns
the original scaled mantissa. -/
theorem problem2_23_binaryNoGuardScaledMantissa_eq_self_of_even
    {m : ℕ} (hm : m % 2 = 0) :
    problem2_23_binaryNoGuardScaledMantissa m = m := by
  rw [problem2_23_binaryNoGuardScaledMantissa_eq_add_mod_two, hm, Nat.add_zero]

/-- If the low mantissa bit is one, the no-guard binary sequence rounds the
scaled mantissa up by one lattice step. -/
theorem problem2_23_binaryNoGuardScaledMantissa_eq_succ_of_odd
    {m : ℕ} (hm : m % 2 = 1) :
    problem2_23_binaryNoGuardScaledMantissa m = m + 1 := by
  rw [problem2_23_binaryNoGuardScaledMantissa_eq_add_mod_two, hm]

/-- Interpret a scaled integer mantissa as a real value. -/
def problem2_23_binaryScaledValue (m : ℕ) (scale : ℝ) : ℝ :=
  (m : ℝ) * scale

/-- Real-valued no-guard result obtained from the scaled mantissa theorem. -/
def problem2_23_binaryNoGuardYScaled (m : ℕ) (scale : ℝ) : ℝ :=
  (problem2_23_binaryNoGuardScaledMantissa m : ℝ) * scale

/-- Real no-guard error: the result differs from `x` by exactly the dropped
low bit times the lattice scale. -/
theorem problem2_23_binaryNoGuardYScaled_error_eq_low_bit
    (m : ℕ) (scale : ℝ) :
    problem2_23_binaryNoGuardYScaled m scale -
        problem2_23_binaryScaledValue m scale =
      ((m % 2 : ℕ) : ℝ) * scale := by
  unfold problem2_23_binaryNoGuardYScaled problem2_23_binaryScaledValue
  rw [problem2_23_binaryNoGuardScaledMantissa_eq_add_mod_two]
  norm_num
  ring_nf

theorem problem2_23_binaryNoGuardYScaled_eq_scaledValue_add_low_bit
    (m : ℕ) (scale : ℝ) :
    problem2_23_binaryNoGuardYScaled m scale =
      problem2_23_binaryScaledValue m scale + ((m % 2 : ℕ) : ℝ) * scale := by
  have h := problem2_23_binaryNoGuardYScaled_error_eq_low_bit m scale
  linarith

theorem problem2_23_guard_and_binary_noGuard_summary :
    (∀ (fmt : FloatingPointFormat) (x : ℝ),
        fmt.finiteSystem x → fmt.finiteSystem (x + x) →
          problem2_23_guardDigitY fmt x = x) ∧
      (∀ (m : ℕ) (scale : ℝ),
        problem2_23_binaryNoGuardYScaled m scale =
          problem2_23_binaryScaledValue m scale +
            ((m % 2 : ℕ) : ℝ) * scale) := by
  constructor
  · intro fmt x hx hxx
    exact problem2_23_guardDigitY_eq_x_of_finiteSystem hx hxx
  · intro m scale
    exact problem2_23_binaryNoGuardYScaled_eq_scaledValue_add_low_bit m scale

end

end NumStability
