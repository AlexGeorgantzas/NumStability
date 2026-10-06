/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter27.SoftwareEnvironment

namespace NumStability

/-! # Higham Chapter 27, Problem 27.6: the Moler--Morrison `pythag` iteration

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 27, Problem 27.6, printed pp. 507--509.  This file formalizes the exact
algebra delegated to the Problem by the body discussion on p. 500: the Halley
specialization, the scaled two-variable recurrence, preservation of the
Pythagorean sum, monotone enclosure, and the exact cubic error identity.

The source's machine-dependent claim that the MATLAB stopping test fires in at
most three iterations is deliberately not hidden in these real-arithmetic
theorems: that claim depends on the concrete format and evaluation semantics of
`r + 4 == 4`.
-/

/-- The Halley update for the positive root of `x^2 - p^2 = 0`, in the form
printed in Higham Problem 27.6(a). -/
noncomputable def higham27PythagHalleyStep (p x : Real) : Real :=
  x * (1 + 2 * (p ^ 2 - x ^ 2) / (p ^ 2 + 3 * x ^ 2))

/-- The first component of the exact scaled `pythag` recurrence. -/
noncomputable def higham27PythagXStep (x y : Real) : Real :=
  x * (1 + 2 * y ^ 2 / (4 * x ^ 2 + y ^ 2))

/-- The second component of the exact scaled `pythag` recurrence. -/
noncomputable def higham27PythagYStep (x y : Real) : Real :=
  y ^ 3 / (4 * x ^ 2 + y ^ 2)

/-- Problem 27.6(a): substituting `f(x)=x^2-p^2`, `f'(x)=2x`, and
`f''(x)=2` in Halley's method gives the printed update.  The left side is the
standard simplified Halley quotient `x - f f'/(f'^2-f f''/2)`. -/
theorem higham27_problem27_6_halley_specialization
    (p x : Real) (hden : p ^ 2 + 3 * x ^ 2 ≠ 0) :
    x - ((x ^ 2 - p ^ 2) * (2 * x)) /
          ((2 * x) ^ 2 - (x ^ 2 - p ^ 2)) =
      higham27PythagHalleyStep p x := by
  unfold higham27PythagHalleyStep
  have hden' : (2 * x) ^ 2 - (x ^ 2 - p ^ 2) ≠ 0 := by
    rw [show (2 * x) ^ 2 - (x ^ 2 - p ^ 2) =
      p ^ 2 + 3 * x ^ 2 by ring]
    exact hden
  rw [show (2 * x) ^ 2 - (x ^ 2 - p ^ 2) =
    p ^ 2 + 3 * x ^ 2 by ring]
  field_simp [hden, hden']
  ring

/-- The pair recurrence is exactly the Halley update whenever
`p^2 = x^2+y^2`. -/
theorem higham27_problem27_6_pair_step_eq_halley
    (p x y : Real) (hsq : p ^ 2 = x ^ 2 + y ^ 2)
    (hden : 4 * x ^ 2 + y ^ 2 ≠ 0) :
    higham27PythagXStep x y = higham27PythagHalleyStep p x := by
  unfold higham27PythagXStep higham27PythagHalleyStep
  have hden' : p ^ 2 + 3 * x ^ 2 ≠ 0 := by
    intro hz
    apply hden
    nlinarith
  rw [hsq]
  rw [show x ^ 2 + y ^ 2 + 3 * x ^ 2 =
    4 * x ^ 2 + y ^ 2 by ring]
  ring_nf

/-- Problem 27.6(a): the exact two-variable recurrence preserves the squared
Pythagorean sum.  Consequently the second component remains the square-root
residual associated with the first component whenever it was so initially. -/
theorem higham27_problem27_6_pair_step_invariant
    (x y : Real) (hden : 4 * x ^ 2 + y ^ 2 ≠ 0) :
    higham27PythagXStep x y ^ 2 + higham27PythagYStep x y ^ 2 =
      x ^ 2 + y ^ 2 := by
  have hxstep : higham27PythagXStep x y =
      x * (4 * x ^ 2 + 3 * y ^ 2) / (4 * x ^ 2 + y ^ 2) := by
    unfold higham27PythagXStep
    have hfrac :
        1 + 2 * y ^ 2 / (4 * x ^ 2 + y ^ 2) =
          ((4 * x ^ 2 + y ^ 2) + 2 * y ^ 2) /
            (4 * x ^ 2 + y ^ 2) := by
      calc
        1 + 2 * y ^ 2 / (4 * x ^ 2 + y ^ 2) =
            (4 * x ^ 2 + y ^ 2) / (4 * x ^ 2 + y ^ 2) +
              2 * y ^ 2 / (4 * x ^ 2 + y ^ 2) := by rw [div_self hden]
        _ = ((4 * x ^ 2 + y ^ 2) + 2 * y ^ 2) /
              (4 * x ^ 2 + y ^ 2) := (add_div _ _ _).symm
    rw [hfrac]
    ring
  rw [hxstep]
  unfold higham27PythagYStep
  rw [div_pow, div_pow, ← add_div]
  apply (div_eq_iff (pow_ne_zero 2 hden)).2
  ring

/-- The MATLAB variables `r=(q/p)^2`, `s=r/(4+r)`,
`p <- p+2*s*p`, `q <- s*q` implement the displayed scaled recurrence. -/
theorem higham27_problem27_6_matlab_scaled_step
    (x y : Real) (hx : x ≠ 0) :
    let r := (y / x) ^ 2
    let s := r / (4 + r)
    (x + 2 * s * x, s * y) =
      (higham27PythagXStep x y, higham27PythagYStep x y) := by
  dsimp
  have hspos : 0 < 4 + (y / x) ^ 2 := by positivity
  have hsne : 4 + (y / x) ^ 2 ≠ 0 := ne_of_gt hspos
  have hden : 4 * x ^ 2 + y ^ 2 ≠ 0 := by
    have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    nlinarith [sq_nonneg y]
  apply Prod.ext
  · unfold higham27PythagXStep
    field_simp [hx, hsne, hden]
  · unfold higham27PythagYStep
    field_simp [hx, hsne, hden]

/-- Problem 27.6(b): one Halley step cubes the error exactly. -/
theorem higham27_problem27_6_cubic_error_identity
    (p x : Real) (hden : p ^ 2 + 3 * x ^ 2 ≠ 0) :
    p - higham27PythagHalleyStep p x =
      (p - x) ^ 3 / (p ^ 2 + 3 * x ^ 2) := by
  have hstep : higham27PythagHalleyStep p x =
      x * (3 * p ^ 2 + x ^ 2) / (p ^ 2 + 3 * x ^ 2) := by
    unfold higham27PythagHalleyStep
    have hfrac :
        1 + 2 * (p ^ 2 - x ^ 2) / (p ^ 2 + 3 * x ^ 2) =
          ((p ^ 2 + 3 * x ^ 2) + 2 * (p ^ 2 - x ^ 2)) /
            (p ^ 2 + 3 * x ^ 2) := by
      calc
        1 + 2 * (p ^ 2 - x ^ 2) / (p ^ 2 + 3 * x ^ 2) =
            (p ^ 2 + 3 * x ^ 2) / (p ^ 2 + 3 * x ^ 2) +
              2 * (p ^ 2 - x ^ 2) / (p ^ 2 + 3 * x ^ 2) := by
                rw [div_self hden]
        _ = ((p ^ 2 + 3 * x ^ 2) + 2 * (p ^ 2 - x ^ 2)) /
              (p ^ 2 + 3 * x ^ 2) := (add_div _ _ _).symm
    rw [hfrac]
    ring
  rw [hstep]
  calc
    p - x * (3 * p ^ 2 + x ^ 2) / (p ^ 2 + 3 * x ^ 2) =
        p * (p ^ 2 + 3 * x ^ 2) / (p ^ 2 + 3 * x ^ 2) -
          x * (3 * p ^ 2 + x ^ 2) / (p ^ 2 + 3 * x ^ 2) := by
            rw [mul_div_cancel_right₀ p hden]
    _ = (p * (p ^ 2 + 3 * x ^ 2) - x * (3 * p ^ 2 + x ^ 2)) /
          (p ^ 2 + 3 * x ^ 2) := (sub_div _ _ _).symm
    _ = (p - x) ^ 3 / (p ^ 2 + 3 * x ^ 2) := by
      congr 1
      ring

/-- Problem 27.6(a): below the positive root, the Halley iterates are
monotone and remain below that root. -/
theorem higham27_problem27_6_monotone_enclosure
    (p x : Real) (hp : 0 < p) (hx0 : 0 <= x) (hxp : x <= p) :
    x <= higham27PythagHalleyStep p x ∧
      higham27PythagHalleyStep p x <= p := by
  have hdenpos : 0 < p ^ 2 + 3 * x ^ 2 := by
    nlinarith [sq_pos_of_pos hp, sq_nonneg x]
  have hden : p ^ 2 + 3 * x ^ 2 ≠ 0 := ne_of_gt hdenpos
  constructor
  · have hsq : 0 <= p ^ 2 - x ^ 2 := by nlinarith
    have hdiff :
        higham27PythagHalleyStep p x - x =
          2 * x * (p ^ 2 - x ^ 2) / (p ^ 2 + 3 * x ^ 2) := by
      unfold higham27PythagHalleyStep
      field_simp [hden]
      ring
    rw [← sub_nonneg, hdiff]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx0) hsq)
      (le_of_lt hdenpos)
  · rw [← sub_nonneg]
    rw [higham27_problem27_6_cubic_error_identity p x hden]
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hxp) 3) (le_of_lt hdenpos)

/-- Quantitative cubic contraction: while `0 <= x <= p`, the next absolute
error is at most the cube of the current error divided by `p^2`. -/
theorem higham27_problem27_6_cubic_error_bound
    (p x : Real) (hp : 0 < p) (_hx0 : 0 <= x) (hxp : x <= p) :
    0 <= p - higham27PythagHalleyStep p x ∧
      p - higham27PythagHalleyStep p x <= (p - x) ^ 3 / p ^ 2 := by
  have hdenpos : 0 < p ^ 2 + 3 * x ^ 2 := by
    nlinarith [sq_pos_of_pos hp, sq_nonneg x]
  have hp2pos : 0 < p ^ 2 := sq_pos_of_pos hp
  have hnum : 0 <= (p - x) ^ 3 := pow_nonneg (sub_nonneg.mpr hxp) 3
  have hid := higham27_problem27_6_cubic_error_identity p x (ne_of_gt hdenpos)
  rw [hid]
  constructor
  · exact div_nonneg hnum (le_of_lt hdenpos)
  · exact div_le_div_of_nonneg_left hnum hp2pos
      (by nlinarith [sq_nonneg x])

end NumStability
