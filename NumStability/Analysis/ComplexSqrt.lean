-- Analysis/ComplexSqrt.lean
--
-- Exact stable complex square-root formulae for Higham Chapter 1, Problem 1.4.

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumStability

/-!
# Stable Complex Square-Root Formulae

Higham Problem 1.4 asks for stable formulae for computing a square root
`x + i*y` of `a + i*b`.  The standard cancellation-avoiding formula computes
the large component from a square root and the small component from the
relation `2*x*y = b`:

* if `0 <= a` and `a + i*b` is nonzero, use
  `x = sqrt((r+a)/2)` and `y = b/(2*x)`;
* if `a < 0`, use
  `y = sign(b)*sqrt((r-a)/2)` and `x = b/(2*y)`;
* for `a = b = 0`, use `x = y = 0`.

Here `r = sqrt(a^2+b^2)`.  The theorems below prove the exact algebraic
correctness of these formulae.  A floating-point theorem for the square-root
and division calls themselves is a separate machine-model obligation.
-/

/-- Magnitude `sqrt(a^2+b^2)` used by the stable complex square-root formula. -/
noncomputable def complexSqrtRadius (a b : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2)

/-- Sign choice for the imaginary part in the `a < 0` branch.  The zero case
chooses the principal positive imaginary square root. -/
noncomputable def complexSqrtImagSign (b : ℝ) : ℝ :=
  if b < 0 then -1 else 1

/-- Real part formula for the stable `0 <= a` branch. -/
noncomputable def complexSqrtStableXNonnegA (a b : ℝ) : ℝ :=
  Real.sqrt ((complexSqrtRadius a b + a) / 2)

/-- Imaginary part formula for the stable `0 <= a` branch, computed from
`2*x*y = b` to avoid cancellation when `y` is small. -/
noncomputable def complexSqrtStableYNonnegA (a b : ℝ) : ℝ :=
  b / (2 * complexSqrtStableXNonnegA a b)

/-- Imaginary part formula for the stable `a < 0` branch. -/
noncomputable def complexSqrtStableYNegA (a b : ℝ) : ℝ :=
  complexSqrtImagSign b * Real.sqrt ((complexSqrtRadius a b - a) / 2)

/-- Real part formula for the stable `a < 0` branch, computed from
`2*x*y = b` to avoid cancellation when `x` is small. -/
noncomputable def complexSqrtStableXNegA (a b : ℝ) : ℝ :=
  b / (2 * complexSqrtStableYNegA a b)

/-- Assemble `x + i*y` from real components. -/
noncomputable def complexFromRealImag (x y : ℝ) : ℂ :=
  (x : ℂ) + (y : ℂ) * Complex.I

theorem complexSqrtRadius_nonneg (a b : ℝ) :
    0 ≤ complexSqrtRadius a b := by
  exact Real.sqrt_nonneg _

theorem complexSqrtRadius_sq (a b : ℝ) :
    complexSqrtRadius a b ^ 2 = a ^ 2 + b ^ 2 := by
  unfold complexSqrtRadius
  exact Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))

theorem complexSqrtImagSign_sq (b : ℝ) :
    complexSqrtImagSign b ^ 2 = 1 := by
  unfold complexSqrtImagSign
  by_cases hb : b < 0 <;> simp [hb]

theorem complexSqrtImagSign_mul_abs (b : ℝ) :
    complexSqrtImagSign b * |b| = b := by
  unfold complexSqrtImagSign
  by_cases hb : b < 0
  · have hle : b ≤ 0 := le_of_lt hb
    simp [hb, abs_of_nonpos hle]
  · have hle : 0 ≤ b := le_of_not_gt hb
    simp [hb, abs_of_nonneg hle]

/-- If components satisfy the real and imaginary square equations, then
`x + i*y` is a complex square root of `a + i*b`. -/
theorem complexFromRealImag_sq_eq_of_components
    {a b x y : ℝ} (hre : x ^ 2 - y ^ 2 = a) (him : 2 * x * y = b) :
    complexFromRealImag x y ^ 2 = complexFromRealImag a b := by
  apply Complex.ext
  · simp [complexFromRealImag, pow_two, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  · simp [complexFromRealImag, pow_two, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    nlinarith

theorem complexSqrtStableXNonnegA_pos {a b : ℝ}
    (ha : 0 ≤ a) (hnz : a ≠ 0 ∨ b ≠ 0) :
    0 < complexSqrtStableXNonnegA a b := by
  unfold complexSqrtStableXNonnegA
  apply Real.sqrt_pos.2
  have hr_nonneg : 0 ≤ complexSqrtRadius a b := complexSqrtRadius_nonneg a b
  have hr_plus_a_pos : 0 < complexSqrtRadius a b + a := by
    by_cases ha0 : a = 0
    · have hbne : b ≠ 0 := by
        rcases hnz with ha_ne | hb_ne
        · exact (ha_ne ha0).elim
        · exact hb_ne
      have hr_eq_abs : complexSqrtRadius a b = |b| := by
        unfold complexSqrtRadius
        simp [ha0, Real.sqrt_sq_eq_abs]
      have hb_abs_pos : 0 < |b| := abs_pos.mpr hbne
      nlinarith
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      nlinarith
  nlinarith

theorem complexSqrtStableXNonnegA_ne_zero {a b : ℝ}
    (ha : 0 ≤ a) (hnz : a ≠ 0 ∨ b ≠ 0) :
    complexSqrtStableXNonnegA a b ≠ 0 :=
  ne_of_gt (complexSqrtStableXNonnegA_pos ha hnz)

/-- In the nonnegative-real-part branch, the stable formula satisfies the two
component equations for a complex square root. -/
theorem complexSqrtStable_nonnegA_components {a b : ℝ}
    (ha : 0 ≤ a) (hnz : a ≠ 0 ∨ b ≠ 0) :
    let x := complexSqrtStableXNonnegA a b
    let y := complexSqrtStableYNonnegA a b
    x ^ 2 - y ^ 2 = a ∧ 2 * x * y = b := by
  intro x y
  have hxne : x ≠ 0 := by
    exact complexSqrtStableXNonnegA_ne_zero ha hnz
  have hy_eq : y = b / (2 * x) := rfl
  have hx_sq : x ^ 2 = (complexSqrtRadius a b + a) / 2 := by
    subst x
    unfold complexSqrtStableXNonnegA
    apply Real.sq_sqrt
    have hr_nonneg := complexSqrtRadius_nonneg a b
    nlinarith [ha]
  have htwo_xy : 2 * x * y = b := by
    rw [hy_eq]
    field_simp [hxne]
  refine ⟨?_, htwo_xy⟩
  have hrad_sq : complexSqrtRadius a b ^ 2 = a ^ 2 + b ^ 2 :=
    complexSqrtRadius_sq a b
  have hx_sq_ne : x ^ 2 ≠ 0 := pow_ne_zero 2 hxne
  have hr_plus_a_ne : complexSqrtRadius a b + a ≠ 0 := by
    intro hzero
    have hx_zero : x ^ 2 = 0 := by
      simpa [hzero] using hx_sq
    exact hx_sq_ne hx_zero
  calc
    x ^ 2 - y ^ 2
        = x ^ 2 - b ^ 2 / (4 * x ^ 2) := by
          rw [hy_eq]
          field_simp [hxne]
          ring_nf
    _ = a := by
      rw [hx_sq]
      field_simp [hr_plus_a_ne]
      nlinarith

/-- Correctness of the stable square-root formula when `0 <= a` and the input
is nonzero. -/
theorem complexSqrtStable_nonnegA_sq {a b : ℝ}
    (ha : 0 ≤ a) (hnz : a ≠ 0 ∨ b ≠ 0) :
    complexFromRealImag
        (complexSqrtStableXNonnegA a b)
        (complexSqrtStableYNonnegA a b) ^ 2 =
      complexFromRealImag a b := by
  have hcomp := complexSqrtStable_nonnegA_components (a := a) (b := b) ha hnz
  exact complexFromRealImag_sq_eq_of_components hcomp.1 hcomp.2

theorem complexSqrtStableYNegA_ne_zero {a b : ℝ} (ha : a < 0) :
    complexSqrtStableYNegA a b ≠ 0 := by
  unfold complexSqrtStableYNegA
  apply mul_ne_zero
  · have hsq := complexSqrtImagSign_sq b
    intro hzero
    rw [hzero] at hsq
    norm_num at hsq
  · apply ne_of_gt
    apply Real.sqrt_pos.2
    have hr_nonneg := complexSqrtRadius_nonneg a b
    nlinarith

/-- In the negative-real-part branch, the stable formula satisfies the two
component equations for a complex square root. -/
theorem complexSqrtStable_negA_components {a b : ℝ} (ha : a < 0) :
    let x := complexSqrtStableXNegA a b
    let y := complexSqrtStableYNegA a b
    x ^ 2 - y ^ 2 = a ∧ 2 * x * y = b := by
  intro x y
  have hyne : y ≠ 0 := by
    exact complexSqrtStableYNegA_ne_zero ha
  have hx_eq : x = b / (2 * y) := rfl
  have hsign_sq : complexSqrtImagSign b ^ 2 = 1 :=
    complexSqrtImagSign_sq b
  have hy_sq : y ^ 2 = (complexSqrtRadius a b - a) / 2 := by
    subst y
    unfold complexSqrtStableYNegA
    rw [mul_pow, hsign_sq, one_mul]
    apply Real.sq_sqrt
    have hr_nonneg := complexSqrtRadius_nonneg a b
    nlinarith
  have htwo_xy : 2 * x * y = b := by
    rw [hx_eq]
    field_simp [hyne]
  refine ⟨?_, htwo_xy⟩
  have hrad_sq : complexSqrtRadius a b ^ 2 = a ^ 2 + b ^ 2 :=
    complexSqrtRadius_sq a b
  have hy_sq_ne : y ^ 2 ≠ 0 := pow_ne_zero 2 hyne
  have hr_minus_a_ne : complexSqrtRadius a b - a ≠ 0 := by
    intro hzero
    have hy_zero : y ^ 2 = 0 := by
      simpa [hzero] using hy_sq
    exact hy_sq_ne hy_zero
  calc
    x ^ 2 - y ^ 2
        = b ^ 2 / (4 * y ^ 2) - y ^ 2 := by
          rw [hx_eq]
          field_simp [hyne]
          ring_nf
    _ = a := by
      rw [hy_sq]
      field_simp [hr_minus_a_ne]
      nlinarith

/-- Correctness of the stable square-root formula when `a < 0`. -/
theorem complexSqrtStable_negA_sq {a b : ℝ} (ha : a < 0) :
    complexFromRealImag
        (complexSqrtStableXNegA a b)
        (complexSqrtStableYNegA a b) ^ 2 =
      complexFromRealImag a b := by
  have hcomp := complexSqrtStable_negA_components (a := a) (b := b) ha
  exact complexFromRealImag_sq_eq_of_components hcomp.1 hcomp.2

/-- The zero-input special case of the stable complex square-root formula. -/
theorem complexSqrtStable_zero_sq :
    complexFromRealImag 0 0 ^ 2 = complexFromRealImag 0 0 := by
  simp [complexFromRealImag]

end NumStability
