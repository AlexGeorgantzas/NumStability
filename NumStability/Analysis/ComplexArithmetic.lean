-- Analysis/ComplexArithmetic.lean
--
-- Rounded complex scalar arithmetic from Higham Chapter 3, Lemma 3.5.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding

namespace NumStability

open scoped BigOperators

/-!
# Rounded Complex Arithmetic

Higham Chapter 3, Section 3.6 derives complex-arithmetic error models from
real floating-point arithmetic.  This file formalizes the ordinary rounded
add/sub/mul/div cases from Lemma 3.5 and the exact Smith branch formulas used
by the overflow-avoiding division note that points to Chapter 25.
-/

/-- Complex relative-error model: the computed complex scalar is the exact
complex scalar times `1 + delta`, with `delta` bounded in complex norm. -/
def complexRelErrorModel (computed exact : ℂ) (u : ℝ) : Prop :=
  ∃ delta : ℂ, ‖delta‖ ≤ u ∧ computed = exact * (1 + delta)

/-- Package a complex normwise absolute-error bound into the source relative
error form.  The zero exact-value case follows from the bound itself. -/
theorem complexRelErrorModel_of_norm_error_le {computed exact : ℂ} {u : ℝ}
    (_hu : 0 ≤ u)
    (hbound : ‖computed - exact‖ ≤ u * ‖exact‖) :
    complexRelErrorModel computed exact u := by
  by_cases hexact : exact = 0
  · have hnorm : ‖computed‖ ≤ 0 := by
      simpa [hexact] using hbound
    have hcomputed : computed = 0 := norm_le_zero_iff.mp hnorm
    refine ⟨0, ?_, ?_⟩
    · simpa using _hu
    · simp [hexact, hcomputed]
  · let delta : ℂ := (computed - exact) / exact
    have hexact_norm_pos : 0 < ‖exact‖ := norm_pos_iff.mpr hexact
    refine ⟨delta, ?_, ?_⟩
    · have hdelta_norm : ‖delta‖ = ‖computed - exact‖ / ‖exact‖ := by
        simp [delta]
      rw [hdelta_norm]
      exact (div_le_iff₀ hexact_norm_pos).mpr hbound
    · simp [delta]
      field_simp [hexact]
      ring

/-- Complex addition implemented by two rounded real additions, as in Higham
Chapter 3 equation (3.13a). -/
noncomputable def fl_complexAdd (fp : FPModel) (x y : ℂ) : ℂ :=
  ⟨fp.fl_add x.re y.re, fp.fl_add x.im y.im⟩

/-- Complex subtraction implemented by two rounded real subtractions. -/
noncomputable def fl_complexSub (fp : FPModel) (x y : ℂ) : ℂ :=
  ⟨fp.fl_sub x.re y.re, fp.fl_sub x.im y.im⟩

/-- Squared-norm error bound for rounded complex addition. -/
theorem fl_complexAdd_normSq_error_le (fp : FPModel) (x y : ℂ) :
    Complex.normSq (fl_complexAdd fp x y - (x + y)) ≤
      fp.u ^ 2 * Complex.normSq (x + y) := by
  obtain ⟨deltaRe, hdeltaRe, hflRe⟩ := fp.model_add x.re y.re
  obtain ⟨deltaIm, hdeltaIm, hflIm⟩ := fp.model_add x.im y.im
  have hdeltaRe_sq : deltaRe ^ 2 ≤ fp.u ^ 2 := by
    have habs : |deltaRe| ≤ |fp.u| := by
      simpa [abs_of_nonneg fp.u_nonneg] using hdeltaRe
    exact sq_le_sq.mpr habs
  have hdeltaIm_sq : deltaIm ^ 2 ≤ fp.u ^ 2 := by
    have habs : |deltaIm| ≤ |fp.u| := by
      simpa [abs_of_nonneg fp.u_nonneg] using hdeltaIm
    exact sq_le_sq.mpr habs
  have hre_sq_nonneg : 0 ≤ (x.re + y.re) ^ 2 := sq_nonneg _
  have him_sq_nonneg : 0 ≤ (x.im + y.im) ^ 2 := sq_nonneg _
  simp [fl_complexAdd, Complex.normSq_apply, hflRe, hflIm, pow_two]
  nlinarith

/-- Normwise error bound for rounded complex addition. -/
theorem fl_complexAdd_error_bound (fp : FPModel) (x y : ℂ) :
    ‖fl_complexAdd fp x y - (x + y)‖ ≤ fp.u * ‖x + y‖ := by
  have hsq := fl_complexAdd_normSq_error_le fp x y
  have hrhs_nonneg : 0 ≤ fp.u * ‖x + y‖ :=
    mul_nonneg fp.u_nonneg (norm_nonneg _)
  have hsq_norm :
      ‖fl_complexAdd fp x y - (x + y)‖ ^ 2 ≤ (fp.u * ‖x + y‖) ^ 2 := by
    have hrhs_sq :
        (fp.u * ‖x + y‖) ^ 2 = fp.u ^ 2 * Complex.normSq (x + y) := by
      rw [mul_pow, ← Complex.normSq_eq_norm_sq]
    rw [← Complex.normSq_eq_norm_sq, hrhs_sq]
    exact hsq
  have habs := sq_le_sq.mp hsq_norm
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs_nonneg] using habs

/-- **Complex addition error model** (Higham Chapter 3, Lemma 3.5, addition
case).

The computed operation uses two rounded real additions and satisfies the source
complex relative-error form with radius `u`. -/
theorem fl_complexAdd_rel_error_model (fp : FPModel) (x y : ℂ) :
    complexRelErrorModel (fl_complexAdd fp x y) (x + y) fp.u :=
  complexRelErrorModel_of_norm_error_le fp.u_nonneg
    (fl_complexAdd_error_bound fp x y)

/-- Squared-norm error bound for rounded complex subtraction. -/
theorem fl_complexSub_normSq_error_le (fp : FPModel) (x y : ℂ) :
    Complex.normSq (fl_complexSub fp x y - (x - y)) ≤
      fp.u ^ 2 * Complex.normSq (x - y) := by
  obtain ⟨deltaRe, hdeltaRe, hflRe⟩ := fp.model_sub x.re y.re
  obtain ⟨deltaIm, hdeltaIm, hflIm⟩ := fp.model_sub x.im y.im
  have hdeltaRe_sq : deltaRe ^ 2 ≤ fp.u ^ 2 := by
    have habs : |deltaRe| ≤ |fp.u| := by
      simpa [abs_of_nonneg fp.u_nonneg] using hdeltaRe
    exact sq_le_sq.mpr habs
  have hdeltaIm_sq : deltaIm ^ 2 ≤ fp.u ^ 2 := by
    have habs : |deltaIm| ≤ |fp.u| := by
      simpa [abs_of_nonneg fp.u_nonneg] using hdeltaIm
    exact sq_le_sq.mpr habs
  have hre_sq_nonneg : 0 ≤ (x.re - y.re) ^ 2 := sq_nonneg _
  have him_sq_nonneg : 0 ≤ (x.im - y.im) ^ 2 := sq_nonneg _
  simp [fl_complexSub, Complex.normSq_apply, hflRe, hflIm, pow_two]
  nlinarith

/-- Normwise error bound for rounded complex subtraction. -/
theorem fl_complexSub_error_bound (fp : FPModel) (x y : ℂ) :
    ‖fl_complexSub fp x y - (x - y)‖ ≤ fp.u * ‖x - y‖ := by
  have hsq := fl_complexSub_normSq_error_le fp x y
  have hrhs_nonneg : 0 ≤ fp.u * ‖x - y‖ :=
    mul_nonneg fp.u_nonneg (norm_nonneg _)
  have hsq_norm :
      ‖fl_complexSub fp x y - (x - y)‖ ^ 2 ≤ (fp.u * ‖x - y‖) ^ 2 := by
    have hrhs_sq :
        (fp.u * ‖x - y‖) ^ 2 = fp.u ^ 2 * Complex.normSq (x - y) := by
      rw [mul_pow, ← Complex.normSq_eq_norm_sq]
    rw [← Complex.normSq_eq_norm_sq, hrhs_sq]
    exact hsq
  have habs := sq_le_sq.mp hsq_norm
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs_nonneg] using habs

/-- **Complex subtraction error model** (Higham Chapter 3, Lemma 3.5,
subtraction case).

The computed operation uses two rounded real subtractions and satisfies the
source complex relative-error form with radius `u`. -/
theorem fl_complexSub_rel_error_model (fp : FPModel) (x y : ℂ) :
    complexRelErrorModel (fl_complexSub fp x y) (x - y) fp.u :=
  complexRelErrorModel_of_norm_error_le fp.u_nonneg
    (fl_complexSub_error_bound fp x y)

/-- Complex multiplication implemented by the standard four real products and
two final rounded real additions/subtractions, as in Higham Chapter 3 equation
(3.13b). -/
noncomputable def fl_complexMul (fp : FPModel) (x y : ℂ) : ℂ :=
  ⟨fp.fl_sub (fp.fl_mul x.re y.re) (fp.fl_mul x.im y.im),
    fp.fl_add (fp.fl_mul x.re y.im) (fp.fl_mul x.im y.re)⟩

/-- Real component error for `fl(fl(a*c) - fl(b*d))`.

This is the scalar kernel used by the real part of rounded complex
multiplication in Higham Chapter 3 equation (3.13b). -/
theorem fl_mul_sub_error_le_gamma2 (fp : FPModel) (hγ : gammaValid fp 2)
    (a b c d : ℝ) :
    |fp.fl_sub (fp.fl_mul a c) (fp.fl_mul b d) - (a * c - b * d)| ≤
      gamma fp 2 * (|a * c| + |b * d|) := by
  obtain ⟨δac, hδac, hac⟩ := fp.model_mul a c
  obtain ⟨δbd, hδbd, hbd⟩ := fp.model_mul b d
  obtain ⟨δs, hδs, hs⟩ := fp.model_sub (fp.fl_mul a c) (fp.fl_mul b d)
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hδacγ : |δac| ≤ gamma fp 1 :=
    le_trans hδac (u_le_gamma fp (by norm_num) hγ1)
  have hδbdγ : |δbd| ≤ gamma fp 1 :=
    le_trans hδbd (u_le_gamma fp (by norm_num) hγ1)
  have hδsγ : |δs| ≤ gamma fp 1 :=
    le_trans hδs (u_le_gamma fp (by norm_num) hγ1)
  obtain ⟨θac, hθac, hθac_eq⟩ :=
    gamma_mul fp 1 1 δac δs hδacγ hδsγ (by simpa using hγ)
  obtain ⟨θbd, hθbd, hθbd_eq⟩ :=
    gamma_mul fp 1 1 δbd δs hδbdγ hδsγ (by simpa using hγ)
  have hrewrite :
      fp.fl_sub (fp.fl_mul a c) (fp.fl_mul b d) - (a * c - b * d) =
        (a * c) * θac - (b * d) * θbd := by
    rw [hs, hac, hbd]
    calc
      (((a * c) * (1 + δac) - (b * d) * (1 + δbd)) * (1 + δs) -
          (a * c - b * d))
          = (a * c) * ((1 + δac) * (1 + δs) - 1) -
              (b * d) * ((1 + δbd) * (1 + δs) - 1) := by
              ring
      _ = (a * c) * θac - (b * d) * θbd := by
              rw [hθac_eq, hθbd_eq]
              ring
  have hγ2_nonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hγ
  calc
    |fp.fl_sub (fp.fl_mul a c) (fp.fl_mul b d) - (a * c - b * d)|
        = |(a * c) * θac - (b * d) * θbd| := by rw [hrewrite]
    _ ≤ |(a * c) * θac| + |(b * d) * θbd| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le ((a * c) * θac) (-((b * d) * θbd))
    _ = |a * c| * |θac| + |b * d| * |θbd| := by
        rw [abs_mul (a * c) θac, abs_mul (b * d) θbd]
    _ ≤ |a * c| * gamma fp 2 + |b * d| * gamma fp 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hθac (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hθbd (abs_nonneg _))
    _ = gamma fp 2 * (|a * c| + |b * d|) := by ring

/-- Real component error for `fl(fl(a*d) + fl(b*c))`.

This is the scalar kernel used by the imaginary part of rounded complex
multiplication in Higham Chapter 3 equation (3.13b). -/
theorem fl_mul_add_error_le_gamma2 (fp : FPModel) (hγ : gammaValid fp 2)
    (a b c d : ℝ) :
    |fp.fl_add (fp.fl_mul a d) (fp.fl_mul b c) - (a * d + b * c)| ≤
      gamma fp 2 * (|a * d| + |b * c|) := by
  obtain ⟨δad, hδad, had⟩ := fp.model_mul a d
  obtain ⟨δbc, hδbc, hbc⟩ := fp.model_mul b c
  obtain ⟨δs, hδs, hs⟩ := fp.model_add (fp.fl_mul a d) (fp.fl_mul b c)
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hδadγ : |δad| ≤ gamma fp 1 :=
    le_trans hδad (u_le_gamma fp (by norm_num) hγ1)
  have hδbcγ : |δbc| ≤ gamma fp 1 :=
    le_trans hδbc (u_le_gamma fp (by norm_num) hγ1)
  have hδsγ : |δs| ≤ gamma fp 1 :=
    le_trans hδs (u_le_gamma fp (by norm_num) hγ1)
  obtain ⟨θad, hθad, hθad_eq⟩ :=
    gamma_mul fp 1 1 δad δs hδadγ hδsγ (by simpa using hγ)
  obtain ⟨θbc, hθbc, hθbc_eq⟩ :=
    gamma_mul fp 1 1 δbc δs hδbcγ hδsγ (by simpa using hγ)
  have hrewrite :
      fp.fl_add (fp.fl_mul a d) (fp.fl_mul b c) - (a * d + b * c) =
        (a * d) * θad + (b * c) * θbc := by
    rw [hs, had, hbc]
    calc
      (((a * d) * (1 + δad) + (b * c) * (1 + δbc)) * (1 + δs) -
          (a * d + b * c))
          = (a * d) * ((1 + δad) * (1 + δs) - 1) +
              (b * c) * ((1 + δbc) * (1 + δs) - 1) := by
              ring
      _ = (a * d) * θad + (b * c) * θbc := by
              rw [hθad_eq, hθbc_eq]
              ring
  calc
    |fp.fl_add (fp.fl_mul a d) (fp.fl_mul b c) - (a * d + b * c)|
        = |(a * d) * θad + (b * c) * θbc| := by rw [hrewrite]
    _ ≤ |(a * d) * θad| + |(b * c) * θbc| := abs_add_le _ _
    _ = |a * d| * |θad| + |b * c| * |θbc| := by
        rw [abs_mul (a * d) θad, abs_mul (b * c) θbc]
    _ ≤ |a * d| * gamma fp 2 + |b * c| * gamma fp 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hθad (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hθbc (abs_nonneg _))
    _ = gamma fp 2 * (|a * d| + |b * c|) := by ring

/-- The elementary norm conversion behind the `sqrt 2` in Higham Chapter 3,
Lemma 3.5 for complex multiplication. -/
theorem complex_mul_component_abs_terms_sq_le (a b c d : ℝ) :
    (|a * c| + |b * d|) ^ 2 + (|a * d| + |b * c|) ^ 2 ≤
      2 * ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := by
  rw [abs_mul a c, abs_mul b d, abs_mul a d, abs_mul b c]
  have h1 : 0 ≤ (|a| * |c| - |b| * |d|) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (|a| * |d| - |b| * |c|) ^ 2 := sq_nonneg _
  nlinarith [sq_abs a, sq_abs b, sq_abs c, sq_abs d]

/-- Squared-norm error bound for rounded complex multiplication. -/
theorem fl_complexMul_normSq_error_le (fp : FPModel) (hγ : gammaValid fp 2)
    (x y : ℂ) :
    Complex.normSq (fl_complexMul fp x y - x * y) ≤
      2 * (gamma fp 2) ^ 2 * Complex.normSq (x * y) := by
  let γ := gamma fp 2
  let er :=
    fp.fl_sub (fp.fl_mul x.re y.re) (fp.fl_mul x.im y.im) -
      (x.re * y.re - x.im * y.im)
  let ei :=
    fp.fl_add (fp.fl_mul x.re y.im) (fp.fl_mul x.im y.re) -
      (x.re * y.im + x.im * y.re)
  let R := |x.re * y.re| + |x.im * y.im|
  let I := |x.re * y.im| + |x.im * y.re|
  have hγ_nonneg : 0 ≤ γ := gamma_nonneg fp hγ
  have hR_nonneg : 0 ≤ R := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hI_nonneg : 0 ≤ I := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hre_abs : |er| ≤ γ * R := by
    simpa [γ, er, R] using fl_mul_sub_error_le_gamma2 fp hγ x.re x.im y.re y.im
  have him_abs : |ei| ≤ γ * I := by
    simpa [γ, ei, I] using fl_mul_add_error_le_gamma2 fp hγ x.re x.im y.re y.im
  have hre_sq : er ^ 2 ≤ (γ * R) ^ 2 := by
    exact (sq_le_sq).mpr (by
      simpa [abs_of_nonneg (mul_nonneg hγ_nonneg hR_nonneg)] using hre_abs)
  have him_sq : ei ^ 2 ≤ (γ * I) ^ 2 := by
    exact (sq_le_sq).mpr (by
      simpa [abs_of_nonneg (mul_nonneg hγ_nonneg hI_nonneg)] using him_abs)
  have hcomp : R ^ 2 + I ^ 2 ≤ 2 * Complex.normSq (x * y) := by
    have h :=
      complex_mul_component_abs_terms_sq_le x.re x.im y.re y.im
    rw [Complex.normSq_mul]
    simpa [R, I, Complex.normSq_apply, pow_two] using h
  have hsq_terms : er ^ 2 + ei ^ 2 ≤ γ ^ 2 * (R ^ 2 + I ^ 2) := by
    nlinarith
  have hsq_bound : er ^ 2 + ei ^ 2 ≤ γ ^ 2 * (2 * Complex.normSq (x * y)) := by
    exact le_trans hsq_terms
      (mul_le_mul_of_nonneg_left hcomp (sq_nonneg γ))
  have hnorm :
      Complex.normSq (fl_complexMul fp x y - x * y) = er ^ 2 + ei ^ 2 := by
    simp [fl_complexMul, er, ei, Complex.normSq_apply, pow_two]
  rw [hnorm]
  nlinarith

/-- Normwise error bound for rounded complex multiplication. -/
theorem fl_complexMul_error_bound (fp : FPModel) (hγ : gammaValid fp 2)
    (x y : ℂ) :
    ‖fl_complexMul fp x y - x * y‖ ≤
      Real.sqrt 2 * gamma fp 2 * ‖x * y‖ := by
  have hsq := fl_complexMul_normSq_error_le fp hγ x y
  have hγ_nonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hγ
  have hrhs_nonneg : 0 ≤ Real.sqrt 2 * gamma fp 2 * ‖x * y‖ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hγ_nonneg) (norm_nonneg _)
  have hsq_norm :
      ‖fl_complexMul fp x y - x * y‖ ^ 2 ≤
        (Real.sqrt 2 * gamma fp 2 * ‖x * y‖) ^ 2 := by
    have hrhs_sq :
        (Real.sqrt 2 * gamma fp 2 * ‖x * y‖) ^ 2 =
          2 * (gamma fp 2) ^ 2 * Complex.normSq (x * y) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        ← Complex.normSq_eq_norm_sq]
    rw [← Complex.normSq_eq_norm_sq, hrhs_sq]
    exact hsq
  have habs := sq_le_sq.mp hsq_norm
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs_nonneg,
    abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ)), abs_of_nonneg hγ_nonneg,
    norm_mul, mul_assoc] using habs

/-- **Complex multiplication error model** (Higham Chapter 3, Lemma 3.5,
multiplication case).

The computed operation uses equation (3.13b) and satisfies the source complex
relative-error form with radius `sqrt(2) * gamma_2`. -/
theorem fl_complexMul_rel_error_model (fp : FPModel) (hγ : gammaValid fp 2)
    (x y : ℂ) :
    complexRelErrorModel (fl_complexMul fp x y) (x * y)
      (Real.sqrt 2 * gamma fp 2) := by
  have hradius_nonneg : 0 ≤ Real.sqrt 2 * gamma fp 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (gamma_nonneg fp hγ)
  exact complexRelErrorModel_of_norm_error_le hradius_nonneg
    (fl_complexMul_error_bound fp hγ x y)

/-- If a real numerator and positive denominator have relative/absolute errors
controlled by `gamma_2`, the exact quotient of the computed numerator and
denominator has the source `gamma_4` absolute error bound.

This is the real scalar inequality used in Higham Chapter 3, Lemma 3.5 for
the real and imaginary parts of complex division. -/
theorem quotient_abs_error_le_gamma4_of_gamma2
    (fp : FPModel) (hγ4 : gammaValid fp 4)
    {N Nhat D Dhat A : ℝ}
    (hDpos : 0 < D) (hA_nonneg : 0 ≤ A)
    (hN_abs : |N| ≤ A)
    (hNhat_abs : |Nhat - N| ≤ gamma fp 2 * A)
    (hDhat_abs : |Dhat - D| ≤ gamma fp 2 * D) :
    |Nhat / Dhat - N / D| ≤ gamma fp 4 * (A / D) := by
  let γ2 := gamma fp 2
  have hγ2_nonneg : 0 ≤ γ2 :=
    gamma_nonneg fp (gammaValid_mono fp (by norm_num) hγ4)
  have hγ2_lt_one : γ2 < 1 := by
    simpa [γ2] using gamma_lt_one fp 2 (by simpa using hγ4)
  have hD_nonneg : 0 ≤ D := le_of_lt hDpos
  have hγ2D_nonneg : 0 ≤ γ2 * D := mul_nonneg hγ2_nonneg hD_nonneg
  have hDhat_lower : D * (1 - γ2) ≤ Dhat := by
    have hleft := (abs_le.mp hDhat_abs).1
    nlinarith
  have hDhat_pos : 0 < Dhat := by
    have hlow_pos : 0 < D * (1 - γ2) :=
      mul_pos hDpos (by linarith)
    exact lt_of_lt_of_le hlow_pos hDhat_lower
  have hDhatD_pos : 0 < Dhat * D := mul_pos hDhat_pos hDpos
  have hsplit :
      Nhat / Dhat - N / D =
        (Nhat - N) / Dhat + N * (D - Dhat) / (Dhat * D) := by
    field_simp [hDhat_pos.ne', hDpos.ne']
    ring
  have htri :
      |Nhat / Dhat - N / D| ≤
        |Nhat - N| / Dhat + |N| * |Dhat - D| / (Dhat * D) := by
    rw [hsplit]
    calc
      |(Nhat - N) / Dhat + N * (D - Dhat) / (Dhat * D)|
          ≤ |(Nhat - N) / Dhat| + |N * (D - Dhat) / (Dhat * D)| :=
            abs_add_le _ _
      _ = |Nhat - N| / Dhat + |N| * |D - Dhat| / (Dhat * D) := by
          rw [abs_div, abs_of_pos hDhat_pos, abs_div,
            abs_of_pos hDhatD_pos, abs_mul]
      _ = |Nhat - N| / Dhat + |N| * |Dhat - D| / (Dhat * D) := by
          rw [abs_sub_comm D Dhat]
  have hterm1 :
      |Nhat - N| / Dhat ≤ γ2 * A / Dhat := by
    exact div_le_div_of_nonneg_right
      (by simpa [γ2] using hNhat_abs) (le_of_lt hDhat_pos)
  have hden_abs' : |Dhat - D| ≤ γ2 * D := by
    simpa [γ2] using hDhat_abs
  have hterm2_num :
      |N| * |Dhat - D| ≤ A * (γ2 * D) := by
    exact mul_le_mul hN_abs hden_abs' (abs_nonneg _) hA_nonneg
  have hterm2 :
      |N| * |Dhat - D| / (Dhat * D) ≤ γ2 * A / Dhat := by
    calc
      |N| * |Dhat - D| / (Dhat * D)
          ≤ A * (γ2 * D) / (Dhat * D) :=
            div_le_div_of_nonneg_right hterm2_num (le_of_lt hDhatD_pos)
      _ = γ2 * A / Dhat := by
          field_simp [hDhat_pos.ne', hDpos.ne']
  have htwo_over_dhat :
      |Nhat / Dhat - N / D| ≤ 2 * (γ2 * A / Dhat) := by
    calc
      |Nhat / Dhat - N / D|
          ≤ |Nhat - N| / Dhat + |N| * |Dhat - D| / (Dhat * D) := htri
      _ ≤ γ2 * A / Dhat + γ2 * A / Dhat := add_le_add hterm1 hterm2
      _ = 2 * (γ2 * A / Dhat) := by ring
  have hnum_nonneg : 0 ≤ 2 * (γ2 * A) :=
    mul_nonneg (by norm_num) (mul_nonneg hγ2_nonneg hA_nonneg)
  have hlower_pos : 0 < D * (1 - γ2) :=
    mul_pos hDpos (by linarith)
  have hden_step :
      2 * (γ2 * A / Dhat) ≤ 2 * (γ2 * A) / (D * (1 - γ2)) := by
    calc
      2 * (γ2 * A / Dhat) = 2 * (γ2 * A) / Dhat := by ring
      _ ≤ 2 * (γ2 * A) / (D * (1 - γ2)) :=
        div_le_div_of_nonneg_left hnum_nonneg hlower_pos hDhat_lower
  have hfour_u : 4 * fp.u < 1 := by
    have h := hγ4
    unfold gammaValid at h
    norm_num at h
    simpa [mul_assoc] using h
  have htwo_u : 2 * fp.u < 1 := by
    nlinarith [fp.u_nonneg, hfour_u]
  have hden2_pos : 0 < 1 - 2 * fp.u := by linarith
  have hden4_pos : 0 < 1 - 4 * fp.u := by linarith
  have hgamma_eq : 2 * γ2 / (1 - γ2) = gamma fp 4 := by
    unfold γ2 gamma
    norm_num
    field_simp [hden2_pos.ne', hden4_pos.ne']
    ring
  have hfinal_eq :
      2 * (γ2 * A) / (D * (1 - γ2)) = gamma fp 4 * (A / D) := by
    rw [← hgamma_eq]
    field_simp [hDpos.ne', (by linarith : (1 - γ2) ≠ 0)]
  exact le_trans htwo_over_dhat (by simpa [hfinal_eq] using hden_step)

/-- If a real numerator and positive denominator have relative/absolute errors
controlled by `gamma_3`, the exact quotient of the computed numerator and
denominator has a `gamma_6` absolute error bound.

This is the scalar quotient core needed for Smith's overflow-avoiding complex
division: its numerator and denominator branches use three rounded real
operations before the final real division. -/
theorem quotient_abs_error_le_gamma6_of_gamma3
    (fp : FPModel) (hγ6 : gammaValid fp 6)
    {N Nhat D Dhat A : ℝ}
    (hDpos : 0 < D) (hA_nonneg : 0 ≤ A)
    (hN_abs : |N| ≤ A)
    (hNhat_abs : |Nhat - N| ≤ gamma fp 3 * A)
    (hDhat_abs : |Dhat - D| ≤ gamma fp 3 * D) :
    |Nhat / Dhat - N / D| ≤ gamma fp 6 * (A / D) := by
  let γ3 := gamma fp 3
  have hγ3_nonneg : 0 ≤ γ3 :=
    gamma_nonneg fp (gammaValid_mono fp (by norm_num) hγ6)
  have hγ3_lt_one : γ3 < 1 := by
    simpa [γ3] using gamma_lt_one fp 3 (by simpa using hγ6)
  have hD_nonneg : 0 ≤ D := le_of_lt hDpos
  have hγ3D_nonneg : 0 ≤ γ3 * D := mul_nonneg hγ3_nonneg hD_nonneg
  have hDhat_lower : D * (1 - γ3) ≤ Dhat := by
    have hleft := (abs_le.mp hDhat_abs).1
    nlinarith
  have hDhat_pos : 0 < Dhat := by
    have hlow_pos : 0 < D * (1 - γ3) :=
      mul_pos hDpos (by linarith)
    exact lt_of_lt_of_le hlow_pos hDhat_lower
  have hDhatD_pos : 0 < Dhat * D := mul_pos hDhat_pos hDpos
  have hsplit :
      Nhat / Dhat - N / D =
        (Nhat - N) / Dhat + N * (D - Dhat) / (Dhat * D) := by
    field_simp [hDhat_pos.ne', hDpos.ne']
    ring
  have htri :
      |Nhat / Dhat - N / D| ≤
        |Nhat - N| / Dhat + |N| * |Dhat - D| / (Dhat * D) := by
    rw [hsplit]
    calc
      |(Nhat - N) / Dhat + N * (D - Dhat) / (Dhat * D)|
          ≤ |(Nhat - N) / Dhat| + |N * (D - Dhat) / (Dhat * D)| :=
            abs_add_le _ _
      _ = |Nhat - N| / Dhat + |N| * |D - Dhat| / (Dhat * D) := by
          rw [abs_div, abs_of_pos hDhat_pos, abs_div,
            abs_of_pos hDhatD_pos, abs_mul]
      _ = |Nhat - N| / Dhat + |N| * |Dhat - D| / (Dhat * D) := by
          rw [abs_sub_comm D Dhat]
  have hterm1 :
      |Nhat - N| / Dhat ≤ γ3 * A / Dhat := by
    exact div_le_div_of_nonneg_right
      (by simpa [γ3] using hNhat_abs) (le_of_lt hDhat_pos)
  have hden_abs' : |Dhat - D| ≤ γ3 * D := by
    simpa [γ3] using hDhat_abs
  have hterm2_num :
      |N| * |Dhat - D| ≤ A * (γ3 * D) := by
    exact mul_le_mul hN_abs hden_abs' (abs_nonneg _) hA_nonneg
  have hterm2 :
      |N| * |Dhat - D| / (Dhat * D) ≤ γ3 * A / Dhat := by
    calc
      |N| * |Dhat - D| / (Dhat * D)
          ≤ A * (γ3 * D) / (Dhat * D) :=
            div_le_div_of_nonneg_right hterm2_num (le_of_lt hDhatD_pos)
      _ = γ3 * A / Dhat := by
          field_simp [hDhat_pos.ne', hDpos.ne']
  have htwo_over_dhat :
      |Nhat / Dhat - N / D| ≤ 2 * (γ3 * A / Dhat) := by
    calc
      |Nhat / Dhat - N / D|
          ≤ |Nhat - N| / Dhat + |N| * |Dhat - D| / (Dhat * D) := htri
      _ ≤ γ3 * A / Dhat + γ3 * A / Dhat := add_le_add hterm1 hterm2
      _ = 2 * (γ3 * A / Dhat) := by ring
  have hnum_nonneg : 0 ≤ 2 * (γ3 * A) :=
    mul_nonneg (by norm_num) (mul_nonneg hγ3_nonneg hA_nonneg)
  have hlower_pos : 0 < D * (1 - γ3) :=
    mul_pos hDpos (by linarith)
  have hden_step :
      2 * (γ3 * A / Dhat) ≤ 2 * (γ3 * A) / (D * (1 - γ3)) := by
    calc
      2 * (γ3 * A / Dhat) = 2 * (γ3 * A) / Dhat := by ring
      _ ≤ 2 * (γ3 * A) / (D * (1 - γ3)) :=
        div_le_div_of_nonneg_left hnum_nonneg hlower_pos hDhat_lower
  have hsix_u : 6 * fp.u < 1 := by
    have h := hγ6
    unfold gammaValid at h
    norm_num at h
    simpa [mul_assoc] using h
  have hthree_u : 3 * fp.u < 1 := by
    nlinarith [fp.u_nonneg, hsix_u]
  have hden3_pos : 0 < 1 - 3 * fp.u := by linarith
  have hden6_pos : 0 < 1 - 6 * fp.u := by linarith
  have hgamma_eq : 2 * γ3 / (1 - γ3) = gamma fp 6 := by
    unfold γ3 gamma
    norm_num
    field_simp [hden3_pos.ne', hden6_pos.ne']
    ring
  have hfinal_eq :
      2 * (γ3 * A) / (D * (1 - γ3)) = gamma fp 6 * (A / D) := by
    rw [← hgamma_eq]
    field_simp [hDpos.ne', (by linarith : (1 - γ3) ≠ 0)]
  exact le_trans htwo_over_dhat (by simpa [hfinal_eq] using hden_step)

/-- If a real numerator and positive denominator have relative/absolute errors
controlled by `gamma_3`, one final rounded real division gives a `gamma_7`
absolute error bound.

This is the scalar bridge used by the Smith/Chapter 25 overflow-avoiding
complex division analysis. -/
theorem fl_quotient_abs_error_le_gamma7_of_gamma3
    (fp : FPModel) (hγ7 : gammaValid fp 7)
    {N Nhat D Dhat A : ℝ}
    (hDpos : 0 < D) (hA_nonneg : 0 ≤ A)
    (hN_abs : |N| ≤ A)
    (hNhat_abs : |Nhat - N| ≤ gamma fp 3 * A)
    (hDhat_abs : |Dhat - D| ≤ gamma fp 3 * D) :
    |fp.fl_div Nhat Dhat - N / D| ≤ gamma fp 7 * (A / D) := by
  let γ3 := gamma fp 3
  let γ6 := gamma fp 6
  let B := A / D
  have hγ6valid : gammaValid fp 6 := gammaValid_mono fp (by norm_num) hγ7
  have hγ3valid : gammaValid fp 3 := gammaValid_mono fp (by norm_num) hγ7
  have hγ1valid : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ7
  have hγ3_nonneg : 0 ≤ γ3 := gamma_nonneg fp hγ3valid
  have hγ6_nonneg : 0 ≤ γ6 := gamma_nonneg fp hγ6valid
  have hB_nonneg : 0 ≤ B := div_nonneg hA_nonneg hDpos.le
  have hγ3_lt_one : γ3 < 1 := by
    simpa [γ3] using gamma_lt_one fp 3 hγ6valid
  have hDhat_lower : D * (1 - γ3) ≤ Dhat := by
    have hleft := (abs_le.mp hDhat_abs).1
    nlinarith [le_of_lt hDpos]
  have hDhat_pos : 0 < Dhat := by
    have hlow_pos : 0 < D * (1 - γ3) :=
      mul_pos hDpos (by linarith)
    exact lt_of_lt_of_le hlow_pos hDhat_lower
  obtain ⟨δ, hδ, hfl⟩ := fp.model_div Nhat Dhat hDhat_pos.ne'
  let Qhat := Nhat / Dhat
  let Q := N / D
  have hquot : |Qhat - Q| ≤ γ6 * B := by
    simpa [Qhat, Q, γ6, B] using
      quotient_abs_error_le_gamma6_of_gamma3 fp hγ6valid hDpos hA_nonneg
        hN_abs hNhat_abs hDhat_abs
  have hQ_abs : |Q| ≤ B := by
    have hD_nonneg : 0 ≤ D := le_of_lt hDpos
    calc
      |Q| = |N| / D := by
        simp [Q, abs_div, abs_of_pos hDpos]
      _ ≤ A / D := div_le_div_of_nonneg_right hN_abs hD_nonneg
      _ = B := rfl
  have hQhat_abs : |Qhat| ≤ (1 + γ6) * B := by
    calc
      |Qhat| = |Q + (Qhat - Q)| := by ring_nf
      _ ≤ |Q| + |Qhat - Q| := abs_add_le _ _
      _ ≤ B + γ6 * B := add_le_add hQ_abs hquot
      _ = (1 + γ6) * B := by ring
  have hcoeff :
      γ6 + fp.u * (1 + γ6) ≤ gamma fp 7 := by
    have hu_le_γ1 : fp.u ≤ gamma fp 1 :=
      u_le_gamma fp (by norm_num) hγ1valid
    have hleft :
        γ6 + fp.u * (1 + γ6) ≤
          gamma fp 6 + gamma fp 1 + gamma fp 6 * gamma fp 1 := by
      calc
        γ6 + fp.u * (1 + γ6)
            = gamma fp 6 + fp.u + gamma fp 6 * fp.u := by
                simp [γ6]
                ring
        _ ≤ gamma fp 6 + gamma fp 1 + gamma fp 6 * gamma fp 1 := by
            have hsum : gamma fp 6 + fp.u ≤ gamma fp 6 + gamma fp 1 := by
              linarith
            have hprod : gamma fp 6 * fp.u ≤ gamma fp 6 * gamma fp 1 :=
              mul_le_mul_of_nonneg_left hu_le_γ1 hγ6_nonneg
            exact add_le_add hsum hprod
    have hsum :
        gamma fp 6 + gamma fp 1 + gamma fp 6 * gamma fp 1 ≤
          gamma fp (6 + 1) :=
      gamma_sum_le fp 6 1 (by simpa using hγ7)
    exact le_trans hleft (by simpa using hsum)
  have hfl_error :
      |fp.fl_div Nhat Dhat - Q| ≤ (γ6 + fp.u * (1 + γ6)) * B := by
    rw [hfl]
    calc
      |Qhat * (1 + δ) - Q|
          = |(Qhat - Q) + Qhat * δ| := by ring_nf
      _ ≤ |Qhat - Q| + |Qhat * δ| := abs_add_le _ _
      _ = |Qhat - Q| + |Qhat| * |δ| := by rw [abs_mul]
      _ ≤ γ6 * B + ((1 + γ6) * B) * fp.u := by
          exact add_le_add hquot
            (mul_le_mul hQhat_abs hδ (abs_nonneg _) (by
              exact mul_nonneg (by linarith [hγ6_nonneg]) hB_nonneg))
      _ = (γ6 + fp.u * (1 + γ6)) * B := by ring
  calc
    |fp.fl_div Nhat Dhat - N / D|
        = |fp.fl_div Nhat Dhat - Q| := rfl
    _ ≤ (γ6 + fp.u * (1 + γ6)) * B := hfl_error
    _ ≤ gamma fp 7 * B := mul_le_mul_of_nonneg_right hcoeff hB_nonneg

/-- Absolute-denominator version of
`quotient_abs_error_le_gamma6_of_gamma3`.

This removes the sign side condition on Smith branch denominators; the bound is
measured relative to `|D|`. -/
theorem quotient_abs_error_le_gamma6_of_gamma3_absDen
    (fp : FPModel) (hγ6 : gammaValid fp 6)
    {N Nhat D Dhat A : ℝ}
    (hDne : D ≠ 0) (hA_nonneg : 0 ≤ A)
    (hN_abs : |N| ≤ A)
    (hNhat_abs : |Nhat - N| ≤ gamma fp 3 * A)
    (hDhat_abs : |Dhat - D| ≤ gamma fp 3 * |D|) :
    |Nhat / Dhat - N / D| ≤ gamma fp 6 * (A / |D|) := by
  by_cases hD_nonneg : 0 ≤ D
  · have hDpos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hDne)
    simpa [abs_of_nonneg hD_nonneg] using
      quotient_abs_error_le_gamma6_of_gamma3 fp hγ6 hDpos hA_nonneg
        hN_abs hNhat_abs (by simpa [abs_of_nonneg hD_nonneg] using hDhat_abs)
  · have hDneg : D < 0 := lt_of_not_ge hD_nonneg
    have hDpos' : 0 < -D := by linarith
    have hN_abs' : |-N| ≤ A := by simpa using hN_abs
    have hNhat_abs' :
        |-Nhat - -N| ≤ gamma fp 3 * A := by
      calc
        |-Nhat - -N| = |Nhat - N| := by
          rw [show -Nhat - -N = -(Nhat - N) by ring, abs_neg]
        _ ≤ gamma fp 3 * A := hNhat_abs
    have hDhat_abs' :
        |-Dhat - -D| ≤ gamma fp 3 * (-D) := by
      have hDhat_abs_neg : |Dhat - D| ≤ gamma fp 3 * (-D) := by
        simpa [abs_of_neg hDneg] using hDhat_abs
      calc
        |-Dhat - -D| = |Dhat - D| := by
          rw [show -Dhat - -D = -(Dhat - D) by ring, abs_neg]
        _ ≤ gamma fp 3 * (-D) := hDhat_abs_neg
    have h :=
      quotient_abs_error_le_gamma6_of_gamma3 fp hγ6 hDpos' hA_nonneg
        hN_abs' hNhat_abs' hDhat_abs'
    simpa [abs_of_neg hDneg] using h

/-- Absolute-denominator version of
`fl_quotient_abs_error_le_gamma7_of_gamma3`.

The exact denominator may have either sign, as happens in Smith's complex
division branches. -/
theorem fl_quotient_abs_error_le_gamma7_of_gamma3_absDen
    (fp : FPModel) (hγ7 : gammaValid fp 7)
    {N Nhat D Dhat A : ℝ}
    (hDne : D ≠ 0) (hA_nonneg : 0 ≤ A)
    (hN_abs : |N| ≤ A)
    (hNhat_abs : |Nhat - N| ≤ gamma fp 3 * A)
    (hDhat_abs : |Dhat - D| ≤ gamma fp 3 * |D|) :
    |fp.fl_div Nhat Dhat - N / D| ≤ gamma fp 7 * (A / |D|) := by
  let γ3 := gamma fp 3
  let γ6 := gamma fp 6
  let B := A / |D|
  have hγ6valid : gammaValid fp 6 := gammaValid_mono fp (by norm_num) hγ7
  have hγ3valid : gammaValid fp 3 := gammaValid_mono fp (by norm_num) hγ7
  have hγ1valid : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ7
  have hγ3_nonneg : 0 ≤ γ3 := gamma_nonneg fp hγ3valid
  have hγ6_nonneg : 0 ≤ γ6 := gamma_nonneg fp hγ6valid
  have hDabs_pos : 0 < |D| := abs_pos.mpr hDne
  have hB_nonneg : 0 ≤ B := div_nonneg hA_nonneg (le_of_lt hDabs_pos)
  have hγ3_lt_one : γ3 < 1 := by
    simpa [γ3] using gamma_lt_one fp 3 hγ6valid
  have hDhat_ne : Dhat ≠ 0 := by
    by_cases hD_nonneg : 0 ≤ D
    · have hDpos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hDne)
      have hDhat_lower : D * (1 - γ3) ≤ Dhat := by
        have hleft := (abs_le.mp (by
          simpa [γ3, abs_of_nonneg hD_nonneg] using hDhat_abs)).1
        nlinarith
      have hDhat_pos : 0 < Dhat := by
        have hlow_pos : 0 < D * (1 - γ3) :=
          mul_pos hDpos (by linarith)
        exact lt_of_lt_of_le hlow_pos hDhat_lower
      exact hDhat_pos.ne'
    · have hDneg : D < 0 := lt_of_not_ge hD_nonneg
      have hDhat_upper : Dhat ≤ D * (1 - γ3) := by
        have hright := (abs_le.mp (by
          simpa [γ3, abs_of_neg hDneg] using hDhat_abs)).2
        nlinarith
      have hDhat_neg : Dhat < 0 := by
        have hupper_neg : D * (1 - γ3) < 0 :=
          mul_neg_of_neg_of_pos hDneg (by linarith)
        exact lt_of_le_of_lt hDhat_upper hupper_neg
      exact ne_of_lt hDhat_neg
  obtain ⟨δ, hδ, hfl⟩ := fp.model_div Nhat Dhat hDhat_ne
  let Qhat := Nhat / Dhat
  let Q := N / D
  have hquot : |Qhat - Q| ≤ γ6 * B := by
    simpa [Qhat, Q, γ6, B] using
      quotient_abs_error_le_gamma6_of_gamma3_absDen fp hγ6valid hDne hA_nonneg
        hN_abs hNhat_abs hDhat_abs
  have hQ_abs : |Q| ≤ B := by
    calc
      |Q| = |N| / |D| := by simp [Q, abs_div]
      _ ≤ A / |D| := div_le_div_of_nonneg_right hN_abs (le_of_lt hDabs_pos)
      _ = B := rfl
  have hQhat_abs : |Qhat| ≤ (1 + γ6) * B := by
    calc
      |Qhat| = |Q + (Qhat - Q)| := by ring_nf
      _ ≤ |Q| + |Qhat - Q| := abs_add_le _ _
      _ ≤ B + γ6 * B := add_le_add hQ_abs hquot
      _ = (1 + γ6) * B := by ring
  have hcoeff :
      γ6 + fp.u * (1 + γ6) ≤ gamma fp 7 := by
    have hu_le_γ1 : fp.u ≤ gamma fp 1 :=
      u_le_gamma fp (by norm_num) hγ1valid
    have hleft :
        γ6 + fp.u * (1 + γ6) ≤
          gamma fp 6 + gamma fp 1 + gamma fp 6 * gamma fp 1 := by
      calc
        γ6 + fp.u * (1 + γ6)
            = gamma fp 6 + fp.u + gamma fp 6 * fp.u := by
                simp [γ6]
                ring
        _ ≤ gamma fp 6 + gamma fp 1 + gamma fp 6 * gamma fp 1 := by
            have hsum : gamma fp 6 + fp.u ≤ gamma fp 6 + gamma fp 1 := by
              linarith
            have hprod : gamma fp 6 * fp.u ≤ gamma fp 6 * gamma fp 1 :=
              mul_le_mul_of_nonneg_left hu_le_γ1 hγ6_nonneg
            exact add_le_add hsum hprod
    have hsum :
        gamma fp 6 + gamma fp 1 + gamma fp 6 * gamma fp 1 ≤
          gamma fp (6 + 1) :=
      gamma_sum_le fp 6 1 (by simpa using hγ7)
    exact le_trans hleft (by simpa using hsum)
  have hfl_error :
      |fp.fl_div Nhat Dhat - Q| ≤ (γ6 + fp.u * (1 + γ6)) * B := by
    rw [hfl]
    calc
      |Qhat * (1 + δ) - Q|
          = |(Qhat - Q) + Qhat * δ| := by ring_nf
      _ ≤ |Qhat - Q| + |Qhat * δ| := abs_add_le _ _
      _ = |Qhat - Q| + |Qhat| * |δ| := by rw [abs_mul]
      _ ≤ γ6 * B + ((1 + γ6) * B) * fp.u := by
          exact add_le_add hquot
            (mul_le_mul hQhat_abs hδ (abs_nonneg _) (by
              exact mul_nonneg (by linarith [hγ6_nonneg]) hB_nonneg))
      _ = (γ6 + fp.u * (1 + γ6)) * B := by ring
  calc
    |fp.fl_div Nhat Dhat - N / D|
        = |fp.fl_div Nhat Dhat - Q| := rfl
    _ ≤ (γ6 + fp.u * (1 + γ6)) * B := hfl_error
    _ ≤ gamma fp 7 * B := mul_le_mul_of_nonneg_right hcoeff hB_nonneg

/-- Denominator `fl(c*c + d*d)` used in the source complex-division formula
(3.14c). -/
noncomputable def fl_complexDivDen (fp : FPModel) (y : ℂ) : ℝ :=
  fp.fl_add (fp.fl_mul y.re y.re) (fp.fl_mul y.im y.im)

/-- Real numerator `fl(a*c + b*d)` used in equation (3.14c). -/
noncomputable def fl_complexDivNumRe (fp : FPModel) (x y : ℂ) : ℝ :=
  fp.fl_add (fp.fl_mul x.re y.re) (fp.fl_mul x.im y.im)

/-- Imaginary numerator `fl(b*c - a*d)` used in equation (3.14c). -/
noncomputable def fl_complexDivNumIm (fp : FPModel) (x y : ℂ) : ℝ :=
  fp.fl_sub (fp.fl_mul x.im y.re) (fp.fl_mul x.re y.im)

/-- Complex division as represented in the proof of Higham Chapter 3,
Lemma 3.5: rounded real numerator and denominator subexpressions from (3.14c),
followed by the displayed exact real quotients. -/
noncomputable def fl_complexDiv (fp : FPModel) (x y : ℂ) : ℂ :=
  ⟨fl_complexDivNumRe fp x y / fl_complexDivDen fp y,
    fl_complexDivNumIm fp x y / fl_complexDivDen fp y⟩

/-- Denominator error for the source complex-division formula (3.14c). -/
theorem fl_complexDivDen_error_le_gamma2 (fp : FPModel) (hγ : gammaValid fp 2)
    (y : ℂ) :
    |fl_complexDivDen fp y - Complex.normSq y| ≤
      gamma fp 2 * Complex.normSq y := by
  have h :=
    fl_mul_add_error_le_gamma2 fp hγ y.re y.im y.im y.re
  simpa [fl_complexDivDen, Complex.normSq_apply, pow_two,
    abs_mul, abs_of_nonneg (sq_nonneg y.re),
    abs_of_nonneg (sq_nonneg y.im)] using h

/-- Real numerator error for the source complex-division formula (3.14c). -/
theorem fl_complexDivNumRe_error_le_gamma2 (fp : FPModel)
    (hγ : gammaValid fp 2) (x y : ℂ) :
    |fl_complexDivNumRe fp x y - (x.re * y.re + x.im * y.im)| ≤
      gamma fp 2 * (|x.re * y.re| + |x.im * y.im|) := by
  simpa [fl_complexDivNumRe] using
    fl_mul_add_error_le_gamma2 fp hγ x.re x.im y.im y.re

/-- Imaginary numerator error for the source complex-division formula (3.14c). -/
theorem fl_complexDivNumIm_error_le_gamma2 (fp : FPModel)
    (hγ : gammaValid fp 2) (x y : ℂ) :
    |fl_complexDivNumIm fp x y - (x.im * y.re - x.re * y.im)| ≤
      gamma fp 2 * (|x.im * y.re| + |x.re * y.im|) := by
  simpa [fl_complexDivNumIm] using
    fl_mul_sub_error_le_gamma2 fp hγ x.im x.re y.re y.im

/-- Real-component error for source complex division. -/
theorem fl_complexDiv_re_error_le_gamma4 (fp : FPModel)
    (hγ : gammaValid fp 4) (x y : ℂ) (hy : y ≠ 0) :
    |fl_complexDivNumRe fp x y / fl_complexDivDen fp y -
        (x.re * y.re + x.im * y.im) / Complex.normSq y| ≤
      gamma fp 4 *
        ((|x.re * y.re| + |x.im * y.im|) / Complex.normSq y) := by
  have hγ2 : gammaValid fp 2 := gammaValid_mono fp (by norm_num) hγ
  have hDpos : 0 < Complex.normSq y := by
    exact Complex.normSq_pos.mpr hy
  have hA_nonneg : 0 ≤ |x.re * y.re| + |x.im * y.im| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hN_abs : |x.re * y.re + x.im * y.im| ≤
      |x.re * y.re| + |x.im * y.im| :=
    abs_add_le _ _
  exact quotient_abs_error_le_gamma4_of_gamma2 fp hγ hDpos hA_nonneg hN_abs
    (fl_complexDivNumRe_error_le_gamma2 fp hγ2 x y)
    (fl_complexDivDen_error_le_gamma2 fp hγ2 y)

/-- Imaginary-component error for source complex division. -/
theorem fl_complexDiv_im_error_le_gamma4 (fp : FPModel)
    (hγ : gammaValid fp 4) (x y : ℂ) (hy : y ≠ 0) :
    |fl_complexDivNumIm fp x y / fl_complexDivDen fp y -
        (x.im * y.re - x.re * y.im) / Complex.normSq y| ≤
      gamma fp 4 *
        ((|x.im * y.re| + |x.re * y.im|) / Complex.normSq y) := by
  have hγ2 : gammaValid fp 2 := gammaValid_mono fp (by norm_num) hγ
  have hDpos : 0 < Complex.normSq y := by
    exact Complex.normSq_pos.mpr hy
  have hA_nonneg : 0 ≤ |x.im * y.re| + |x.re * y.im| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hN_abs : |x.im * y.re - x.re * y.im| ≤
      |x.im * y.re| + |x.re * y.im| := by
    simpa [sub_eq_add_neg, abs_neg] using
      abs_add_le (x.im * y.re) (-(x.re * y.im))
  exact quotient_abs_error_le_gamma4_of_gamma2 fp hγ hDpos hA_nonneg hN_abs
    (fl_complexDivNumIm_error_le_gamma2 fp hγ2 x y)
    (fl_complexDivDen_error_le_gamma2 fp hγ2 y)

/-- Scaled component inequality behind the `sqrt(2)` factor for source complex
division. -/
theorem complex_div_component_abs_terms_sq_le (x y : ℂ) (hy : y ≠ 0) :
    ((|x.re * y.re| + |x.im * y.im|) / Complex.normSq y) ^ 2 +
        ((|x.im * y.re| + |x.re * y.im|) / Complex.normSq y) ^ 2 ≤
      2 * Complex.normSq (x / y) := by
  have hDpos : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
  let D := Complex.normSq y
  let A := |x.re * y.re| + |x.im * y.im|
  let B := |x.im * y.re| + |x.re * y.im|
  have h :=
    complex_mul_component_abs_terms_sq_le x.re x.im y.re y.im
  have hscaled :=
    div_le_div_of_nonneg_right h (sq_nonneg D)
  have hD_ne : D ≠ 0 := by simpa [D] using hDpos.ne'
  have hleft :
      (A / D) ^ 2 + (B / D) ^ 2 = (A ^ 2 + B ^ 2) / D ^ 2 := by
    field_simp [hD_ne]
  have hright :
      2 * Complex.normSq (x / y) =
        (2 * ((x.re ^ 2 + x.im ^ 2) * (y.re ^ 2 + y.im ^ 2))) / D ^ 2 := by
    rw [Complex.normSq_div]
    simp [D, Complex.normSq_apply, pow_two]
    field_simp [hDpos.ne']
  rw [hleft, hright]
  simpa [A, B, D, pow_two, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Real-component error for source complex division, stated against the exact
complex quotient. -/
theorem fl_complexDiv_re_exact_error_le_gamma4 (fp : FPModel)
    (hγ : gammaValid fp 4) (x y : ℂ) (hy : y ≠ 0) :
    |(fl_complexDiv fp x y - x / y).re| ≤
      gamma fp 4 *
        ((|x.re * y.re| + |x.im * y.im|) / Complex.normSq y) := by
  have hDpos : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
  have hre :
      (x / y).re =
        (x.re * y.re + x.im * y.im) / Complex.normSq y := by
    rw [Complex.div_re]
    field_simp [hDpos.ne']
  simpa [fl_complexDiv, hre] using
    fl_complexDiv_re_error_le_gamma4 fp hγ x y hy

/-- Imaginary-component error for source complex division, stated against the
exact complex quotient. -/
theorem fl_complexDiv_im_exact_error_le_gamma4 (fp : FPModel)
    (hγ : gammaValid fp 4) (x y : ℂ) (hy : y ≠ 0) :
    |(fl_complexDiv fp x y - x / y).im| ≤
      gamma fp 4 *
        ((|x.im * y.re| + |x.re * y.im|) / Complex.normSq y) := by
  have hDpos : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
  have him :
      (x / y).im =
        (x.im * y.re - x.re * y.im) / Complex.normSq y := by
    rw [Complex.div_im]
    field_simp [hDpos.ne']
  simpa [fl_complexDiv, him] using
    fl_complexDiv_im_error_le_gamma4 fp hγ x y hy

/-- Squared-norm error bound for source complex division. -/
theorem fl_complexDiv_normSq_error_le (fp : FPModel)
    (hγ : gammaValid fp 4) (x y : ℂ) (hy : y ≠ 0) :
    Complex.normSq (fl_complexDiv fp x y - x / y) ≤
      2 * (gamma fp 4) ^ 2 * Complex.normSq (x / y) := by
  let γ := gamma fp 4
  let R := (|x.re * y.re| + |x.im * y.im|) / Complex.normSq y
  let I := (|x.im * y.re| + |x.re * y.im|) / Complex.normSq y
  have hγ_nonneg : 0 ≤ γ := gamma_nonneg fp hγ
  have hDpos : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
  have hR_nonneg : 0 ≤ R := by
    exact div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hDpos.le
  have hI_nonneg : 0 ≤ I := by
    exact div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hDpos.le
  have hre_abs : |(fl_complexDiv fp x y - x / y).re| ≤ γ * R := by
    simpa [γ, R] using fl_complexDiv_re_exact_error_le_gamma4 fp hγ x y hy
  have him_abs : |(fl_complexDiv fp x y - x / y).im| ≤ γ * I := by
    simpa [γ, I] using fl_complexDiv_im_exact_error_le_gamma4 fp hγ x y hy
  have hre_sq :
      (fl_complexDiv fp x y - x / y).re ^ 2 ≤ (γ * R) ^ 2 := by
    exact (sq_le_sq).mpr (by
      simpa [abs_of_nonneg (mul_nonneg hγ_nonneg hR_nonneg)] using hre_abs)
  have him_sq :
      (fl_complexDiv fp x y - x / y).im ^ 2 ≤ (γ * I) ^ 2 := by
    exact (sq_le_sq).mpr (by
      simpa [abs_of_nonneg (mul_nonneg hγ_nonneg hI_nonneg)] using him_abs)
  have hcomp : R ^ 2 + I ^ 2 ≤ 2 * Complex.normSq (x / y) := by
    simpa [R, I] using complex_div_component_abs_terms_sq_le x y hy
  have hsq_terms :
      (fl_complexDiv fp x y - x / y).re ^ 2 +
          (fl_complexDiv fp x y - x / y).im ^ 2 ≤
        γ ^ 2 * (R ^ 2 + I ^ 2) := by
    nlinarith
  have hsq_bound :
      (fl_complexDiv fp x y - x / y).re ^ 2 +
          (fl_complexDiv fp x y - x / y).im ^ 2 ≤
        γ ^ 2 * (2 * Complex.normSq (x / y)) := by
    exact le_trans hsq_terms
      (mul_le_mul_of_nonneg_left hcomp (sq_nonneg γ))
  rw [Complex.normSq_apply]
  nlinarith

/-- Normwise error bound for source complex division. -/
theorem fl_complexDiv_error_bound (fp : FPModel)
    (hγ : gammaValid fp 4) (x y : ℂ) (hy : y ≠ 0) :
    ‖fl_complexDiv fp x y - x / y‖ ≤
      Real.sqrt 2 * gamma fp 4 * ‖x / y‖ := by
  have hsq := fl_complexDiv_normSq_error_le fp hγ x y hy
  have hγ_nonneg : 0 ≤ gamma fp 4 := gamma_nonneg fp hγ
  have hrhs_nonneg : 0 ≤ Real.sqrt 2 * gamma fp 4 * ‖x / y‖ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hγ_nonneg) (norm_nonneg _)
  have hsq_norm :
      ‖fl_complexDiv fp x y - x / y‖ ^ 2 ≤
        (Real.sqrt 2 * gamma fp 4 * ‖x / y‖) ^ 2 := by
    have hrhs_sq :
        (Real.sqrt 2 * gamma fp 4 * ‖x / y‖) ^ 2 =
          2 * (gamma fp 4) ^ 2 * Complex.normSq (x / y) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        ← Complex.normSq_eq_norm_sq]
    rw [← Complex.normSq_eq_norm_sq, hrhs_sq]
    exact hsq
  have habs := sq_le_sq.mp hsq_norm
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs_nonneg,
    abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ)), abs_of_nonneg hγ_nonneg,
    abs_of_nonneg (div_nonneg (norm_nonneg x) (norm_nonneg y)),
    norm_div, mul_assoc] using habs

/-- **Complex division error model** (Higham Chapter 3, Lemma 3.5, division
case for the source formula (3.14c)).

The theorem follows the displayed proof of Lemma 3.5: real numerator and
denominator subexpressions are rounded, and the displayed real quotients are
then bounded in complex relative-error form with radius `sqrt(2) * gamma_4`. -/
theorem fl_complexDiv_rel_error_model (fp : FPModel)
    (hγ : gammaValid fp 4) (x y : ℂ) (hy : y ≠ 0) :
    complexRelErrorModel (fl_complexDiv fp x y) (x / y)
      (Real.sqrt 2 * gamma fp 4) := by
  have hradius_nonneg : 0 ≤ Real.sqrt 2 * gamma fp 4 :=
    mul_nonneg (Real.sqrt_nonneg _) (gamma_nonneg fp hγ)
  exact complexRelErrorModel_of_norm_error_le hradius_nonneg
    (fl_complexDiv_error_bound fp hγ x y hy)

/-! ## Exact Smith branch formulas for overflow-avoiding division -/

/-- Three-operation Smith subexpression bound for
`fl(a + fl(b * fl(c / d)))`.

The quotient, product, and final addition contribute the `gamma_3` budget used
in the overflow-avoiding complex-division analysis. -/
theorem fl_add_mul_div_error_le_gamma3 (fp : FPModel)
    (hγ : gammaValid fp 3) (a b c d : ℝ) (hd : d ≠ 0) :
    |fp.fl_add a (fp.fl_mul b (fp.fl_div c d)) - (a + b * (c / d))| ≤
      gamma fp 3 * (|a| + |b * (c / d)|) := by
  obtain ⟨δd, hδd, hdiv⟩ := fp.model_div c d hd
  obtain ⟨δm, hδm, hmul⟩ := fp.model_mul b (fp.fl_div c d)
  obtain ⟨δa, hδa, hadd⟩ := fp.model_add a (fp.fl_mul b (fp.fl_div c d))
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hγ2 : gammaValid fp 2 := gammaValid_mono fp (by norm_num) hγ
  have hδdγ : |δd| ≤ gamma fp 1 :=
    le_trans hδd (u_le_gamma fp (by norm_num) hγ1)
  have hδmγ : |δm| ≤ gamma fp 1 :=
    le_trans hδm (u_le_gamma fp (by norm_num) hγ1)
  have hδaγ1 : |δa| ≤ gamma fp 1 :=
    le_trans hδa (u_le_gamma fp (by norm_num) hγ1)
  have hδaγ3 : |δa| ≤ gamma fp 3 :=
    le_trans hδaγ1 (gamma_mono fp (by norm_num) hγ)
  obtain ⟨θ2, hθ2, hθ2_eq⟩ :=
    gamma_mul fp 1 1 δd δm hδdγ hδmγ (by simpa using hγ2)
  obtain ⟨θ3, hθ3, hθ3_eq⟩ :=
    gamma_mul fp 2 1 θ2 δa hθ2 hδaγ1 (by simpa using hγ)
  let T : ℝ := b * (c / d)
  have hrewrite :
      fp.fl_add a (fp.fl_mul b (fp.fl_div c d)) - (a + b * (c / d)) =
        a * δa + T * θ3 := by
    rw [hadd, hmul, hdiv]
    change (a + (b * ((c / d) * (1 + δd))) * (1 + δm)) *
        (1 + δa) - (a + T) = a * δa + T * θ3
    have hprod :
        (b * ((c / d) * (1 + δd))) * (1 + δm) =
          T * ((1 + δd) * (1 + δm)) := by
      ring
    rw [hprod, hθ2_eq]
    calc
      (a + T * (1 + θ2)) * (1 + δa) - (a + T)
          = a * δa + T * ((1 + θ2) * (1 + δa) - 1) := by ring
      _ = a * δa + T * θ3 := by
          rw [hθ3_eq]
          ring
  calc
    |fp.fl_add a (fp.fl_mul b (fp.fl_div c d)) - (a + b * (c / d))|
        = |a * δa + T * θ3| := by rw [hrewrite]
    _ ≤ |a * δa| + |T * θ3| := abs_add_le _ _
    _ = |a| * |δa| + |T| * |θ3| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * gamma fp 3 + |T| * gamma fp 3 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hδaγ3 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hθ3 (abs_nonneg _))
    _ = gamma fp 3 * (|a| + |b * (c / d)|) := by
        simp [T]
        ring

/-- Three-operation Smith subexpression bound for
`fl(a - fl(b * fl(c / d)))`. -/
theorem fl_sub_mul_div_error_le_gamma3 (fp : FPModel)
    (hγ : gammaValid fp 3) (a b c d : ℝ) (hd : d ≠ 0) :
    |fp.fl_sub a (fp.fl_mul b (fp.fl_div c d)) - (a - b * (c / d))| ≤
      gamma fp 3 * (|a| + |b * (c / d)|) := by
  obtain ⟨δd, hδd, hdiv⟩ := fp.model_div c d hd
  obtain ⟨δm, hδm, hmul⟩ := fp.model_mul b (fp.fl_div c d)
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub a (fp.fl_mul b (fp.fl_div c d))
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hγ2 : gammaValid fp 2 := gammaValid_mono fp (by norm_num) hγ
  have hδdγ : |δd| ≤ gamma fp 1 :=
    le_trans hδd (u_le_gamma fp (by norm_num) hγ1)
  have hδmγ : |δm| ≤ gamma fp 1 :=
    le_trans hδm (u_le_gamma fp (by norm_num) hγ1)
  have hδsγ1 : |δs| ≤ gamma fp 1 :=
    le_trans hδs (u_le_gamma fp (by norm_num) hγ1)
  have hδsγ3 : |δs| ≤ gamma fp 3 :=
    le_trans hδsγ1 (gamma_mono fp (by norm_num) hγ)
  obtain ⟨θ2, hθ2, hθ2_eq⟩ :=
    gamma_mul fp 1 1 δd δm hδdγ hδmγ (by simpa using hγ2)
  obtain ⟨θ3, hθ3, hθ3_eq⟩ :=
    gamma_mul fp 2 1 θ2 δs hθ2 hδsγ1 (by simpa using hγ)
  let T : ℝ := b * (c / d)
  have hrewrite :
      fp.fl_sub a (fp.fl_mul b (fp.fl_div c d)) - (a - b * (c / d)) =
        a * δs - T * θ3 := by
    rw [hsub, hmul, hdiv]
    change (a - (b * ((c / d) * (1 + δd))) * (1 + δm)) *
        (1 + δs) - (a - T) = a * δs - T * θ3
    have hprod :
        (b * ((c / d) * (1 + δd))) * (1 + δm) =
          T * ((1 + δd) * (1 + δm)) := by
      ring
    rw [hprod, hθ2_eq]
    calc
      (a - T * (1 + θ2)) * (1 + δs) - (a - T)
          = a * δs - T * ((1 + θ2) * (1 + δs) - 1) := by ring
      _ = a * δs - T * θ3 := by
          rw [hθ3_eq]
          ring
  calc
    |fp.fl_sub a (fp.fl_mul b (fp.fl_div c d)) - (a - b * (c / d))|
        = |a * δs - T * θ3| := by rw [hrewrite]
    _ ≤ |a * δs| + |T * θ3| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le (a * δs) (-(T * θ3))
    _ = |a| * |δs| + |T| * |θ3| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * gamma fp 3 + |T| * gamma fp 3 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hδsγ3 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hθ3 (abs_nonneg _))
    _ = gamma fp 3 * (|a| + |b * (c / d)|) := by
        simp [T]
        ring

/-- Three-operation Smith subexpression bound for
`fl(fl(b * fl(c / d)) - a)`. -/
theorem fl_mul_div_sub_error_le_gamma3 (fp : FPModel)
    (hγ : gammaValid fp 3) (a b c d : ℝ) (hd : d ≠ 0) :
    |fp.fl_sub (fp.fl_mul b (fp.fl_div c d)) a - (b * (c / d) - a)| ≤
      gamma fp 3 * (|b * (c / d)| + |a|) := by
  obtain ⟨δd, hδd, hdiv⟩ := fp.model_div c d hd
  obtain ⟨δm, hδm, hmul⟩ := fp.model_mul b (fp.fl_div c d)
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub (fp.fl_mul b (fp.fl_div c d)) a
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hγ2 : gammaValid fp 2 := gammaValid_mono fp (by norm_num) hγ
  have hδdγ : |δd| ≤ gamma fp 1 :=
    le_trans hδd (u_le_gamma fp (by norm_num) hγ1)
  have hδmγ : |δm| ≤ gamma fp 1 :=
    le_trans hδm (u_le_gamma fp (by norm_num) hγ1)
  have hδsγ1 : |δs| ≤ gamma fp 1 :=
    le_trans hδs (u_le_gamma fp (by norm_num) hγ1)
  have hδsγ3 : |δs| ≤ gamma fp 3 :=
    le_trans hδsγ1 (gamma_mono fp (by norm_num) hγ)
  obtain ⟨θ2, hθ2, hθ2_eq⟩ :=
    gamma_mul fp 1 1 δd δm hδdγ hδmγ (by simpa using hγ2)
  obtain ⟨θ3, hθ3, hθ3_eq⟩ :=
    gamma_mul fp 2 1 θ2 δs hθ2 hδsγ1 (by simpa using hγ)
  let T : ℝ := b * (c / d)
  have hrewrite :
      fp.fl_sub (fp.fl_mul b (fp.fl_div c d)) a - (b * (c / d) - a) =
        T * θ3 - a * δs := by
    rw [hsub, hmul, hdiv]
    change ((b * ((c / d) * (1 + δd))) * (1 + δm) - a) *
        (1 + δs) - (T - a) = T * θ3 - a * δs
    have hprod :
        (b * ((c / d) * (1 + δd))) * (1 + δm) =
          T * ((1 + δd) * (1 + δm)) := by
      ring
    rw [hprod, hθ2_eq]
    calc
      (T * (1 + θ2) - a) * (1 + δs) - (T - a)
          = T * ((1 + θ2) * (1 + δs) - 1) - a * δs := by ring
      _ = T * θ3 - a * δs := by
          rw [hθ3_eq]
          ring
  calc
    |fp.fl_sub (fp.fl_mul b (fp.fl_div c d)) a - (b * (c / d) - a)|
        = |T * θ3 - a * δs| := by rw [hrewrite]
    _ ≤ |T * θ3| + |a * δs| := by
        simpa [sub_eq_add_neg, abs_neg, add_comm] using
          abs_add_le (T * θ3) (-(a * δs))
    _ = |T| * |θ3| + |a| * |δs| := by
        rw [abs_mul T θ3, abs_mul a δs]
    _ ≤ |T| * gamma fp 3 + |a| * gamma fp 3 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hθ3 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hδsγ3 (abs_nonneg _))
    _ = gamma fp 3 * (|b * (c / d)| + |a|) := by
        simp [T]
        ring

/-- Exact Smith/Chapter 25 branch using `r = d/c` when the real part of the
denominator is the selected nonzero scale. -/
noncomputable def smithComplexDivBranchCExact (x y : ℂ) : ℂ :=
  let r : ℝ := y.im / y.re
  ⟨(x.re + x.im * r) / (y.re + y.im * r),
    (x.im - x.re * r) / (y.re + y.im * r)⟩

/-- Exact Smith/Chapter 25 branch using `r = c/d` when the imaginary part of
the denominator is the selected nonzero scale. -/
noncomputable def smithComplexDivBranchDExact (x y : ℂ) : ℂ :=
  let r : ℝ := y.re / y.im
  ⟨(x.im + x.re * r) / (y.im + y.re * r),
    (x.im * r - x.re) / (y.im + y.re * r)⟩

/-- Rounded Smith branch ratio `r = fl(d/c)` for the `|c| > |d|` branch. -/
noncomputable def fl_smithComplexDivBranchCRatio (fp : FPModel) (y : ℂ) : ℝ :=
  fp.fl_div y.im y.re

/-- Rounded denominator `fl(c + fl(d*r))` for the `r = fl(d/c)` Smith branch. -/
noncomputable def fl_smithComplexDivBranchCDen (fp : FPModel) (y : ℂ) : ℝ :=
  fp.fl_add y.re (fp.fl_mul y.im (fl_smithComplexDivBranchCRatio fp y))

/-- Rounded real numerator `fl(a + fl(b*r))` for the `r = fl(d/c)` Smith branch. -/
noncomputable def fl_smithComplexDivBranchCNumRe
    (fp : FPModel) (x y : ℂ) : ℝ :=
  fp.fl_add x.re (fp.fl_mul x.im (fl_smithComplexDivBranchCRatio fp y))

/-- Rounded imaginary numerator `fl(b - fl(a*r))` for the `r = fl(d/c)` branch. -/
noncomputable def fl_smithComplexDivBranchCNumIm
    (fp : FPModel) (x y : ℂ) : ℝ :=
  fp.fl_sub x.im (fp.fl_mul x.re (fl_smithComplexDivBranchCRatio fp y))

/-- Rounded Smith/Chapter 25 branch using `r = fl(d/c)`. -/
noncomputable def fl_smithComplexDivBranchC (fp : FPModel) (x y : ℂ) : ℂ :=
  ⟨fp.fl_div (fl_smithComplexDivBranchCNumRe fp x y)
      (fl_smithComplexDivBranchCDen fp y),
    fp.fl_div (fl_smithComplexDivBranchCNumIm fp x y)
      (fl_smithComplexDivBranchCDen fp y)⟩

/-- Rounded Smith branch ratio `r = fl(c/d)` for the `|d| > |c|` branch. -/
noncomputable def fl_smithComplexDivBranchDRatio (fp : FPModel) (y : ℂ) : ℝ :=
  fp.fl_div y.re y.im

/-- Rounded denominator `fl(d + fl(c*r))` for the `r = fl(c/d)` Smith branch. -/
noncomputable def fl_smithComplexDivBranchDDen (fp : FPModel) (y : ℂ) : ℝ :=
  fp.fl_add y.im (fp.fl_mul y.re (fl_smithComplexDivBranchDRatio fp y))

/-- Rounded real numerator `fl(b + fl(a*r))` for the `r = fl(c/d)` Smith branch. -/
noncomputable def fl_smithComplexDivBranchDNumRe
    (fp : FPModel) (x y : ℂ) : ℝ :=
  fp.fl_add x.im (fp.fl_mul x.re (fl_smithComplexDivBranchDRatio fp y))

/-- Rounded imaginary numerator `fl(fl(b*r) - a)` for the `r = fl(c/d)` branch. -/
noncomputable def fl_smithComplexDivBranchDNumIm
    (fp : FPModel) (x y : ℂ) : ℝ :=
  fp.fl_sub (fp.fl_mul x.im (fl_smithComplexDivBranchDRatio fp y)) x.re

/-- Rounded Smith/Chapter 25 branch using `r = fl(c/d)`. -/
noncomputable def fl_smithComplexDivBranchD (fp : FPModel) (x y : ℂ) : ℂ :=
  ⟨fp.fl_div (fl_smithComplexDivBranchDNumRe fp x y)
      (fl_smithComplexDivBranchDDen fp y),
    fp.fl_div (fl_smithComplexDivBranchDNumIm fp x y)
      (fl_smithComplexDivBranchDDen fp y)⟩

/-- Rounded Smith/Chapter 25 overflow-avoiding complex division.

The `c` branch is used when `|d| <= |c|` (including ties); otherwise the `d`
branch is used. -/
noncomputable def fl_smithComplexDiv (fp : FPModel) (x y : ℂ) : ℂ :=
  if |y.im| ≤ |y.re| then
    fl_smithComplexDivBranchC fp x y
  else
    fl_smithComplexDivBranchD fp x y

/-- Denominator subexpression error for the rounded `r = fl(d/c)` Smith
branch. -/
theorem fl_smithComplexDivBranchCDen_error_le_gamma3 (fp : FPModel)
    (hγ : gammaValid fp 3) (y : ℂ) (hyre : y.re ≠ 0) :
    |fl_smithComplexDivBranchCDen fp y - (y.re + y.im * (y.im / y.re))| ≤
      gamma fp 3 * (|y.re| + |y.im * (y.im / y.re)|) := by
  simpa [fl_smithComplexDivBranchCDen, fl_smithComplexDivBranchCRatio] using
    fl_add_mul_div_error_le_gamma3 fp hγ y.re y.im y.im y.re hyre

/-- Real-numerator subexpression error for the rounded `r = fl(d/c)` Smith
branch. -/
theorem fl_smithComplexDivBranchCNumRe_error_le_gamma3 (fp : FPModel)
    (hγ : gammaValid fp 3) (x y : ℂ) (hyre : y.re ≠ 0) :
    |fl_smithComplexDivBranchCNumRe fp x y -
        (x.re + x.im * (y.im / y.re))| ≤
      gamma fp 3 * (|x.re| + |x.im * (y.im / y.re)|) := by
  simpa [fl_smithComplexDivBranchCNumRe, fl_smithComplexDivBranchCRatio] using
    fl_add_mul_div_error_le_gamma3 fp hγ x.re x.im y.im y.re hyre

/-- Imaginary-numerator subexpression error for the rounded `r = fl(d/c)`
Smith branch. -/
theorem fl_smithComplexDivBranchCNumIm_error_le_gamma3 (fp : FPModel)
    (hγ : gammaValid fp 3) (x y : ℂ) (hyre : y.re ≠ 0) :
    |fl_smithComplexDivBranchCNumIm fp x y -
        (x.im - x.re * (y.im / y.re))| ≤
      gamma fp 3 * (|x.im| + |x.re * (y.im / y.re)|) := by
  simpa [fl_smithComplexDivBranchCNumIm, fl_smithComplexDivBranchCRatio] using
    fl_sub_mul_div_error_le_gamma3 fp hγ x.im x.re y.im y.re hyre

/-- Denominator subexpression error for the rounded `r = fl(c/d)` Smith
branch. -/
theorem fl_smithComplexDivBranchDDen_error_le_gamma3 (fp : FPModel)
    (hγ : gammaValid fp 3) (y : ℂ) (hyim : y.im ≠ 0) :
    |fl_smithComplexDivBranchDDen fp y - (y.im + y.re * (y.re / y.im))| ≤
      gamma fp 3 * (|y.im| + |y.re * (y.re / y.im)|) := by
  simpa [fl_smithComplexDivBranchDDen, fl_smithComplexDivBranchDRatio] using
    fl_add_mul_div_error_le_gamma3 fp hγ y.im y.re y.re y.im hyim

/-- Real-numerator subexpression error for the rounded `r = fl(c/d)` Smith
branch. -/
theorem fl_smithComplexDivBranchDNumRe_error_le_gamma3 (fp : FPModel)
    (hγ : gammaValid fp 3) (x y : ℂ) (hyim : y.im ≠ 0) :
    |fl_smithComplexDivBranchDNumRe fp x y -
        (x.im + x.re * (y.re / y.im))| ≤
      gamma fp 3 * (|x.im| + |x.re * (y.re / y.im)|) := by
  simpa [fl_smithComplexDivBranchDNumRe, fl_smithComplexDivBranchDRatio] using
    fl_add_mul_div_error_le_gamma3 fp hγ x.im x.re y.re y.im hyim

/-- Imaginary-numerator subexpression error for the rounded `r = fl(c/d)`
Smith branch. -/
theorem fl_smithComplexDivBranchDNumIm_error_le_gamma3 (fp : FPModel)
    (hγ : gammaValid fp 3) (x y : ℂ) (hyim : y.im ≠ 0) :
    |fl_smithComplexDivBranchDNumIm fp x y -
        (x.im * (y.re / y.im) - x.re)| ≤
      gamma fp 3 * (|x.im * (y.re / y.im)| + |x.re|) := by
  simpa [fl_smithComplexDivBranchDNumIm, fl_smithComplexDivBranchDRatio] using
    fl_mul_div_sub_error_le_gamma3 fp hγ x.re x.im y.re y.im hyim

/-- The exact denominator in the `r = d/c` Smith branch is nonzero whenever
the selected scale `c` is nonzero. -/
theorem smithComplexDivBranchCDen_ne_zero (y : ℂ) (hyre : y.re ≠ 0) :
    y.re + y.im * (y.im / y.re) ≠ 0 := by
  intro hzero
  have hmul :
      (y.re + y.im * (y.im / y.re)) * y.re = y.re ^ 2 + y.im ^ 2 := by
    field_simp [hyre]
  have hsq_zero : y.re ^ 2 + y.im ^ 2 = 0 := by
    rw [← hmul, hzero]
    ring
  have hre_sq_pos : 0 < y.re ^ 2 := sq_pos_of_ne_zero hyre
  have him_sq_nonneg : 0 ≤ y.im ^ 2 := sq_nonneg _
  nlinarith

/-- The exact denominator terms in the `r = d/c` Smith branch have the same
sign, so the denominator absolute value is the sum of absolute terms. -/
theorem smithComplexDivBranchCDen_abs_eq (y : ℂ) (hyre : y.re ≠ 0) :
    |y.re + y.im * (y.im / y.re)| =
      |y.re| + |y.im * (y.im / y.re)| := by
  have hterm_eq : y.im * (y.im / y.re) = y.im ^ 2 / y.re := by ring
  by_cases hre_nonneg : 0 ≤ y.re
  · have hre_pos : 0 < y.re := lt_of_le_of_ne hre_nonneg (Ne.symm hyre)
    have hterm_nonneg : 0 ≤ y.im * (y.im / y.re) := by
      rw [hterm_eq]
      exact div_nonneg (sq_nonneg _) hre_nonneg
    rw [abs_of_nonneg (add_nonneg hre_nonneg hterm_nonneg),
      abs_of_nonneg hre_nonneg, abs_of_nonneg hterm_nonneg]
  · have hre_neg : y.re < 0 := lt_of_not_ge hre_nonneg
    have hre_nonpos : y.re ≤ 0 := le_of_lt hre_neg
    have hterm_nonpos : y.im * (y.im / y.re) ≤ 0 := by
      rw [hterm_eq]
      exact div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hre_nonpos
    rw [abs_of_nonpos (add_nonpos hre_nonpos hterm_nonpos),
      abs_of_nonpos hre_nonpos, abs_of_nonpos hterm_nonpos]
    ring

/-- The exact denominator in the `r = c/d` Smith branch is nonzero whenever
the selected scale `d` is nonzero. -/
theorem smithComplexDivBranchDDen_ne_zero (y : ℂ) (hyim : y.im ≠ 0) :
    y.im + y.re * (y.re / y.im) ≠ 0 := by
  intro hzero
  have hmul :
      (y.im + y.re * (y.re / y.im)) * y.im = y.im ^ 2 + y.re ^ 2 := by
    field_simp [hyim]
  have hsq_zero : y.im ^ 2 + y.re ^ 2 = 0 := by
    rw [← hmul, hzero]
    ring
  have him_sq_pos : 0 < y.im ^ 2 := sq_pos_of_ne_zero hyim
  have hre_sq_nonneg : 0 ≤ y.re ^ 2 := sq_nonneg _
  nlinarith

/-- The exact denominator terms in the `r = c/d` Smith branch have the same
sign, so the denominator absolute value is the sum of absolute terms. -/
theorem smithComplexDivBranchDDen_abs_eq (y : ℂ) (hyim : y.im ≠ 0) :
    |y.im + y.re * (y.re / y.im)| =
      |y.im| + |y.re * (y.re / y.im)| := by
  have hterm_eq : y.re * (y.re / y.im) = y.re ^ 2 / y.im := by ring
  by_cases him_nonneg : 0 ≤ y.im
  · have him_pos : 0 < y.im := lt_of_le_of_ne him_nonneg (Ne.symm hyim)
    have hterm_nonneg : 0 ≤ y.re * (y.re / y.im) := by
      rw [hterm_eq]
      exact div_nonneg (sq_nonneg _) him_nonneg
    rw [abs_of_nonneg (add_nonneg him_nonneg hterm_nonneg),
      abs_of_nonneg him_nonneg, abs_of_nonneg hterm_nonneg]
  · have him_neg : y.im < 0 := lt_of_not_ge him_nonneg
    have him_nonpos : y.im ≤ 0 := le_of_lt him_neg
    have hterm_nonpos : y.re * (y.re / y.im) ≤ 0 := by
      rw [hterm_eq]
      exact div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) him_nonpos
    rw [abs_of_nonpos (add_nonpos him_nonpos hterm_nonpos),
      abs_of_nonpos him_nonpos, abs_of_nonpos hterm_nonpos]
    ring

/-- Real-component `gamma_7` quotient error for the rounded `r = d/c` Smith
branch. -/
theorem fl_smithComplexDivBranchC_re_error_le_gamma7 (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyre : y.re ≠ 0) :
    |(fl_smithComplexDivBranchC fp x y - smithComplexDivBranchCExact x y).re| ≤
      gamma fp 7 *
        ((|x.re| + |x.im * (y.im / y.re)|) /
          |y.re + y.im * (y.im / y.re)|) := by
  let N : ℝ := x.re + x.im * (y.im / y.re)
  let Nhat : ℝ := fl_smithComplexDivBranchCNumRe fp x y
  let D : ℝ := y.re + y.im * (y.im / y.re)
  let Dhat : ℝ := fl_smithComplexDivBranchCDen fp y
  let A : ℝ := |x.re| + |x.im * (y.im / y.re)|
  have hγ3 : gammaValid fp 3 := gammaValid_mono fp (by norm_num) hγ
  have hA_nonneg : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hN_abs : |N| ≤ A := by
    simpa [N, A] using abs_add_le x.re (x.im * (y.im / y.re))
  have hNhat_abs : |Nhat - N| ≤ gamma fp 3 * A := by
    simpa [Nhat, N, A] using
      fl_smithComplexDivBranchCNumRe_error_le_gamma3 fp hγ3 x y hyre
  have hDne : D ≠ 0 := by
    simpa [D] using smithComplexDivBranchCDen_ne_zero y hyre
  have hDhat_abs : |Dhat - D| ≤ gamma fp 3 * |D| := by
    have hraw := fl_smithComplexDivBranchCDen_error_le_gamma3 fp hγ3 y hyre
    have hDabs := smithComplexDivBranchCDen_abs_eq y hyre
    simpa [Dhat, D, hDabs] using hraw
  have h :=
    fl_quotient_abs_error_le_gamma7_of_gamma3_absDen fp hγ hDne
      hA_nonneg hN_abs hNhat_abs hDhat_abs
  simpa [fl_smithComplexDivBranchC, smithComplexDivBranchCExact, Nhat, Dhat,
    N, D, A] using h

/-- Imaginary-component `gamma_7` quotient error for the rounded `r = d/c`
Smith branch. -/
theorem fl_smithComplexDivBranchC_im_error_le_gamma7 (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyre : y.re ≠ 0) :
    |(fl_smithComplexDivBranchC fp x y - smithComplexDivBranchCExact x y).im| ≤
      gamma fp 7 *
        ((|x.im| + |x.re * (y.im / y.re)|) /
          |y.re + y.im * (y.im / y.re)|) := by
  let N : ℝ := x.im - x.re * (y.im / y.re)
  let Nhat : ℝ := fl_smithComplexDivBranchCNumIm fp x y
  let D : ℝ := y.re + y.im * (y.im / y.re)
  let Dhat : ℝ := fl_smithComplexDivBranchCDen fp y
  let A : ℝ := |x.im| + |x.re * (y.im / y.re)|
  have hγ3 : gammaValid fp 3 := gammaValid_mono fp (by norm_num) hγ
  have hA_nonneg : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hN_abs : |N| ≤ A := by
    simpa [N, A, sub_eq_add_neg, abs_neg] using
      abs_add_le x.im (-(x.re * (y.im / y.re)))
  have hNhat_abs : |Nhat - N| ≤ gamma fp 3 * A := by
    simpa [Nhat, N, A] using
      fl_smithComplexDivBranchCNumIm_error_le_gamma3 fp hγ3 x y hyre
  have hDne : D ≠ 0 := by
    simpa [D] using smithComplexDivBranchCDen_ne_zero y hyre
  have hDhat_abs : |Dhat - D| ≤ gamma fp 3 * |D| := by
    have hraw := fl_smithComplexDivBranchCDen_error_le_gamma3 fp hγ3 y hyre
    have hDabs := smithComplexDivBranchCDen_abs_eq y hyre
    simpa [Dhat, D, hDabs] using hraw
  have h :=
    fl_quotient_abs_error_le_gamma7_of_gamma3_absDen fp hγ hDne
      hA_nonneg hN_abs hNhat_abs hDhat_abs
  simpa [fl_smithComplexDivBranchC, smithComplexDivBranchCExact, Nhat, Dhat,
    N, D, A] using h

/-- Real-component `gamma_7` quotient error for the rounded `r = c/d` Smith
branch. -/
theorem fl_smithComplexDivBranchD_re_error_le_gamma7 (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyim : y.im ≠ 0) :
    |(fl_smithComplexDivBranchD fp x y - smithComplexDivBranchDExact x y).re| ≤
      gamma fp 7 *
        ((|x.im| + |x.re * (y.re / y.im)|) /
          |y.im + y.re * (y.re / y.im)|) := by
  let N : ℝ := x.im + x.re * (y.re / y.im)
  let Nhat : ℝ := fl_smithComplexDivBranchDNumRe fp x y
  let D : ℝ := y.im + y.re * (y.re / y.im)
  let Dhat : ℝ := fl_smithComplexDivBranchDDen fp y
  let A : ℝ := |x.im| + |x.re * (y.re / y.im)|
  have hγ3 : gammaValid fp 3 := gammaValid_mono fp (by norm_num) hγ
  have hA_nonneg : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hN_abs : |N| ≤ A := by
    simpa [N, A] using abs_add_le x.im (x.re * (y.re / y.im))
  have hNhat_abs : |Nhat - N| ≤ gamma fp 3 * A := by
    simpa [Nhat, N, A] using
      fl_smithComplexDivBranchDNumRe_error_le_gamma3 fp hγ3 x y hyim
  have hDne : D ≠ 0 := by
    simpa [D] using smithComplexDivBranchDDen_ne_zero y hyim
  have hDhat_abs : |Dhat - D| ≤ gamma fp 3 * |D| := by
    have hraw := fl_smithComplexDivBranchDDen_error_le_gamma3 fp hγ3 y hyim
    have hDabs := smithComplexDivBranchDDen_abs_eq y hyim
    simpa [Dhat, D, hDabs] using hraw
  have h :=
    fl_quotient_abs_error_le_gamma7_of_gamma3_absDen fp hγ hDne
      hA_nonneg hN_abs hNhat_abs hDhat_abs
  simpa [fl_smithComplexDivBranchD, smithComplexDivBranchDExact, Nhat, Dhat,
    N, D, A] using h

/-- Imaginary-component `gamma_7` quotient error for the rounded `r = c/d`
Smith branch. -/
theorem fl_smithComplexDivBranchD_im_error_le_gamma7 (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyim : y.im ≠ 0) :
    |(fl_smithComplexDivBranchD fp x y - smithComplexDivBranchDExact x y).im| ≤
      gamma fp 7 *
        ((|x.im * (y.re / y.im)| + |x.re|) /
          |y.im + y.re * (y.re / y.im)|) := by
  let N : ℝ := x.im * (y.re / y.im) - x.re
  let Nhat : ℝ := fl_smithComplexDivBranchDNumIm fp x y
  let D : ℝ := y.im + y.re * (y.re / y.im)
  let Dhat : ℝ := fl_smithComplexDivBranchDDen fp y
  let A : ℝ := |x.im * (y.re / y.im)| + |x.re|
  have hγ3 : gammaValid fp 3 := gammaValid_mono fp (by norm_num) hγ
  have hA_nonneg : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hN_abs : |N| ≤ A := by
    simpa [N, A, sub_eq_add_neg, abs_neg] using
      abs_add_le (x.im * (y.re / y.im)) (-x.re)
  have hNhat_abs : |Nhat - N| ≤ gamma fp 3 * A := by
    simpa [Nhat, N, A] using
      fl_smithComplexDivBranchDNumIm_error_le_gamma3 fp hγ3 x y hyim
  have hDne : D ≠ 0 := by
    simpa [D] using smithComplexDivBranchDDen_ne_zero y hyim
  have hDhat_abs : |Dhat - D| ≤ gamma fp 3 * |D| := by
    have hraw := fl_smithComplexDivBranchDDen_error_le_gamma3 fp hγ3 y hyim
    have hDabs := smithComplexDivBranchDDen_abs_eq y hyim
    simpa [Dhat, D, hDabs] using hraw
  have h :=
    fl_quotient_abs_error_le_gamma7_of_gamma3_absDen fp hγ hDne
      hA_nonneg hN_abs hNhat_abs hDhat_abs
  simpa [fl_smithComplexDivBranchD, smithComplexDivBranchDExact, Nhat, Dhat,
    N, D, A] using h

/-- Exact algebra behind Higham Chapter 25 formula (25.1):
if `c = Re y` is nonzero and `r = d/c`, then Smith's `c⁻¹` branch equals the
ordinary complex quotient. -/
theorem smithComplexDivBranchCExact_eq_div
    (x y : ℂ) (hyre : y.re ≠ 0) :
    smithComplexDivBranchCExact x y = x / y := by
  apply Complex.ext
  · simp [smithComplexDivBranchCExact]
    rw [Complex.div_re]
    rw [Complex.normSq_apply]
    field_simp [hyre]
  · simp [smithComplexDivBranchCExact]
    rw [Complex.div_im]
    rw [Complex.normSq_apply]
    field_simp [hyre]

/-- Exact algebra behind the companion Smith branch:
if `d = Im y` is nonzero and `r = c/d`, then the `d⁻¹` branch equals the
ordinary complex quotient. -/
theorem smithComplexDivBranchDExact_eq_div
    (x y : ℂ) (hyim : y.im ≠ 0) :
    smithComplexDivBranchDExact x y = x / y := by
  apply Complex.ext
  · simp [smithComplexDivBranchDExact]
    rw [Complex.div_re]
    rw [Complex.normSq_apply]
    field_simp [hyim]
    ring_nf
  · simp [smithComplexDivBranchDExact]
    rw [Complex.div_im]
    rw [Complex.normSq_apply]
    field_simp [hyim]
    ring_nf

/-! ## Normwise Smith overflow-avoiding division bounds -/

/-- The real-part Smith `r = d/c` component majorant is the ordinary division
component majorant from Lemma 3.5. -/
theorem smithComplexDivBranchC_re_majorant_eq (x y : ℂ) (hyre : y.re ≠ 0) :
    (|x.re| + |x.im * (y.im / y.re)|) /
        |y.re + y.im * (y.im / y.re)| =
      (|x.re * y.re| + |x.im * y.im|) / Complex.normSq y := by
  have hy : y ≠ 0 := by
    intro h
    exact hyre (by simp [h])
  have hnorm_pos : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
  have hyre_abs_ne : |y.re| ≠ 0 := abs_ne_zero.mpr hyre
  have hden_abs :
      |y.re + y.im * (y.im / y.re)| = Complex.normSq y / |y.re| := by
    rw [smithComplexDivBranchCDen_abs_eq y hyre]
    rw [abs_mul, abs_div]
    field_simp [hyre_abs_ne, Complex.normSq_apply]
    rw [sq_abs y.re, sq_abs y.im, Complex.normSq_apply]
    ring
  have hnum :
      |x.re| + |x.im * (y.im / y.re)| =
        (|x.re * y.re| + |x.im * y.im|) / |y.re| := by
    rw [abs_mul, abs_div]
    field_simp [hyre_abs_ne]
    rw [abs_mul x.re y.re, abs_mul x.im y.im]
  rw [hden_abs, hnum]
  field_simp [hyre_abs_ne, hnorm_pos.ne']

/-- The imaginary-part Smith `r = d/c` component majorant is the ordinary
division component majorant from Lemma 3.5. -/
theorem smithComplexDivBranchC_im_majorant_eq (x y : ℂ) (hyre : y.re ≠ 0) :
    (|x.im| + |x.re * (y.im / y.re)|) /
        |y.re + y.im * (y.im / y.re)| =
      (|x.im * y.re| + |x.re * y.im|) / Complex.normSq y := by
  have hy : y ≠ 0 := by
    intro h
    exact hyre (by simp [h])
  have hnorm_pos : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
  have hyre_abs_ne : |y.re| ≠ 0 := abs_ne_zero.mpr hyre
  have hden_abs :
      |y.re + y.im * (y.im / y.re)| = Complex.normSq y / |y.re| := by
    rw [smithComplexDivBranchCDen_abs_eq y hyre]
    rw [abs_mul, abs_div]
    field_simp [hyre_abs_ne, Complex.normSq_apply]
    rw [sq_abs y.re, sq_abs y.im, Complex.normSq_apply]
    ring
  have hnum :
      |x.im| + |x.re * (y.im / y.re)| =
        (|x.im * y.re| + |x.re * y.im|) / |y.re| := by
    rw [abs_mul, abs_div]
    field_simp [hyre_abs_ne]
    rw [abs_mul x.im y.re, abs_mul x.re y.im]
  rw [hden_abs, hnum]
  field_simp [hyre_abs_ne, hnorm_pos.ne']

/-- The real-part Smith `r = c/d` component majorant is the ordinary division
component majorant from Lemma 3.5. -/
theorem smithComplexDivBranchD_re_majorant_eq (x y : ℂ) (hyim : y.im ≠ 0) :
    (|x.im| + |x.re * (y.re / y.im)|) /
        |y.im + y.re * (y.re / y.im)| =
      (|x.re * y.re| + |x.im * y.im|) / Complex.normSq y := by
  have hy : y ≠ 0 := by
    intro h
    exact hyim (by simp [h])
  have hnorm_pos : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
  have hyim_abs_ne : |y.im| ≠ 0 := abs_ne_zero.mpr hyim
  have hden_abs :
      |y.im + y.re * (y.re / y.im)| = Complex.normSq y / |y.im| := by
    rw [smithComplexDivBranchDDen_abs_eq y hyim]
    rw [abs_mul, abs_div]
    field_simp [hyim_abs_ne, Complex.normSq_apply]
    rw [sq_abs y.im, sq_abs y.re, Complex.normSq_apply]
    ring
  have hnum :
      |x.im| + |x.re * (y.re / y.im)| =
        (|x.im * y.im| + |x.re * y.re|) / |y.im| := by
    rw [abs_mul, abs_div]
    field_simp [hyim_abs_ne]
    rw [abs_mul x.im y.im, abs_mul x.re y.re]
  rw [hden_abs, hnum]
  rw [add_comm (|x.im * y.im|) (|x.re * y.re|)]
  field_simp [hyim_abs_ne, hnorm_pos.ne']

/-- The imaginary-part Smith `r = c/d` component majorant is the ordinary
division component majorant from Lemma 3.5. -/
theorem smithComplexDivBranchD_im_majorant_eq (x y : ℂ) (hyim : y.im ≠ 0) :
    (|x.im * (y.re / y.im)| + |x.re|) /
        |y.im + y.re * (y.re / y.im)| =
      (|x.im * y.re| + |x.re * y.im|) / Complex.normSq y := by
  have hy : y ≠ 0 := by
    intro h
    exact hyim (by simp [h])
  have hnorm_pos : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
  have hyim_abs_ne : |y.im| ≠ 0 := abs_ne_zero.mpr hyim
  have hden_abs :
      |y.im + y.re * (y.re / y.im)| = Complex.normSq y / |y.im| := by
    rw [smithComplexDivBranchDDen_abs_eq y hyim]
    rw [abs_mul, abs_div]
    field_simp [hyim_abs_ne, Complex.normSq_apply]
    rw [sq_abs y.im, sq_abs y.re, Complex.normSq_apply]
    ring
  have hnum :
      |x.im * (y.re / y.im)| + |x.re| =
        (|x.im * y.re| + |x.re * y.im|) / |y.im| := by
    rw [abs_mul, abs_div]
    field_simp [hyim_abs_ne]
    rw [abs_mul x.im y.re, abs_mul x.re y.im]
    ring
  rw [hden_abs, hnum]
  field_simp [hyim_abs_ne, hnorm_pos.ne']

/-- Squared-norm error bound for the rounded `r = d/c` Smith branch. -/
theorem fl_smithComplexDivBranchC_normSq_error_le (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyre : y.re ≠ 0) :
    Complex.normSq (fl_smithComplexDivBranchC fp x y - x / y) ≤
      2 * (gamma fp 7) ^ 2 * Complex.normSq (x / y) := by
  let γ := gamma fp 7
  let R := (|x.re| + |x.im * (y.im / y.re)|) /
    |y.re + y.im * (y.im / y.re)|
  let I := (|x.im| + |x.re * (y.im / y.re)|) /
    |y.re + y.im * (y.im / y.re)|
  have hy : y ≠ 0 := by
    intro h
    exact hyre (by simp [h])
  have hγ_nonneg : 0 ≤ γ := gamma_nonneg fp hγ
  have hDabs_nonneg : 0 ≤ |y.re + y.im * (y.im / y.re)| := abs_nonneg _
  have hR_nonneg : 0 ≤ R :=
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hDabs_nonneg
  have hI_nonneg : 0 ≤ I :=
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hDabs_nonneg
  have hExact := smithComplexDivBranchCExact_eq_div x y hyre
  have hre_abs :
      |(fl_smithComplexDivBranchC fp x y - x / y).re| ≤ γ * R := by
    simpa [γ, R, ← hExact] using
      fl_smithComplexDivBranchC_re_error_le_gamma7 fp hγ x y hyre
  have him_abs :
      |(fl_smithComplexDivBranchC fp x y - x / y).im| ≤ γ * I := by
    simpa [γ, I, ← hExact] using
      fl_smithComplexDivBranchC_im_error_le_gamma7 fp hγ x y hyre
  have hre_sq :
      (fl_smithComplexDivBranchC fp x y - x / y).re ^ 2 ≤ (γ * R) ^ 2 := by
    exact (sq_le_sq).mpr (by
      simpa [abs_of_nonneg (mul_nonneg hγ_nonneg hR_nonneg)] using hre_abs)
  have him_sq :
      (fl_smithComplexDivBranchC fp x y - x / y).im ^ 2 ≤ (γ * I) ^ 2 := by
    exact (sq_le_sq).mpr (by
      simpa [abs_of_nonneg (mul_nonneg hγ_nonneg hI_nonneg)] using him_abs)
  have hcomp : R ^ 2 + I ^ 2 ≤ 2 * Complex.normSq (x / y) := by
    have hsource := complex_div_component_abs_terms_sq_le x y hy
    have hR := smithComplexDivBranchC_re_majorant_eq x y hyre
    have hI := smithComplexDivBranchC_im_majorant_eq x y hyre
    simpa [R, I, hR, hI] using hsource
  have hsq_terms :
      (fl_smithComplexDivBranchC fp x y - x / y).re ^ 2 +
          (fl_smithComplexDivBranchC fp x y - x / y).im ^ 2 ≤
        γ ^ 2 * (R ^ 2 + I ^ 2) := by
    nlinarith
  have hsq_bound :
      (fl_smithComplexDivBranchC fp x y - x / y).re ^ 2 +
          (fl_smithComplexDivBranchC fp x y - x / y).im ^ 2 ≤
        γ ^ 2 * (2 * Complex.normSq (x / y)) := by
    exact le_trans hsq_terms
      (mul_le_mul_of_nonneg_left hcomp (sq_nonneg γ))
  rw [Complex.normSq_apply]
  nlinarith

/-- Normwise error bound for the rounded `r = d/c` Smith branch. -/
theorem fl_smithComplexDivBranchC_error_bound (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyre : y.re ≠ 0) :
    ‖fl_smithComplexDivBranchC fp x y - x / y‖ ≤
      Real.sqrt 2 * gamma fp 7 * ‖x / y‖ := by
  have hsq := fl_smithComplexDivBranchC_normSq_error_le fp hγ x y hyre
  have hγ_nonneg : 0 ≤ gamma fp 7 := gamma_nonneg fp hγ
  have hrhs_nonneg : 0 ≤ Real.sqrt 2 * gamma fp 7 * ‖x / y‖ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hγ_nonneg) (norm_nonneg _)
  have hsq_norm :
      ‖fl_smithComplexDivBranchC fp x y - x / y‖ ^ 2 ≤
        (Real.sqrt 2 * gamma fp 7 * ‖x / y‖) ^ 2 := by
    have hrhs_sq :
        (Real.sqrt 2 * gamma fp 7 * ‖x / y‖) ^ 2 =
          2 * (gamma fp 7) ^ 2 * Complex.normSq (x / y) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        ← Complex.normSq_eq_norm_sq]
    rw [← Complex.normSq_eq_norm_sq, hrhs_sq]
    exact hsq
  have habs := sq_le_sq.mp hsq_norm
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs_nonneg,
    abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ)), abs_of_nonneg hγ_nonneg,
    abs_of_nonneg (div_nonneg (norm_nonneg x) (norm_nonneg y)),
    norm_div, mul_assoc] using habs

/-- Relative-error model for the rounded `r = d/c` Smith branch. -/
theorem fl_smithComplexDivBranchC_rel_error_model (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyre : y.re ≠ 0) :
    complexRelErrorModel (fl_smithComplexDivBranchC fp x y) (x / y)
      (Real.sqrt 2 * gamma fp 7) := by
  have hradius_nonneg : 0 ≤ Real.sqrt 2 * gamma fp 7 :=
    mul_nonneg (Real.sqrt_nonneg _) (gamma_nonneg fp hγ)
  exact complexRelErrorModel_of_norm_error_le hradius_nonneg
    (fl_smithComplexDivBranchC_error_bound fp hγ x y hyre)

/-- Squared-norm error bound for the rounded `r = c/d` Smith branch. -/
theorem fl_smithComplexDivBranchD_normSq_error_le (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyim : y.im ≠ 0) :
    Complex.normSq (fl_smithComplexDivBranchD fp x y - x / y) ≤
      2 * (gamma fp 7) ^ 2 * Complex.normSq (x / y) := by
  let γ := gamma fp 7
  let R := (|x.im| + |x.re * (y.re / y.im)|) /
    |y.im + y.re * (y.re / y.im)|
  let I := (|x.im * (y.re / y.im)| + |x.re|) /
    |y.im + y.re * (y.re / y.im)|
  have hy : y ≠ 0 := by
    intro h
    exact hyim (by simp [h])
  have hγ_nonneg : 0 ≤ γ := gamma_nonneg fp hγ
  have hDabs_nonneg : 0 ≤ |y.im + y.re * (y.re / y.im)| := abs_nonneg _
  have hR_nonneg : 0 ≤ R :=
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hDabs_nonneg
  have hI_nonneg : 0 ≤ I :=
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hDabs_nonneg
  have hExact := smithComplexDivBranchDExact_eq_div x y hyim
  have hre_abs :
      |(fl_smithComplexDivBranchD fp x y - x / y).re| ≤ γ * R := by
    simpa [γ, R, ← hExact] using
      fl_smithComplexDivBranchD_re_error_le_gamma7 fp hγ x y hyim
  have him_abs :
      |(fl_smithComplexDivBranchD fp x y - x / y).im| ≤ γ * I := by
    simpa [γ, I, ← hExact] using
      fl_smithComplexDivBranchD_im_error_le_gamma7 fp hγ x y hyim
  have hre_sq :
      (fl_smithComplexDivBranchD fp x y - x / y).re ^ 2 ≤ (γ * R) ^ 2 := by
    exact (sq_le_sq).mpr (by
      simpa [abs_of_nonneg (mul_nonneg hγ_nonneg hR_nonneg)] using hre_abs)
  have him_sq :
      (fl_smithComplexDivBranchD fp x y - x / y).im ^ 2 ≤ (γ * I) ^ 2 := by
    exact (sq_le_sq).mpr (by
      simpa [abs_of_nonneg (mul_nonneg hγ_nonneg hI_nonneg)] using him_abs)
  have hcomp : R ^ 2 + I ^ 2 ≤ 2 * Complex.normSq (x / y) := by
    have hsource := complex_div_component_abs_terms_sq_le x y hy
    have hR := smithComplexDivBranchD_re_majorant_eq x y hyim
    have hI := smithComplexDivBranchD_im_majorant_eq x y hyim
    simpa [R, I, hR, hI] using hsource
  have hsq_terms :
      (fl_smithComplexDivBranchD fp x y - x / y).re ^ 2 +
          (fl_smithComplexDivBranchD fp x y - x / y).im ^ 2 ≤
        γ ^ 2 * (R ^ 2 + I ^ 2) := by
    nlinarith
  have hsq_bound :
      (fl_smithComplexDivBranchD fp x y - x / y).re ^ 2 +
          (fl_smithComplexDivBranchD fp x y - x / y).im ^ 2 ≤
        γ ^ 2 * (2 * Complex.normSq (x / y)) := by
    exact le_trans hsq_terms
      (mul_le_mul_of_nonneg_left hcomp (sq_nonneg γ))
  rw [Complex.normSq_apply]
  nlinarith

/-- Normwise error bound for the rounded `r = c/d` Smith branch. -/
theorem fl_smithComplexDivBranchD_error_bound (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyim : y.im ≠ 0) :
    ‖fl_smithComplexDivBranchD fp x y - x / y‖ ≤
      Real.sqrt 2 * gamma fp 7 * ‖x / y‖ := by
  have hsq := fl_smithComplexDivBranchD_normSq_error_le fp hγ x y hyim
  have hγ_nonneg : 0 ≤ gamma fp 7 := gamma_nonneg fp hγ
  have hrhs_nonneg : 0 ≤ Real.sqrt 2 * gamma fp 7 * ‖x / y‖ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hγ_nonneg) (norm_nonneg _)
  have hsq_norm :
      ‖fl_smithComplexDivBranchD fp x y - x / y‖ ^ 2 ≤
        (Real.sqrt 2 * gamma fp 7 * ‖x / y‖) ^ 2 := by
    have hrhs_sq :
        (Real.sqrt 2 * gamma fp 7 * ‖x / y‖) ^ 2 =
          2 * (gamma fp 7) ^ 2 * Complex.normSq (x / y) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        ← Complex.normSq_eq_norm_sq]
    rw [← Complex.normSq_eq_norm_sq, hrhs_sq]
    exact hsq
  have habs := sq_le_sq.mp hsq_norm
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs_nonneg,
    abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ)), abs_of_nonneg hγ_nonneg,
    abs_of_nonneg (div_nonneg (norm_nonneg x) (norm_nonneg y)),
    norm_div, mul_assoc] using habs

/-- Relative-error model for the rounded `r = c/d` Smith branch. -/
theorem fl_smithComplexDivBranchD_rel_error_model (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hyim : y.im ≠ 0) :
    complexRelErrorModel (fl_smithComplexDivBranchD fp x y) (x / y)
      (Real.sqrt 2 * gamma fp 7) := by
  have hradius_nonneg : 0 ≤ Real.sqrt 2 * gamma fp 7 :=
    mul_nonneg (Real.sqrt_nonneg _) (gamma_nonneg fp hγ)
  exact complexRelErrorModel_of_norm_error_le hradius_nonneg
    (fl_smithComplexDivBranchD_error_bound fp hγ x y hyim)

/-- Normwise error bound for rounded Smith overflow-avoiding complex division.

This is the source page-80 `sqrt(2) * gamma_7` statement for the practical
formula (25.1), with the `c` branch used on ties. -/
theorem fl_smithComplexDiv_error_bound (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hy : y ≠ 0) :
    ‖fl_smithComplexDiv fp x y - x / y‖ ≤
      Real.sqrt 2 * gamma fp 7 * ‖x / y‖ := by
  unfold fl_smithComplexDiv
  by_cases hbranch : |y.im| ≤ |y.re|
  · have hyre : y.re ≠ 0 := by
      intro hre
      have him_abs_zero : |y.im| = 0 :=
        le_antisymm (by simpa [hre] using hbranch) (abs_nonneg _)
      have him : y.im = 0 := abs_eq_zero.mp him_abs_zero
      have hyzero : y = 0 := by
        apply Complex.ext <;> simp [hre, him]
      exact hy hyzero
    simpa [hbranch] using
      fl_smithComplexDivBranchC_error_bound fp hγ x y hyre
  · have hyim : y.im ≠ 0 := by
      intro him
      exact hbranch (by simp [him])
    simpa [hbranch] using
      fl_smithComplexDivBranchD_error_bound fp hγ x y hyim

/-- **Smith overflow-avoiding complex division error model** (Higham Chapter 3,
Lemma 3.5 page-80 note, using Chapter 25 formula (25.1)).

For every nonzero divisor, the rounded Smith branch implementation satisfies
the complex relative-error model with radius `sqrt(2) * gamma_7`. -/
theorem fl_smithComplexDiv_rel_error_model (fp : FPModel)
    (hγ : gammaValid fp 7) (x y : ℂ) (hy : y ≠ 0) :
    complexRelErrorModel (fl_smithComplexDiv fp x y) (x / y)
      (Real.sqrt 2 * gamma fp 7) := by
  have hradius_nonneg : 0 ≤ Real.sqrt 2 * gamma fp 7 :=
    mul_nonneg (Real.sqrt_nonneg _) (gamma_nonneg fp hγ)
  exact complexRelErrorModel_of_norm_error_le hradius_nonneg
    (fl_smithComplexDiv_error_bound fp hγ x y hy)

end NumStability
