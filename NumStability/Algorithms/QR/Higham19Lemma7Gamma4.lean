-- Algorithms/QR/Higham19Lemma7Gamma4.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms (2nd ed.),
-- §19.3, Lemma 19.7, eq. (19.24), p. 366 (and the identical coefficient count
-- in §18.5, Lemma 18.6): the computed Givens coefficients from the construction
-- eq. (19.23)
--
--     c = x_i / sqrt(x_i^2 + x_j^2),   s = x_j / sqrt(x_i^2 + x_j^2)
--
-- satisfy  c_hat = c (1 + theta_4),  s_hat = s (1 + theta_4'),  with
-- |theta_4|, |theta_4'| <= gamma_4.
--
-- This file proves the PRINTED gamma_4 relative-error constant for the concrete
-- repository kernels `fl_givensC` / `fl_givensS` (GivensSpec.lean), improving on
-- the conservative `gamma_6` bound of `fl_givensCoeffError_conservative`.
--
-- The improvement from gamma_6 to gamma_4 is obtained by NOT collapsing the
-- rounded square root into a plain gamma-bounded relative factor and then
-- inverting it (which, via the rigorous reciprocal rule `gamma_inv`, doubles the
-- index k -> 2k and forces gamma_6).  Instead the analysis keeps the two
-- rounding factors that arise from the rounded division as a Stewart
-- relative-error counter <2> (Higham eq. (3.10), same-index reciprocal rule),
-- and bounds the residual inverse-square-root factor at its OWN index using the
-- bespoke real-analysis inequality `abs_inv_sqrt_one_add_sub_one_le`
-- (|1/sqrt(1+t) - 1| <= |t|).  The two gamma_2 factors then combine via
-- `gamma_mul` to gamma_4, matching the printed constant.
--
-- Constant honesty (per Higham p. 357, the integer c in gamma-tilde is left
-- unspecified): the index 4 here is the exact integer index of the repository
-- `gamma` function `gamma fp k = k*u / (1 - k*u)`, proved for the concrete
-- kernel; it is the same integer as Higham's printed gamma_4.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.Norm2
import NumStability.Algorithms.QR.GivensSpec

namespace NumStability.Wave13

open NumStability

-- ============================================================
-- Bespoke real-analysis inequality for the inverse square root
-- ============================================================

/-- Inverse-square-root perturbation bound (exact real-analysis lemma, not a
    floating-point assumption).

    If `0 < 1 + t` and `0 ≤ 1 + t - t^2`, then
    `|1 / sqrt(1 + t) - 1| ≤ |t|`.

    This is the key inequality allowing Higham's Lemma 19.7 (§19.3, eq. (19.24),
    p. 366) coefficient error to stay at index `2` for the square-root factor
    instead of doubling to index `4` under the general reciprocal rule.  The side
    condition `0 ≤ 1 + t - t^2` holds for any `|t| ≤ 1/2` (in particular for
    `|t| ≤ gamma fp 2 ≤ 1/2`). -/
theorem abs_inv_sqrt_one_add_sub_one_le {t : ℝ}
    (hpos : (0 : ℝ) < 1 + t) (hq : (0 : ℝ) ≤ 1 + t - t ^ 2) :
    |1 / Real.sqrt (1 + t) - 1| ≤ |t| := by
  have hsqrt_pos : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr hpos
  have hsqrt_sq : Real.sqrt (1 + t) ^ 2 = 1 + t := Real.sq_sqrt (le_of_lt hpos)
  by_cases hnonneg : 0 ≤ t
  · -- t ≥ 0: 1/sqrt(1+t) ≤ 1 and ≥ 1 - t
    have hroot_ge_one : 1 ≤ Real.sqrt (1 + t) := by
      rw [Real.one_le_sqrt]; linarith
    have hinv_le_one : 1 / Real.sqrt (1 + t) ≤ 1 := by
      rw [div_le_one hsqrt_pos]; exact hroot_ge_one
    -- lower bound: 1 - t ≤ 1/sqrt(1+t)
    have hlow : 1 - t ≤ 1 / Real.sqrt (1 + t) := by
      by_cases ht1 : 1 ≤ t
      · have : (1 : ℝ) - t ≤ 0 := by linarith
        exact le_trans this (le_of_lt (div_pos one_pos hsqrt_pos))
      · -- 0 ≤ t < 1: (1 - t) * sqrt(1+t) ≤ 1
        have hmul : (1 - t) * Real.sqrt (1 + t) ≤ 1 := by
          nlinarith [Real.sq_sqrt (le_of_lt hpos), hsqrt_pos, hnonneg,
            sq_nonneg (Real.sqrt (1 + t) - 1),
            mul_nonneg hnonneg (le_of_lt hsqrt_pos)]
        rw [le_div_iff₀ hsqrt_pos]; linarith [hmul]
    rw [abs_of_nonneg hnonneg]
    rw [abs_le]
    constructor <;> linarith
  · -- t < 0: 1/sqrt(1+t) ≥ 1 and ≤ 1 - t
    have hneg : t < 0 := lt_of_not_ge hnonneg
    have hroot_le_one : Real.sqrt (1 + t) ≤ 1 := by
      rw [Real.sqrt_le_one]; linarith
    have hinv_ge_one : 1 ≤ 1 / Real.sqrt (1 + t) := by
      rw [le_div_iff₀ hsqrt_pos]; linarith [hroot_le_one]
    -- upper bound: 1/sqrt(1+t) ≤ 1 - t
    have hupp : 1 / Real.sqrt (1 + t) ≤ 1 - t := by
      have hfac_pos : 0 < 1 - t := by linarith
      -- 1 ≤ (1 - t) * sqrt(1+t)  ⟸  1 ≤ (1-t)^2 (1+t)
      have hkey : (1 : ℝ) ≤ ((1 - t) * Real.sqrt (1 + t)) := by
        have hsq : (1 : ℝ) ≤ ((1 - t) * Real.sqrt (1 + t)) ^ 2 := by
          have : ((1 - t) * Real.sqrt (1 + t)) ^ 2 = (1 - t) ^ 2 * (1 + t) := by
            rw [mul_pow, hsqrt_sq]
          rw [this]
          nlinarith [hq, hneg, sq_nonneg t]
        nlinarith [mul_nonneg (le_of_lt hfac_pos) (le_of_lt hsqrt_pos), hsq]
      rw [div_le_iff₀ hsqrt_pos]
      nlinarith [hkey]
    rw [abs_of_neg hneg]
    rw [abs_le]
    constructor <;> linarith

-- ============================================================
-- Stewart-counter form of the rounded-division perturbation
-- ============================================================

/-- The pair (final rounded division roundoff `δ'`) / (rounded square-root
    roundoff `δ`) is a Stewart relative-error counter `<2>` (Higham eq. (3.10)),
    hence bounded by `gamma fp 2`.

    This is the same-index accounting that keeps the two primitive roundings of
    the division step from inflating the index, unlike the general reciprocal
    rule. -/
theorem div_roundoff_pair_abs_sub_one_le (fp : FPModel) (δ' δ : ℝ)
    (hδ' : |δ'| ≤ fp.u) (hδ : |δ| ≤ fp.u) (hu : fp.u < 1)
    (hval2 : gammaValid fp 2) :
    |(1 + δ') * (1 / (1 + δ)) - 1| ≤ gamma fp 2 := by
  have hnum : relErrorCounter fp 1 (1 + δ') := by
    refine ⟨fun _ => δ', fun _ => false, ?_, ?_⟩
    · intro i; simpa using hδ'
    · simp
  have hden : relErrorCounter fp 1 (1 + δ) := by
    refine ⟨fun _ => δ, fun _ => false, ?_, ?_⟩
    · intro i; simpa using hδ
    · simp
  have hden_inv : relErrorCounter fp 1 (1 / (1 + δ)) :=
    relErrorCounter_inv fp 1 (1 + δ) hden hu
  have hpair : relErrorCounter fp 2 ((1 + δ') * (1 / (1 + δ))) := by
    have := relErrorCounter_mul fp 1 1 (1 + δ') (1 / (1 + δ)) hnum hden_inv
    simpa using this
  simpa using
    relErrorCounter_abs_sub_one_le_gamma fp 2 ((1 + δ') * (1 / (1 + δ))) hpair hval2

-- ============================================================
-- gamma_2 ≤ 1/2 side facts under `gammaValid fp 6`
-- ============================================================

/-- Under `gammaValid fp 6` the second-order gamma constant is at most `1/2`.

    This is the smallness regime that makes the inverse-square-root side
    condition `0 ≤ 1 + t - t^2` hold for any `|t| ≤ gamma fp 2`. -/
theorem gamma_two_le_half (fp : FPModel) (hval6 : gammaValid fp 6) :
    gamma fp 2 ≤ 1 / 2 := by
  have h6u : (6 : ℝ) * fp.u < 1 := by
    have := hval6; unfold gammaValid at this; push_cast at this; linarith
  have hu_nonneg : 0 ≤ fp.u := fp.u_nonneg
  have h2u_lt : (2 : ℝ) * fp.u < 1 := by linarith
  have hden_pos : 0 < 1 - 2 * fp.u := by linarith
  unfold gamma
  rw [div_le_iff₀ (by push_cast; linarith)]
  push_cast
  -- 2u ≤ (1/2)(1 - 2u)  ⟺  4u ≤ 1 - 2u  ⟺  6u ≤ 1
  linarith

-- ============================================================
-- gamma_4 division bridge for the concrete Givens kernel
-- ============================================================

/-- Coefficient division bridge at the printed `gamma_4` constant
    (Higham §19.3, Lemma 19.7, eq. (19.24), p. 366).

    For the concrete rounded denominator `fl_givensDenom` (a rounded 2-norm:
    two squarings, one add, one rounded square root) and one final rounded
    division, the computed quotient is a `gamma_4` relative perturbation of the
    exact quotient `z / sqrt(x_i^2 + x_j^2)`.

    The four counted rounding contributions are:
    the sum-of-squares factor (`<2>`, from the two squarings and the add,
    surviving the square root as `1/sqrt(1+theta_2)` at index `2`) and the
    (square-root roundoff, division roundoff) pair (a `<2>` Stewart counter). -/
theorem fl_givensCoeff_div_relative_error_gamma4 (fp : FPModel)
    (xi xj z : ℝ) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 4 ∧
      fp.fl_div z (fl_givensDenom fp xi xj) =
        (z / givensDenom xi xj) * (1 + θ) := by
  -- Basic smallness facts
  have hval2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hvalid
  have hval1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have hval4 : gammaValid fp 4 := gammaValid_mono fp (by omega) hvalid
  have hu_lt1 : fp.u < 1 := by
    have := hval1; unfold gammaValid at this; simpa using this
  have hγ2_le_half : gamma fp 2 ≤ 1 / 2 := gamma_two_le_half fp hvalid
  have hγ2_nonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hval2
  -- Denominator sqrt-factor form: fl_norm2 fp 2 v = sqrt(S) * sqrt(1+θ) * (1+δ)
  have hval2n : gammaValid fp (2 * 2) := by
    simpa using hval4
  obtain ⟨θss, δs, hθss, hδs, hθss_pos, hnorm⟩ :=
    fl_norm2_relative_error_sqrt_factor fp 2 (givensCoeffVector xi xj) hval2n
  -- Rewrite the sum of squares as the exact Givens denominator squared.
  have hsum : (∑ i : Fin 2,
      givensCoeffVector xi xj i * givensCoeffVector xi xj i) = xi ^ 2 + xj ^ 2 := by
    rw [givensCoeffVector_sum_sq]
  have hd : givensDenom xi xj ≠ 0 :=
    givensDenom_ne_zero (xi := xi) (xj := xj) h
  have hd_pos_sq : (0 : ℝ) < xi ^ 2 + xj ^ 2 :=
    lt_of_le_of_ne (add_nonneg (sq_nonneg xi) (sq_nonneg xj)) (Ne.symm h)
  have hsqrt_S : Real.sqrt (∑ i : Fin 2,
      givensCoeffVector xi xj i * givensCoeffVector xi xj i) = givensDenom xi xj := by
    rw [hsum]; rfl
  -- Concrete denominator in factored form.
  have hden_form :
      fl_givensDenom fp xi xj =
        givensDenom xi xj * (Real.sqrt (1 + θss) * (1 + δs)) := by
    unfold fl_givensDenom
    rw [hnorm, hsqrt_S]; ring
  -- Positivity of the residual factors.
  have hbss_lt1 : |θss| ≤ gamma fp 2 := hθss
  have hsqrt_one_add_pos : 0 < Real.sqrt (1 + θss) := by
    have : 0 < 1 + θss := by
      have hγlt1 : gamma fp 2 < 1 := by linarith [hγ2_le_half]
      linarith [neg_abs_le θss, hbss_lt1]
    exact Real.sqrt_pos.mpr this
  have hδs_pos : 0 < 1 + δs := by
    linarith [neg_abs_le δs, hδs, hu_lt1]
  have hfacs_pos : 0 < Real.sqrt (1 + θss) * (1 + δs) :=
    mul_pos hsqrt_one_add_pos hδs_pos
  have hfl_den_ne : fl_givensDenom fp xi xj ≠ 0 := by
    rw [hden_form]; exact mul_ne_zero hd hfacs_pos.ne'
  -- Final rounded division.
  obtain ⟨δd, hδd, hdiv⟩ := fp.model_div z (fl_givensDenom fp xi xj) hfl_den_ne
  -- Perturbation factor A = 1 / sqrt(1 + θss); bound |A - 1| ≤ gamma fp 2.
  have hθss_sq_le : θss ^ 2 ≤ (1 : ℝ) / 4 := by
    have : |θss| ≤ 1 / 2 := le_trans hbss_lt1 hγ2_le_half
    nlinarith [sq_abs θss, this, abs_nonneg θss]
  have hθss_ge : (-(1 : ℝ) / 2) ≤ θss := by
    have : |θss| ≤ 1 / 2 := le_trans hbss_lt1 hγ2_le_half
    linarith [neg_abs_le θss, this]
  have hqcond : (0 : ℝ) ≤ 1 + θss - θss ^ 2 := by
    have h1t : (0 : ℝ) < 1 + θss := by linarith [hθss_ge]
    linarith [hθss_sq_le, hθss_ge]
  have hpos_1t : (0 : ℝ) < 1 + θss := by linarith [hθss_ge]
  have hA_bound : |1 / Real.sqrt (1 + θss) - 1| ≤ gamma fp 2 :=
    le_trans (abs_inv_sqrt_one_add_sub_one_le hpos_1t hqcond) hbss_lt1
  set a : ℝ := 1 / Real.sqrt (1 + θss) - 1 with ha_def
  have hA_eq : 1 / Real.sqrt (1 + θss) = 1 + a := by rw [ha_def]; ring
  -- Perturbation factor B = (1 + δd) * (1 / (1 + δs)); bound |B - 1| ≤ gamma fp 2.
  have hB_bound : |(1 + δd) * (1 / (1 + δs)) - 1| ≤ gamma fp 2 :=
    div_roundoff_pair_abs_sub_one_le fp δd δs hδd hδs hu_lt1 hval2
  set b : ℝ := (1 + δd) * (1 / (1 + δs)) - 1 with hb_def
  have hB_eq : (1 + δd) * (1 / (1 + δs)) = 1 + b := by rw [hb_def]; ring
  -- Combine (1 + a)(1 + b) into 1 + ψ with |ψ| ≤ gamma fp 4.
  have hab_bound_a : |a| ≤ gamma fp 2 := hA_bound
  have hab_bound_b : |b| ≤ gamma fp 2 := hB_bound
  obtain ⟨ψ, hψ, hψ_eq⟩ :=
    gamma_mul fp 2 2 a b hab_bound_a hab_bound_b (by simpa using hval4)
  have hψ4 : |ψ| ≤ gamma fp 4 := by simpa using hψ
  refine ⟨ψ, hψ4, ?_⟩
  -- Assemble the identity.
  rw [hdiv, hden_form]
  have hexpand :
      z / (givensDenom xi xj * (Real.sqrt (1 + θss) * (1 + δs))) * (1 + δd)
        = (z / givensDenom xi xj)
            * ((1 / Real.sqrt (1 + θss)) * ((1 + δd) * (1 / (1 + δs)))) := by
    field_simp [hd, hsqrt_one_add_pos.ne', hδs_pos.ne']
  rw [hexpand, hA_eq, hB_eq, hψ_eq]

-- ============================================================
-- gamma_4 relative-error theorems for c_hat and s_hat
-- ============================================================

/-- Computed Givens cosine relative error at the printed `gamma_4` constant
    (Higham §19.3, Lemma 19.7, eq. (19.24), p. 366; identical count in §18.5,
    Lemma 18.6). -/
theorem fl_givensC_relative_error_gamma4 (fp : FPModel)
    (xi xj : ℝ) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 4 ∧
      fl_givensC fp xi xj = givensC xi xj * (1 + θ) := by
  simpa [fl_givensC, givensC] using
    fl_givensCoeff_div_relative_error_gamma4 fp xi xj xi h hvalid

/-- Computed Givens sine relative error at the printed `gamma_4` constant
    (Higham §19.3, Lemma 19.7, eq. (19.24), p. 366; identical count in §18.5,
    Lemma 18.6). -/
theorem fl_givensS_relative_error_gamma4 (fp : FPModel)
    (xi xj : ℝ) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 4 ∧
      fl_givensS fp xi xj = givensS xi xj * (1 + θ) := by
  simpa [fl_givensS, givensS] using
    fl_givensCoeff_div_relative_error_gamma4 fp xi xj xj h hvalid

/-- **Higham Lemma 19.7 at the printed `gamma_4` constant**
    (§19.3, eq. (19.24), p. 366; identical coefficient count in §18.5,
    Lemma 18.6).

    The concrete rounded Givens coefficient kernels `fl_givensC` / `fl_givensS`
    satisfy the coefficient contract `GivensCoeffError` with `μ = gamma fp 4`,
    i.e. `c_hat = c(1 + theta_4)`, `s_hat = s(1 + theta_4')`,
    `|theta_4|, |theta_4'| ≤ gamma_4`.

    This is the printed constant, strictly sharper than the conservative
    `gamma_6` bound proved by `fl_givensCoeffError_conservative`
    (GivensSpec.lean).  The index `4` is the exact integer index of the
    repository `gamma` function `gamma fp k = k*u/(1 - k*u)`; per Higham p. 357
    the integer inside gamma-tilde is otherwise unspecified. -/
theorem fl_givensCoeffError_gamma4 (fp : FPModel)
    (xi xj : ℝ) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    GivensCoeffError (givensC xi xj) (givensS xi xj)
      (fl_givensC fp xi xj) (fl_givensS fp xi xj) (gamma fp 4) := by
  constructor
  · exact fl_givensC_relative_error_gamma4 fp xi xj h hvalid
  · exact fl_givensS_relative_error_gamma4 fp xi xj h hvalid

end NumStability.Wave13
