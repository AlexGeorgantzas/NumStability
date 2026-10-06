-- Analysis/DunfordResidue.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 18, §18.2 — the Dunford (holomorphic-functional-calculus) residue
-- identity underlying eq (18.8)
--     ‖Aᵏ‖₂ ≤ ε⁻¹ · ρ_ε(A)^{k+1}.
--
-- CONTEXT.  `Analysis/ResolventFunctionalCalculus.lean` closed the analyticity of
-- the resolvent (gap (a)) and the contour ML-estimate (ingredient (3)), and
-- assembled the (18.8)-shaped power bound `norm_pow_le_of_cauchy_representation`
-- *modulo* one honestly-flagged hypothesis `hrep`: the Dunford residue identity
--     aᵏ = (2πi)⁻¹ ∮_{C(0,R)} zᵏ (zI−a)⁻¹ dz         (R > ‖a‖).
-- Its closing note recorded that `hrep` was the single remaining link because it
-- needs a Bochner dominated-convergence interchange of `∮` with the `A`-valued
-- Neumann series `R(z) = Σ z^{-n-1} aⁿ` — machinery Mathlib does not package for
-- `circleIntegral`.
--
-- THIS MODULE CLOSES `hrep` OUTRIGHT (ingredient (2)), hence removes the last
-- hypothesis and delivers the (18.8)-shaped power bound UNCONDITIONALLY.
--
-- ROUTE (exactly Higham's §18.2 derivation).
--   (1) `resolvent_hasSum_neumann` — on `‖a‖ < ‖z‖` the resolvent is the
--       convergent `A`-valued Neumann series
--         R(z) = Σ_{n≥0} z^{-(n+1)} aⁿ,
--       obtained by factoring `zI − a = z(1 − z⁻¹a)` and summing the geometric
--       series `Ring.inverse (1 − z⁻¹a) = Σ (z⁻¹a)ⁿ` (`hasSum_geom_series_inverse`).
--   (2) `hasSum_circleIntegral_pow_smul_resolvent` — the DOMINATED-CONVERGENCE
--       interchange: for `R > ‖a‖`,
--         HasSum (fun n => ∮_{C(0,R)} (zᵏ z^{-(n+1)}) • aⁿ)
--                (∮_{C(0,R)} zᵏ • R(z)).
--       Proved by `intervalIntegral.hasSum_integral_of_dominated_convergence`
--       with the geometric dominating function `K·(‖a‖/R)ⁿ`
--       (`K = Rᵏ(‖1‖+1)`), the swap Mathlib itself uses for the scalar Cauchy
--       kernel in `hasSum_two_pi_I_cauchyPowerSeries_integral`.
--   (3) `circleIntegral_pow_smul_pow_inv_eq` — the scalar contour facts: for each
--       `n`, `∮_{C(0,R)} (zᵏ z^{-(n+1)}) • aⁿ = (if n = k then 2πi else 0) • aⁿ`,
--       via `circleIntegral.integral_sub_zpow_of_ne` (`= 0` when the exponent
--       `k−n−1 ≠ −1`) and `circleIntegral.integral_sub_inv_of_mem_ball`
--       (`= 2πi` when `n = k`).
--   (4) `pow_eq_two_pi_I_inv_smul_circleIntegral` (= the identity `hrep`), and the
--       unconditional bound `norm_pow_le_of_cauchy_circleIntegral`.
--
-- HONESTY.  Nothing is smuggled into a hypothesis: the residue identity that the
-- previous module carried as `hrep` is *derived* here.  The dominating function
-- is the genuinely summable geometric one (ratio `‖a‖/R < 1`); the `n = 0` term
-- `‖a⁰‖ = ‖1‖` (which may exceed `1` in a general `NormedRing` without
-- `NormOneClass`) is absorbed by the honest uniform bound
-- `‖aⁿ‖ ≤ (‖1‖+1)‖a‖ⁿ`, so the statements need NO `NormOneClass` assumption and
-- hold verbatim for Higham's ‖·‖₂ on complex matrices.
--
-- All statements are over a complex Banach algebra
-- `[NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]` and hold verbatim for
-- `CStarMatrix (Fin n) (Fin n) ℂ` (or any concrete operator-norm matrix algebra).

import NumStability.Analysis.ResolventFunctionalCalculus
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace NumStability

open scoped Real Topology
open Complex Metric

section ComplexBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-! ### The `A`-valued Neumann series of the resolvent (Higham §18.2). -/

/-- **Resolvent Neumann series** (Higham §18.2, 2nd ed. p. 346).

    For `‖a‖ < ‖z‖`, the resolvent `R(z) = (zI − a)⁻¹` is the convergent
    `A`-valued series `Σ_{n≥0} z^{-(n+1)} aⁿ`.  This is obtained by factoring
    `zI − a = z(1 − z⁻¹a)` (so `R(z) = z⁻¹ · (1 − z⁻¹a)⁻¹`) and expanding the
    geometric series `(1 − z⁻¹a)⁻¹ = Σ (z⁻¹a)ⁿ`, valid because
    `‖z⁻¹a‖ = ‖a‖/‖z‖ < 1`. -/
theorem resolvent_hasSum_neumann (a : A) {z : ℂ} (hz : ‖a‖ < ‖z‖) :
    HasSum (fun n : ℕ => (z ^ (n + 1))⁻¹ • a ^ n) (resolvent a z) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact absurd hz (not_lt.mpr (norm_nonneg a))
  have hzpos : (0 : ℝ) < ‖z‖ := (norm_nonneg a).trans_lt hz
  have hnorm : ‖z⁻¹ • a‖ < 1 := by
    rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_lt_one hzpos]; exact hz
  have hgeom : HasSum (fun n : ℕ => (z⁻¹ • a) ^ n) (Ring.inverse (1 - z⁻¹ • a)) :=
    hasSum_geom_series_inverse (z⁻¹ • a) hnorm
  have hres : resolvent a z = z⁻¹ • Ring.inverse (1 - z⁻¹ • a) := by
    have key := @spectrum.units_smul_resolvent_self ℂ A _ _ _ (Units.mk0 z hz0) a
    rw [Units.smul_def, Units.val_mk0, Units.smul_def, Units.val_inv_eq_inv_val,
      Units.val_mk0] at key
    have hone : resolvent (z⁻¹ • a) (1 : ℂ) = Ring.inverse (1 - z⁻¹ • a) := by
      simp only [resolvent, map_one]
    rw [← hone, ← key, inv_smul_smul₀ hz0]
  rw [hres]
  refine (hgeom.const_smul (z⁻¹ : ℂ)).congr_fun ?_
  intro n
  rw [smul_pow, smul_smul, ← inv_pow, ← pow_succ']

/-! ### Dominated-convergence interchange of `∮` and the Neumann series
    (Higham §18.2, ingredient (2)). -/

/-- **Term-by-term integrability swap for the contour integrand** (Higham §18.2,
    2nd ed. p. 346).

    On the circle `|z| = R` with `R > ‖a‖`, the contour integrand `zᵏ • R(z)`
    equals the sum of the `A`-valued series `Σ_n (zᵏ z^{-(n+1)}) • aⁿ`, and the
    circle integral commutes with the sum:
      `HasSum (fun n => ∮_{C(0,R)} (zᵏ z^{-(n+1)}) • aⁿ) (∮_{C(0,R)} zᵏ • R(z))`.

    The interchange is a Bochner dominated-convergence argument
    (`intervalIntegral.hasSum_integral_of_dominated_convergence`) with the
    summable geometric dominating function `n ↦ Rᵏ(‖1‖+1)·(‖a‖/R)ⁿ` (ratio
    `‖a‖/R < 1`).  This is the `A`-valued analogue of the scalar swap Mathlib
    performs in `hasSum_two_pi_I_cauchyPowerSeries_integral`. -/
theorem hasSum_circleIntegral_pow_smul_resolvent (a : A) (k : ℕ) {R : ℝ} (hR : ‖a‖ < R) :
    HasSum (fun n : ℕ => ∮ z in C(0, R), ((z ^ k * (z ^ (n + 1))⁻¹) • a ^ n))
      (∮ z in C(0, R), z ^ k • resolvent a z) := by
  have hRpos : (0 : ℝ) < R := (norm_nonneg a).trans_lt hR
  have hcm_ne : ∀ θ : ℝ, circleMap 0 R θ ≠ 0 := fun θ => circleMap_ne_center hRpos.ne'
  have hρ : ‖a‖ / R < 1 := (div_lt_one hRpos).2 hR
  have hρ0 : (0 : ℝ) ≤ ‖a‖ / R := div_nonneg (norm_nonneg a) hRpos.le
  set ρ : ℝ := ‖a‖ / R with hρdef
  set K : ℝ := R ^ k * (‖(1 : A)‖ + 1) with hKdef
  simp only [circleIntegral, deriv_circleMap]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _θ => K * ρ ^ n)
    (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · -- AEStronglyMeasurable of the n-th summand (continuity; z ≠ 0 on the circle)
    apply Continuous.aestronglyMeasurable
    apply Continuous.smul (by fun_prop)
    apply Continuous.smul _ continuous_const
    apply Continuous.mul (by fun_prop)
    exact ((continuous_pow (n + 1)).comp (continuous_circleMap 0 R)).inv₀
      (fun θ => pow_ne_zero _ (hcm_ne θ))
  · -- pointwise bound: ‖F n θ‖ ≤ K · ρⁿ
    refine Filter.Eventually.of_forall fun θ _ => ?_
    simp only [norm_smul, norm_mul, norm_inv, norm_pow, norm_circleMap_zero, norm_I, mul_one,
      abs_of_pos hRpos]
    show R * (R ^ k * (R ^ (n + 1))⁻¹ * ‖a ^ n‖) ≤ K * ρ ^ n
    -- Uniform submultiplicative bound valid for ALL n (absorbs the n = 0 term ‖1‖).
    have hpn : ‖a ^ n‖ ≤ (‖(1 : A)‖ + 1) * ‖a‖ ^ n := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp only [pow_zero, mul_one]
        linarith [norm_nonneg (1 : A)]
      · calc ‖a ^ n‖ ≤ ‖a‖ ^ n := norm_pow_le' a hnpos
          _ ≤ (‖(1 : A)‖ + 1) * ‖a‖ ^ n := by
                nlinarith [norm_nonneg (1 : A), pow_nonneg (norm_nonneg a) n]
    have hLHS : R * (R ^ k * (R ^ (n + 1))⁻¹ * ‖a ^ n‖)
        = R ^ k * (R ^ n)⁻¹ * ‖a ^ n‖ := by
      rw [pow_succ]; field_simp
    rw [hLHS, hKdef, hρdef, div_pow]
    calc R ^ k * (R ^ n)⁻¹ * ‖a ^ n‖
        ≤ R ^ k * (R ^ n)⁻¹ * ((‖(1 : A)‖ + 1) * ‖a‖ ^ n) := by gcongr
      _ = R ^ k * (‖(1 : A)‖ + 1) * (‖a‖ ^ n / R ^ n) := by rw [div_eq_mul_inv]; ring
  · -- summability of the dominating function (geometric, ratio ρ < 1)
    exact Filter.Eventually.of_forall fun θ _ =>
      (summable_geometric_of_lt_one hρ0 hρ).mul_left K
  · -- integrability of the (constant) tsum of the bound
    exact intervalIntegrable_const
  · -- pointwise HasSum: Σ F n θ = f θ, from the Neumann series scaled by (z·I)·zᵏ
    refine Filter.Eventually.of_forall fun θ _ => ?_
    have hznorm : ‖a‖ < ‖circleMap 0 R θ‖ := by
      rw [norm_circleMap_zero, abs_of_pos hRpos]; exact hR
    have hneu := (resolvent_hasSum_neumann a hznorm).const_smul
      ((circleMap 0 R θ) ^ k) |>.const_smul (circleMap 0 R θ * I)
    refine hneu.congr_fun ?_
    intro n
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    ring

/-! ### The scalar contour facts (Higham §18.2, ingredient (3)). -/

/-- **Per-term scalar circle integral** (Higham §18.2, 2nd ed. p. 346).

    For each `n`, the `n`-th term of the (interchanged) contour series is
      `∮_{C(0,R)} (zᵏ z^{-(n+1)}) • aⁿ = (if n = k then 2πi else 0) • aⁿ`.
    On the circle `z ≠ 0`, the scalar kernel `zᵏ z^{-(n+1)}` equals the integer
    power `(z − 0)^{k−n−1}`; its circle integral is `0` unless the exponent is
    `−1` (`circleIntegral.integral_sub_zpow_of_ne`), and `2πi` exactly when
    `n = k` (`circleIntegral.integral_sub_inv_of_mem_ball`, `0 ∈ ball 0 R`). -/
theorem circleIntegral_pow_smul_pow_inv_eq (a : A) (k n : ℕ) {R : ℝ} (hRpos : 0 < R) :
    (∮ z in C(0, R), ((z ^ k * (z ^ (n + 1))⁻¹) • a ^ n))
      = (if n = k then (2 * π * I : ℂ) else 0) • a ^ n := by
  rw [circleIntegral.integral_smul_const]
  congr 1
  have hcongr : (∮ z in C(0, R), z ^ k * (z ^ (n + 1))⁻¹)
      = ∮ z in C(0, R), (z - 0) ^ ((k : ℤ) - (n + 1)) := by
    refine circleIntegral.integral_congr hRpos.le (fun z hz => ?_)
    have hz0 : z ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hz
      intro h; rw [h, norm_zero] at hz; exact hRpos.ne' hz.symm
    rw [sub_zero, zpow_sub₀ hz0, div_eq_mul_inv, zpow_natCast]
    norm_cast
  rw [hcongr]
  by_cases hnk : n = k
  · subst hnk
    rw [if_pos rfl]
    have hexp : (n : ℤ) - (n + 1) = -1 := by ring
    rw [hexp]
    have h2 : (∮ z in C(0, R), (z - 0) ^ (-1 : ℤ)) = ∮ z in C(0, R), (z - (0 : ℂ))⁻¹ := by
      refine circleIntegral.integral_congr hRpos.le (fun z _ => ?_)
      rw [zpow_neg_one]
    rw [h2]
    exact circleIntegral.integral_sub_inv_of_mem_ball (by simp [hRpos])
  · rw [if_neg hnk]
    apply circleIntegral.integral_sub_zpow_of_ne
    intro h
    exact hnk (by omega)

/-! ### The Dunford residue identity and the unconditional (18.8)-shaped bound. -/

/-- **Dunford residue identity — ingredient (2) of (18.8), now UNCONDITIONAL.**
    (Higham §18.2, eq (18.8) derivation, 2nd ed. p. 346.)

    For a complex Banach algebra element `a` and any radius `R > ‖a‖` (so the
    circle `|z| = R` encloses the spectrum),
      `aᵏ = (2πi)⁻¹ ∮_{C(0,R)} zᵏ (zI − a)⁻¹ dz`.

    This is *exactly* the hypothesis `hrep` carried by
    `ResolventFunctionalCalculus.norm_pow_le_of_cauchy_representation`; it is now
    PROVED, by combining the dominated-convergence interchange
    (`hasSum_circleIntegral_pow_smul_resolvent`) with the scalar residue
    calculation (`circleIntegral_pow_smul_pow_inv_eq`) — only the `n = k` term
    survives, contributing `2πi · aᵏ`. -/
theorem pow_eq_two_pi_I_inv_smul_circleIntegral (a : A) (k : ℕ) {R : ℝ} (hR : ‖a‖ < R) :
    a ^ k = (2 * π * I : ℂ)⁻¹ • ∮ z in C(0, R), z ^ k • resolvent a z := by
  have hRpos : (0 : ℝ) < R := (norm_nonneg a).trans_lt hR
  have hswap := hasSum_circleIntegral_pow_smul_resolvent a k hR
  simp only [circleIntegral_pow_smul_pow_inv_eq a k _ hRpos] at hswap
  have hsingle : HasSum (fun n : ℕ => (if n = k then (2 * π * I : ℂ) else 0) • a ^ n)
      ((2 * π * I : ℂ) • a ^ k) := by
    have hs := hasSum_single (f := fun n : ℕ => (if n = k then (2 * π * I : ℂ) else 0) • a ^ n)
      k (fun n hn => by simp only [if_neg hn, zero_smul])
    rwa [if_pos rfl] at hs
  have hval : (∮ z in C(0, R), z ^ k • resolvent a z) = (2 * π * I : ℂ) • a ^ k :=
    hswap.unique hsingle
  rw [hval, smul_smul, inv_mul_cancel₀, one_smul]
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨⟨by norm_num, by exact_mod_cast Real.pi_ne_zero⟩, I_ne_zero⟩

/-- **Higham (18.8), contour form — now UNCONDITIONAL.**
    (Higham §18.2, eq (18.8), 2nd ed. p. 346.)

    For any radius `R > ‖a‖` and any uniform bound `C` on `‖zᵏ • R(z)‖` over the
    circle `|z| = R`,
      `‖aᵏ‖ ≤ R · C`.
    The residue identity is now internal (supplied by
    `pow_eq_two_pi_I_inv_smul_circleIntegral`), so — unlike
    `ResolventFunctionalCalculus.norm_pow_le_of_cauchy_representation` — this
    carries NO residue hypothesis.  A concrete `C` is always available from
    `ResolventFunctionalCalculus.exists_bound_pow_smul_resolvent_on_sphere` once
    the circle lies in the resolvent set (automatic here since `R > ‖a‖`); tracing
    the ε-pseudospectrum boundary with `C = R_max^k · ε⁻¹` yields Higham's
    `‖Aᵏ‖₂ ≤ ε⁻¹ · ρ_ε(A)^{k+1}` verbatim. -/
theorem norm_pow_le_of_cauchy_circleIntegral (a : A) {R C : ℝ} (k : ℕ) (hR : ‖a‖ < R)
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖z ^ k • resolvent a z‖ ≤ C) :
    ‖a ^ k‖ ≤ R * C := by
  have hRpos : (0 : ℝ) ≤ R := ((norm_nonneg a).trans_lt hR).le
  exact norm_pow_le_of_cauchy_representation a 0 k hRpos hC
    (pow_eq_two_pi_I_inv_smul_circleIntegral a k hR)

end ComplexBanachAlgebra

end NumStability
