import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import NumStability.Analysis.LinearOperators.MatrixPowers.BaiDemmelGu.StabilityRadius

/-!
# Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.BaiDemmelGu

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
# Bai--Demmel--Gu matrix-power bound

This module formalizes the matrix-power estimate used in the proof of
Lemma 2 of Bai, Demmel, and Gu (1997) and quoted in Higham, *Accuracy and
Stability of Numerical Algorithms*, 2nd ed., Chapter 18.

For an element `a` of a complex Banach algebra whose spectral radius is less
than one, we define `d(a)` to be the attained minimum of

`  ‖resolvent a z‖⁻¹,   ‖z‖ = 1.`

For `CStarMatrix`, the norm in this definition is the operator norm.  The
standard finite-dimensional identification with
`min_{|z|=1} σ_min(zI-A)` uses an additional SVD/minimum-singular-value bridge;
this module does not claim that identity without such a theorem.  The proof
below does not assume the desired inner-circle resolvent estimate: it derives
it from the inverse-resolvent minimum by a Neumann perturbation, then combines
it with the repository's Dunford contour identity.
-/






namespace NumStability

open scoped Real Topology ComplexOrder
open Complex Metric Set Filter

section ComplexBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]























































































































































































































































































































































































































/-- The second branch of the Bai--Demmel--Gu power bound.  In fact the
`1/d(a)` estimate holds for every power; the displayed threshold records the
source's branch split. -/
theorem higham18_baiDemmelGu_smallPower [Nontrivial A] [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1) (m : ℕ)
    (_hm : (m : ℝ) ≤
      (1 - unitCircleStabilityRadius a) / unitCircleStabilityRadius a) :
    ‖a ^ m‖ ≤ (unitCircleStabilityRadius a)⁻¹ := by
  have hd := unitCircleStabilityRadius_pos a hrho
  have hrhoReal : (spectralRadius ℂ a).toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hrho)
      ENNReal.one_ne_top).2 hrho
  have hcontour := norm_pow_le_baiDemmelGu_contour
    a hrho m (r := 1) one_pos le_rfl hrhoReal (by linarith)
  simpa using hcontour














































/-- The optimized, large-power branch of Bai--Demmel--Gu's bound. -/
theorem higham18_baiDemmelGu_largePower [Nontrivial A] [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1) (m : ℕ)
    (hm : (1 - unitCircleStabilityRadius a) /
        unitCircleStabilityRadius a < (m : ℝ)) :
    ‖a ^ m‖ ≤ baiDemmelGuAlpha m * (m : ℝ) *
      (1 - unitCircleStabilityRadius a) ^ m := by
  let d : ℝ := unitCircleStabilityRadius a
  let M : ℝ := (m : ℝ)
  let rho : ℝ := (spectralRadius ℂ a).toReal
  have hd : 0 < d := unitCircleStabilityRadius_pos a hrho
  have hgap := unitCircleStabilityRadius_le_one_sub_spectralRadius_toReal
    a hrho
  have hrhoNonneg : 0 ≤ rho := ENNReal.toReal_nonneg
  have hd1 : d ≤ 1 := by
    dsimp [d, rho] at hgap ⊢
    linarith
  have hcritNonneg : 0 ≤ (1 - d) / d :=
    div_nonneg (sub_nonneg.mpr hd1) hd.le
  have hm' : (1 - d) / d < M := by simpa [d, M] using hm
  have hMpos : 0 < M := hcritNonneg.trans_lt hm'
  have hmNat : 0 < m := by
    have hmR : (0 : ℝ) < (m : ℝ) := by simpa [M] using hMpos
    exact_mod_cast hmR
  by_cases hdEq : d = 1
  · have hpow : a ^ m = 0 :=
      pow_eq_zero_of_unitCircleStabilityRadius_eq_one a hrho m hmNat
        (by simpa [d] using hdEq)
    rw [hpow, norm_zero]
    simp [d, hdEq, Nat.ne_of_gt hmNat]
  · have hdlt : d < 1 := lt_of_le_of_ne hd1 hdEq
    have hgapPos : 0 < 1 - d := sub_pos.mpr hdlt
    have hcrit : 1 - d < M * d :=
      (div_lt_iff₀ hd).1 hm'
    let rstar : ℝ := (1 + 1 / M) * (1 - d)
    have hrstar : 0 < rstar := by
      dsimp [rstar]
      exact mul_pos (by positivity) hgapPos
    have hrd : 1 - d < rstar := by
      dsimp [rstar]
      have hsmall : 0 < (1 / M) * (1 - d) :=
        mul_pos (one_div_pos.mpr hMpos) hgapPos
      nlinarith
    have hrform : rstar = ((M + 1) * (1 - d)) / M := by
      dsimp [rstar]
      field_simp
    have hrstar1 : rstar ≤ 1 := by
      rw [hrform]
      apply (div_le_one hMpos).2
      nlinarith
    have hrhole : rho ≤ 1 - d := by
      dsimp [d, rho] at hgap ⊢
      linarith
    have hrhor : (spectralRadius ℂ a).toReal < rstar := by
      dsimp [rho] at hrhole
      exact hrhole.trans_lt hrd
    have hcontour := norm_pow_le_baiDemmelGu_contour
      a hrho m hrstar hrstar1 hrhor (by simpa [d] using hrd)
    have hdenEq : d - 1 + rstar = (1 - d) / M := by
      dsimp [rstar]
      field_simp
      ring
    calc
      ‖a ^ m‖ ≤ rstar ^ (m + 1) *
          (unitCircleStabilityRadius a - 1 + rstar)⁻¹ := hcontour
      _ = rstar ^ (m + 1) * (d - 1 + rstar)⁻¹ := by rfl
      _ = baiDemmelGuAlpha m * M * (1 - d) ^ m := by
        rw [hdenEq]
        dsimp [rstar, baiDemmelGuAlpha, M]
        rw [mul_pow, inv_div, pow_succ (1 - d) m]
        field_simp
      _ = baiDemmelGuAlpha m * (m : ℝ) *
          (1 - unitCircleStabilityRadius a) ^ m := by rfl

/-- **Bai--Demmel--Gu matrix-power bound quoted in Higham Chapter 18.**

Both source branches are packaged in one assumption-free endpoint.  The only
matrix datum in the conclusion is the stability radius defined above as the
actual attained unit-circle resolvent minimum.
-/
theorem higham18_baiDemmelGu_matrixPowerBound
    [Nontrivial A] [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1) (m : ℕ) :
    (((1 - unitCircleStabilityRadius a) /
          unitCircleStabilityRadius a < (m : ℝ)) →
      ‖a ^ m‖ ≤ baiDemmelGuAlpha m * (m : ℝ) *
        (1 - unitCircleStabilityRadius a) ^ m) ∧
    (((m : ℝ) ≤ (1 - unitCircleStabilityRadius a) /
          unitCircleStabilityRadius a) →
      ‖a ^ m‖ ≤ (unitCircleStabilityRadius a)⁻¹) := by
  exact ⟨higham18_baiDemmelGu_largePower a hrho m,
    higham18_baiDemmelGu_smallPower a hrho m⟩

end ComplexBanachAlgebra

section CStarMatrixSpecialization












end CStarMatrixSpecialization

section AlphaBounds




















































































end AlphaBounds

end NumStability
