-- NumStability/Source/Higham/Chapter05/Algorithm01/ComplexHorner/ErrorBounds/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.HighamChapter5ComplexAlgorithm51`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Tactic
import NumStability.Analysis.ComplexArithmetic
import NumStability.Source.Higham.Chapter05.Algorithm01.ComplexHorner.Basic

/-!
# Theorems

Relocated from `NumStability.Algorithms.HighamChapter5ComplexAlgorithm51` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# HighamChapter5ComplexAlgorithm51 (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.HighamChapter5ComplexAlgorithm51`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

private theorem complexHornerRunningRadius_nonneg
    (fp : FPModel) (hgamma2 : gammaValid fp 2) :
    0 ≤ complexHornerRunningRadius fp := by
  exact mul_nonneg (Real.sqrt_nonneg _) (gamma_nonneg fp hgamma2)

private theorem complexHornerRunningRadius_ge_two_u
    (fp : FPModel) (hgamma2 : gammaValid fp 2) :
    2 * fp.u ≤ complexHornerRunningRadius fp := by
  have hlinear : 2 * fp.u ≤ gamma fp 2 := by
    simpa using n_mul_u_le_gamma fp 2 hgamma2
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hgamma_nonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hgamma2
  calc
    2 * fp.u ≤ gamma fp 2 := hlinear
    _ = 1 * gamma fp 2 := by ring
    _ ≤ Real.sqrt 2 * gamma fp 2 :=
      mul_le_mul_of_nonneg_right hsqrt hgamma_nonneg
    _ = complexHornerRunningRadius fp := rfl

/-- The actual rounded complex addition error can be written a posteriori in
terms of the computed output with the source radius `sqrt(2) * gamma_2`.

This is derived from `fl_complexAdd_error_bound`; it is not an assumed inverse
error model. -/
theorem fl_complexAdd_output_error_bound_gamma2
    (fp : FPModel) (hgamma2 : gammaValid fp 2) (z a : ℂ) :
    ‖fl_complexAdd fp z a - (z + a)‖ ≤
      complexHornerRunningRadius fp * ‖fl_complexAdd fp z a‖ := by
  let y := fl_complexAdd fp z a
  let exact := z + a
  let e : ℝ := ‖y - exact‖
  let t : ℝ := ‖y‖
  let rho : ℝ := complexHornerRunningRadius fp
  have hu_lt_half : fp.u < 1 / 2 := by
    unfold gammaValid at hgamma2
    norm_num at hgamma2 ⊢
    linarith
  have hden : 0 < 1 - fp.u := by linarith
  have hrho_ge : 2 * fp.u ≤ rho := by
    simpa [rho] using
      complexHornerRunningRadius_ge_two_u fp hgamma2
  have hu_coeff : fp.u ≤ rho * (1 - fp.u) := by
    have hhalf : fp.u ≤ 1 / 2 := le_of_lt hu_lt_half
    have hfirst : fp.u ≤ (2 * fp.u) * (1 - fp.u) := by
      nlinarith [fp.u_nonneg]
    have hfactor :
        (2 * fp.u) * (1 - fp.u) ≤ rho * (1 - fp.u) :=
      mul_le_mul_of_nonneg_right hrho_ge (le_of_lt hden)
    exact hfirst.trans hfactor
  have hadd : e ≤ fp.u * ‖exact‖ := by
    simpa [e, y, exact] using fl_complexAdd_error_bound fp z a
  have hexact : ‖exact‖ ≤ e + t := by
    calc
      ‖exact‖ = ‖(exact - y) + y‖ := by congr 1; ring
      _ ≤ ‖exact - y‖ + ‖y‖ := norm_add_le _ _
      _ = e + t := by simp [e, t, norm_sub_rev]
  have he_rec : e ≤ fp.u * (e + t) :=
    hadd.trans (mul_le_mul_of_nonneg_left hexact fp.u_nonneg)
  have hleft : (1 - fp.u) * e ≤ fp.u * t := by
    nlinarith
  have hright : fp.u * t ≤ (1 - fp.u) * (rho * t) := by
    have := mul_le_mul_of_nonneg_right hu_coeff (norm_nonneg y)
    simpa [t, mul_assoc, mul_left_comm, mul_comm] using this
  have hscaled : (1 - fp.u) * e ≤ (1 - fp.u) * (rho * t) :=
    hleft.trans hright
  have he : e ≤ rho * t := le_of_mul_le_mul_left hscaled hden
  simpa [e, t, rho, y, exact] using he

/-- **Actual local complex Horner bound.** The executor formed from
`fl_complexMul` and `fl_complexAdd` satisfies the inverse-local estimate used
by Algorithm 5.1, at exactly the source coefficient
`sqrt(2) * gamma_2`. -/
theorem fl_complexHornerStep_inverse_error_bound
    (fp : FPModel) (hgamma2 : gammaValid fp 2) (x y a : ℂ) :
    ‖fl_complexHornerStep fp x y a - complexHornerStep x y a‖ ≤
      complexHornerRunningRadius fp *
        (‖x‖ * ‖y‖ + ‖fl_complexHornerStep fp x y a‖) := by
  let m := fl_complexMul fp x y
  let q := fl_complexAdd fp m a
  have hadd : ‖q - (m + a)‖ ≤
      complexHornerRunningRadius fp * ‖q‖ := by
    simpa [q, m] using
      fl_complexAdd_output_error_bound_gamma2 fp hgamma2 m a
  have hmul : ‖m - x * y‖ ≤
      complexHornerRunningRadius fp * ‖x * y‖ := by
    simpa [m, complexHornerRunningRadius] using
      fl_complexMul_error_bound fp hgamma2 x y
  have hsplit :
      q - complexHornerStep x y a = (q - (m + a)) + (m - x * y) := by
    simp [complexHornerStep]
    ring
  calc
    ‖fl_complexHornerStep fp x y a - complexHornerStep x y a‖
        = ‖q - complexHornerStep x y a‖ := by rfl
    _ = ‖(q - (m + a)) + (m - x * y)‖ := by rw [hsplit]
    _ ≤ ‖q - (m + a)‖ + ‖m - x * y‖ := norm_add_le _ _
    _ ≤ complexHornerRunningRadius fp * ‖q‖ +
        complexHornerRunningRadius fp * ‖x * y‖ := add_le_add hadd hmul
    _ = complexHornerRunningRadius fp *
        (‖x‖ * ‖y‖ + ‖fl_complexHornerStep fp x y a‖) := by
      rw [norm_mul]
      simp [q, m, fl_complexHornerStep]
      ring

/-- The complex Algorithm 5.1 bound is nonnegative. -/
theorem fl_complexHornerRunningBound_nonneg
    (fp : FPModel) (hgamma2 : gammaValid fp 2)
    (x : ℂ) (coeffsDesc : List ℂ) :
    0 ≤ fl_complexHornerRunningBound fp x coeffsDesc := by
  unfold fl_complexHornerRunningBound
  let state := fl_complexHornerRunningState fp x coeffsDesc
  have hstate : ‖state.1‖ ≤ 2 * state.2 := by
    simpa [state] using
      fl_complexHornerRunningState_norm_fst_le_two_mu fp x coeffsDesc
  exact mul_nonneg (complexHornerRunningRadius_nonneg fp hgamma2) (by linarith)

lemma fl_complexHornerRunningStep_error_bound
    (fp : FPModel) (hgamma2 : gammaValid fp 2) (x : ℂ)
    {state : ℂ × ℝ} {yExact : ℂ}
    (herr : ‖state.1 - yExact‖ ≤
      complexHornerRunningRadius fp * (2 * state.2 - ‖state.1‖))
    (a : ℂ) :
    let next := fl_complexHornerRunningStep fp x state a
    ‖next.1 - complexHornerStep x yExact a‖ ≤
      complexHornerRunningRadius fp * (2 * next.2 - ‖next.1‖) := by
  let yRound := fl_complexHornerStep fp x state.1 a
  have hlocal :
      ‖yRound - complexHornerStep x state.1 a‖ ≤
        complexHornerRunningRadius fp *
          (‖x‖ * ‖state.1‖ + ‖yRound‖) := by
    simpa [yRound] using
      fl_complexHornerStep_inverse_error_bound fp hgamma2 x state.1 a
  have hExactDiff :
      ‖complexHornerStep x state.1 a - complexHornerStep x yExact a‖ =
        ‖x‖ * ‖state.1 - yExact‖ := by
    have h :
        complexHornerStep x state.1 a - complexHornerStep x yExact a =
          x * (state.1 - yExact) := by
      unfold complexHornerStep
      ring
    rw [h, norm_mul]
  have hExactBound :
      ‖complexHornerStep x state.1 a - complexHornerStep x yExact a‖ ≤
        ‖x‖ * (complexHornerRunningRadius fp *
          (2 * state.2 - ‖state.1‖)) := by
    rw [hExactDiff]
    exact mul_le_mul_of_nonneg_left herr (norm_nonneg x)
  have htri :
      ‖yRound - complexHornerStep x yExact a‖ ≤
        ‖yRound - complexHornerStep x state.1 a‖ +
          ‖complexHornerStep x state.1 a -
            complexHornerStep x yExact a‖ := by
    have hsplit :
        yRound - complexHornerStep x yExact a =
          (yRound - complexHornerStep x state.1 a) +
            (complexHornerStep x state.1 a -
              complexHornerStep x yExact a) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  have hsum := add_le_add hlocal hExactBound
  have htarget :
      complexHornerRunningRadius fp *
          (‖x‖ * ‖state.1‖ + ‖yRound‖) +
        ‖x‖ * (complexHornerRunningRadius fp *
          (2 * state.2 - ‖state.1‖)) =
      complexHornerRunningRadius fp *
        (2 * (‖x‖ * state.2 + ‖yRound‖) - ‖yRound‖) := by ring
  dsimp
  simp only [fl_complexHornerRunningStep]
  exact htri.trans (by simpa [htarget] using hsum)

lemma fl_complexHornerRunningFold_error_bound
    (fp : FPModel) (hgamma2 : gammaValid fp 2) (x : ℂ) :
    ∀ (rest : List ℂ) (yRound yExact : ℂ) (mu : ℝ),
      0 ≤ mu →
      ‖yRound‖ ≤ 2 * mu →
      ‖yRound - yExact‖ ≤
        complexHornerRunningRadius fp * (2 * mu - ‖yRound‖) →
      let state := rest.foldl (fl_complexHornerRunningStep fp x) (yRound, mu)
      ‖state.1 - rest.foldl (complexHornerStep x) yExact‖ ≤
        complexHornerRunningRadius fp * (2 * state.2 - ‖state.1‖) := by
  intro rest
  induction rest with
  | nil =>
      intro yRound yExact mu _ _ herr
      simpa using herr
  | cons a rest ih =>
      intro yRound yExact mu hmu _hstate herr
      let next := fl_complexHornerRunningStep fp x (yRound, mu) a
      have hstep :
          ‖next.1 - complexHornerStep x yExact a‖ ≤
            complexHornerRunningRadius fp * (2 * next.2 - ‖next.1‖) := by
        simpa [next] using
          fl_complexHornerRunningStep_error_bound fp hgamma2 x
            (state := (yRound, mu)) (yExact := yExact) herr a
      have hnext_mu : 0 ≤ next.2 := by
        simpa [next] using
          fl_complexHornerRunningStep_snd_nonneg fp x a
            (state := (yRound, mu)) hmu
      have hnext_norm : ‖next.1‖ ≤ 2 * next.2 := by
        simpa [next] using
          fl_complexHornerRunningStep_norm_fst_le_two_snd fp x a
            (state := (yRound, mu)) hmu
      simpa [List.foldl, next] using
        ih next.1 (complexHornerStep x yExact a) next.2
          hnext_mu hnext_norm hstep

/-- **Higham Chapter 5, Algorithm 5.1, complex-data extension.**

The actual executor assembled from `fl_complexMul` and `fl_complexAdd` is
bounded by the source running quantity
`sqrt(2) * gamma_2 * (2*mu - |y|)`. -/
theorem fl_complexHornerDesc_running_error_bound
    (fp : FPModel) (hgamma2 : gammaValid fp 2)
    (x : ℂ) (coeffsDesc : List ℂ) :
    ‖fl_complexHornerDesc fp x coeffsDesc -
        complexPolyDesc x coeffsDesc‖ ≤
      fl_complexHornerRunningBound fp x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_complexHornerDesc, complexPolyDesc,
        fl_complexHornerRunningBound, fl_complexHornerRunningState]
  | cons a rest =>
      have hmu : 0 ≤ ‖a‖ / 2 := by positivity
      have hstate : ‖a‖ ≤ 2 * (‖a‖ / 2) := by
        have h : (2 : ℝ) * (‖a‖ / 2) = ‖a‖ := by ring
        rw [h]
      have herr :
          ‖a - a‖ ≤ complexHornerRunningRadius fp *
            (2 * (‖a‖ / 2) - ‖a‖) := by
        have hzero : (2 : ℝ) * (‖a‖ / 2) - ‖a‖ = 0 := by ring
        simp [hzero]
      have hfold :=
        fl_complexHornerRunningFold_error_bound fp hgamma2 x
          rest a a (‖a‖ / 2) hmu hstate herr
      have hpoly :
          complexPolyDesc x (a :: rest) =
            rest.foldl (complexHornerStep x) a := by
        rw [← complexHornerDesc_eq_complexPolyDesc x (a :: rest)]
        rfl
      let state :=
        rest.foldl (fl_complexHornerRunningStep fp x) (a, ‖a‖ / 2)
      have hfst :
          state.1 = rest.foldl (fl_complexHornerStep fp x) a := by
        simpa [state] using
          fl_complexHornerRunningFold_fst_eq fp x rest a (‖a‖ / 2)
      simpa [fl_complexHornerDesc, fl_complexHornerRunningBound,
        fl_complexHornerRunningState, hpoly, state, hfst] using hfold

end NumStability
