-- Algorithms/HighamChapter5ComplexAlgorithm51.lean
--
-- Higham Chapter 5, Algorithm 5.1 for complex data, using the actual rounded
-- complex operations from Chapter 3, Lemma 3.5.

import Mathlib.Tactic
import NumStability.Analysis.ComplexArithmetic

namespace NumStability

/-!
# Complex-data extension of Algorithm 5.1

Higham states immediately after Algorithm 5.1 that the same running-error
recurrence works for complex coefficients and argument when the final scale is
replaced by `sqrt(2) * gamma_2`.  This module constructs the actual executor
from `fl_complexMul` and `fl_complexAdd`; the endpoint does not assume a
Horner-step error expansion.
-/

/-- One exact complex Horner update. -/
def complexHornerStep (x y a : ℂ) : ℂ := x * y + a

/-- One actual rounded complex Horner update: first the Chapter 3 rounded
complex multiplication, then the Chapter 3 rounded complex addition. -/
noncomputable def fl_complexHornerStep
    (fp : FPModel) (x y a : ℂ) : ℂ :=
  fl_complexAdd fp (fl_complexMul fp x y) a

/-- Exact complex Horner evaluation for descending coefficients. -/
def complexHornerDesc (x : ℂ) : List ℂ → ℂ
  | [] => 0
  | a :: rest => rest.foldl (complexHornerStep x) a

/-- The complex polynomial in descending coefficient order. -/
def complexPolyDesc (x : ℂ) : List ℂ → ℂ
  | [] => 0
  | a :: rest => a * x ^ rest.length + complexPolyDesc x rest

lemma complexHornerFold_eq_acc_mul_pow_add_polyDesc (x : ℂ) :
    ∀ (rest : List ℂ) (y : ℂ),
      rest.foldl (complexHornerStep x) y =
        y * x ^ rest.length + complexPolyDesc x rest := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [complexPolyDesc]
  | cons a rest ih =>
      intro y
      simp [List.foldl, complexHornerStep, complexPolyDesc, ih, pow_succ]
      ring

/-- Exact complex Horner evaluation agrees with the displayed polynomial. -/
theorem complexHornerDesc_eq_complexPolyDesc
    (x : ℂ) (coeffsDesc : List ℂ) :
    complexHornerDesc x coeffsDesc = complexPolyDesc x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [complexHornerDesc, complexPolyDesc]
        using complexHornerFold_eq_acc_mul_pow_add_polyDesc x rest a

/-- Actual rounded complex Horner evaluation for descending coefficients. -/
noncomputable def fl_complexHornerDesc
    (fp : FPModel) (x : ℂ) : List ℂ → ℂ
  | [] => 0
  | a :: rest => rest.foldl (fl_complexHornerStep fp x) a

/-- The source coefficient `sqrt(2) * gamma_2` for the complex extension of
Algorithm 5.1. -/
noncomputable def complexHornerRunningRadius (fp : FPModel) : ℝ :=
  Real.sqrt 2 * gamma fp 2

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

/-- One complex Algorithm 5.1 state update. The first component is the actual
rounded Horner value; the second is the exact real running accumulator. -/
noncomputable def fl_complexHornerRunningStep
    (fp : FPModel) (x : ℂ) (state : ℂ × ℝ) (a : ℂ) : ℂ × ℝ :=
  let y := fl_complexHornerStep fp x state.1 a
  (y, ‖x‖ * state.2 + ‖y‖)

/-- Complex Algorithm 5.1 running state, before its final scale. -/
noncomputable def fl_complexHornerRunningState
    (fp : FPModel) (x : ℂ) : List ℂ → ℂ × ℝ
  | [] => (0, 0)
  | a :: rest =>
      rest.foldl (fl_complexHornerRunningStep fp x) (a, ‖a‖ / 2)

/-- Complex Algorithm 5.1's final source bound
`sqrt(2) * gamma_2 * (2*mu - |y|)`. -/
noncomputable def fl_complexHornerRunningBound
    (fp : FPModel) (x : ℂ) (coeffsDesc : List ℂ) : ℝ :=
  let state := fl_complexHornerRunningState fp x coeffsDesc
  complexHornerRunningRadius fp * (2 * state.2 - ‖state.1‖)

lemma fl_complexHornerRunningFold_fst_eq (fp : FPModel) (x : ℂ) :
    ∀ (rest : List ℂ) (y : ℂ) (mu : ℝ),
      (rest.foldl (fl_complexHornerRunningStep fp x) (y, mu)).1 =
        rest.foldl (fl_complexHornerStep fp x) y := by
  intro rest
  induction rest with
  | nil => intro y mu; rfl
  | cons a rest ih =>
      intro y mu
      simp [List.foldl, fl_complexHornerRunningStep, ih]

/-- The first component of the running state is the actual rounded complex
Horner execution. -/
theorem fl_complexHornerRunningState_fst_eq_fl_complexHornerDesc
    (fp : FPModel) (x : ℂ) (coeffsDesc : List ℂ) :
    (fl_complexHornerRunningState fp x coeffsDesc).1 =
      fl_complexHornerDesc fp x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [fl_complexHornerRunningState, fl_complexHornerDesc]
        using fl_complexHornerRunningFold_fst_eq fp x rest a (‖a‖ / 2)

lemma fl_complexHornerRunningStep_snd_nonneg
    (fp : FPModel) (x a : ℂ) {state : ℂ × ℝ} (hmu : 0 ≤ state.2) :
    0 ≤ (fl_complexHornerRunningStep fp x state a).2 := by
  simp [fl_complexHornerRunningStep]
  exact add_nonneg (mul_nonneg (norm_nonneg x) hmu) (norm_nonneg _)

lemma fl_complexHornerRunningStep_norm_fst_le_two_snd
    (fp : FPModel) (x a : ℂ) {state : ℂ × ℝ} (hmu : 0 ≤ state.2) :
    ‖(fl_complexHornerRunningStep fp x state a).1‖ ≤
      2 * (fl_complexHornerRunningStep fp x state a).2 := by
  simp [fl_complexHornerRunningStep]
  have hterm : 0 ≤ ‖x‖ * state.2 :=
    mul_nonneg (norm_nonneg x) hmu
  have hy : 0 ≤ ‖fl_complexHornerStep fp x state.1 a‖ := norm_nonneg _
  nlinarith

lemma fl_complexHornerRunningFold_snd_nonneg (fp : FPModel) (x : ℂ) :
    ∀ (rest : List ℂ) (state : ℂ × ℝ),
      0 ≤ state.2 →
      0 ≤ (rest.foldl (fl_complexHornerRunningStep fp x) state).2 := by
  intro rest
  induction rest with
  | nil => intro state hmu; simpa using hmu
  | cons a rest ih =>
      intro state hmu
      exact ih (fl_complexHornerRunningStep fp x state a)
        (fl_complexHornerRunningStep_snd_nonneg fp x a hmu)

lemma fl_complexHornerRunningFold_norm_fst_le_two_snd
    (fp : FPModel) (x : ℂ) :
    ∀ (rest : List ℂ) (state : ℂ × ℝ),
      0 ≤ state.2 →
      ‖state.1‖ ≤ 2 * state.2 →
      ‖(rest.foldl (fl_complexHornerRunningStep fp x) state).1‖ ≤
        2 * (rest.foldl (fl_complexHornerRunningStep fp x) state).2 := by
  intro rest
  induction rest with
  | nil => intro state _ hstate; simpa using hstate
  | cons a rest ih =>
      intro state hmu _hstate
      exact ih (fl_complexHornerRunningStep fp x state a)
        (fl_complexHornerRunningStep_snd_nonneg fp x a hmu)
        (fl_complexHornerRunningStep_norm_fst_le_two_snd fp x a hmu)

/-- The final state satisfies the source invariant `|y| <= 2*mu`. -/
theorem fl_complexHornerRunningState_norm_fst_le_two_mu
    (fp : FPModel) (x : ℂ) (coeffsDesc : List ℂ) :
    ‖(fl_complexHornerRunningState fp x coeffsDesc).1‖ ≤
      2 * (fl_complexHornerRunningState fp x coeffsDesc).2 := by
  cases coeffsDesc with
  | nil => simp [fl_complexHornerRunningState]
  | cons a rest =>
      have hinit_mu : 0 ≤ ‖a‖ / 2 := by positivity
      have hinit_norm : ‖a‖ ≤ 2 * (‖a‖ / 2) := by
        have h : (2 : ℝ) * (‖a‖ / 2) = ‖a‖ := by ring
        rw [h]
      simpa [fl_complexHornerRunningState]
        using fl_complexHornerRunningFold_norm_fst_le_two_snd fp x rest
          (a, ‖a‖ / 2) hinit_mu hinit_norm

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
