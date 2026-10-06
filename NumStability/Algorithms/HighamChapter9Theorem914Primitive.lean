import NumStability.Algorithms.HighamChapter9

/-!
# Higham Theorem 9.14: primitive tridiagonal recurrence audit

This file isolates the actual scalar recurrence used in the proof of Theorem
9.14.  In particular, it does not identify the rounded factors with an exact
LU factorization of the input matrix.
-/

namespace NumStability

open scoped BigOperators

/-- Exact scalar pivots in the no-pivot tridiagonal recurrence (9.19). -/
noncomputable def higham9_14_exactPivot
    (a d c : ℕ → ℝ) : ℕ → ℝ
  | 0 => d 0
  | k + 1 => d (k + 1) - (a (k + 1) / higham9_14_exactPivot a d c k) * c k

/-- Actual rounded scalar pivots, using exactly one division, multiplication,
and subtraction at every positive index. -/
noncomputable def higham9_14_roundedPivot
    (fp : FPModel) (a d c : ℕ → ℝ) : ℕ → ℝ
  | 0 => d 0
  | k + 1 =>
      fp.fl_sub (d (k + 1))
        (fp.fl_mul
          (fp.fl_div (a (k + 1)) (higham9_14_roundedPivot fp a d c k))
          (c k))

/-- Actual rounded subdiagonal multiplier paired with
`higham9_14_roundedPivot`.  Its value at zero is unused. -/
noncomputable def higham9_14_roundedMultiplier
    (fp : FPModel) (a d c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      fp.fl_div (a (k + 1)) (higham9_14_roundedPivot fp a d c k)

/-- Exact subdiagonal multiplier paired with `higham9_14_exactPivot`. -/
noncomputable def higham9_14_exactMultiplier
    (a d c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => a (k + 1) / higham9_14_exactPivot a d c k

@[simp] theorem higham9_14_exactPivot_zero (a d c : ℕ → ℝ) :
    higham9_14_exactPivot a d c 0 = d 0 := rfl

@[simp] theorem higham9_14_exactPivot_succ (a d c : ℕ → ℝ) (k : ℕ) :
    higham9_14_exactPivot a d c (k + 1) =
      d (k + 1) -
        higham9_14_exactMultiplier a d c (k + 1) * c k := rfl

@[simp] theorem higham9_14_roundedPivot_zero
    (fp : FPModel) (a d c : ℕ → ℝ) :
    higham9_14_roundedPivot fp a d c 0 = d 0 := rfl

@[simp] theorem higham9_14_roundedPivot_succ
    (fp : FPModel) (a d c : ℕ → ℝ) (k : ℕ) :
    higham9_14_roundedPivot fp a d c (k + 1) =
      fp.fl_sub (d (k + 1))
        (fp.fl_mul (higham9_14_roundedMultiplier fp a d c (k + 1)) (c k)) := rfl

/-- A division perturbation estimate with the denominator protected by a
strict half-margin. -/
private theorem higham9_14_div_input_stability
    {a p phat C rho g : ℝ}
    (hC : 0 ≤ C) (hrho : 0 < rho)
    (ha : |a| ≤ C) (hp : rho ≤ |p|)
    (hclose : |phat - p| ≤ g) (hg : g < rho / 2) :
    |a / phat - a / p| ≤ 2 * C * g / rho ^ 2 := by
  have hp_abs_pos : 0 < |p| := lt_of_lt_of_le hrho hp
  have hp0 : p ≠ 0 := abs_pos.mp hp_abs_pos
  have hphat_abs : rho / 2 < |phat| := by
    have htri : |p| ≤ |phat| + |phat - p| := by
      have heq : p = phat - (phat - p) := by ring
      calc
        |p| = |phat - (phat - p)| := congrArg abs heq
        _ ≤ |phat| + |phat - p| := abs_sub _ _
    linarith
  have hphat_abs_pos : 0 < |phat| := (half_pos hrho).trans hphat_abs
  have hphat0 : phat ≠ 0 := abs_pos.mp hphat_abs_pos
  have hident :
      a / phat - a / p = a * (p - phat) / (phat * p) := by
    field_simp [hp0, hphat0]
  rw [hident, abs_div, abs_mul, abs_mul]
  have hden_pos : 0 < |phat| * |p| := mul_pos hphat_abs_pos hp_abs_pos
  have hden : rho ^ 2 / 2 < |phat| * |p| := by
    nlinarith [mul_lt_mul_of_pos_right hphat_abs hp_abs_pos,
      mul_le_mul_of_nonneg_left hp (le_of_lt (half_pos hrho))]
  have hnum : |a| * |p - phat| ≤ C * g := by
    have herr : |p - phat| ≤ g := by simpa [abs_sub_comm] using hclose
    exact mul_le_mul ha herr (abs_nonneg _) hC
  have htarget_pos : 0 < rho ^ 2 := sq_pos_of_pos hrho
  apply (div_le_iff₀ hden_pos).2
  have hscale :
      (2 * C * g / rho ^ 2) * (rho ^ 2 / 2) = C * g := by
    field_simp [ne_of_gt htarget_pos]
  have hcoeff_nonneg : 0 ≤ 2 * C * g / rho ^ 2 := by
    have hg0 : 0 ≤ g := by
      have : 0 ≤ |phat - p| := abs_nonneg _
      linarith
    positivity
  calc
    |a| * |p - phat| ≤ C * g := hnum
    _ = (2 * C * g / rho ^ 2) * (rho ^ 2 / 2) := hscale.symm
    _ ≤ (2 * C * g / rho ^ 2) * (|phat| * |p|) :=
      mul_le_mul_of_nonneg_left (le_of_lt hden) hcoeff_nonneg

/-- Growth constant in the explicit pivot-closeness recurrence. -/
noncomputable def higham9_14_pivotGrowth (C rho : ℝ) : ℝ :=
  1 + 8 * C ^ 2 / rho ^ 2

/-- One-step rounding contribution in the explicit pivot-closeness
recurrence. -/
noncomputable def higham9_14_pivotRound (u C rho : ℝ) : ℝ :=
  u * (C + 11 * C ^ 2 / rho)

/-- One rounded recurrence step stays close to the corresponding exact step.

The assumptions are source-data bounds and a previously proved pivot-error
bound.  In particular, neither nonbreakdown nor a sign fact about the new
computed pivot is assumed. -/
private theorem higham9_14_roundedPivot_step_error
    (fp : FPModel) {a d c p phat C rho g : ℝ}
    (hC : 1 ≤ C) (hrho : 0 < rho)
    (ha : |a| ≤ C) (hd : |d| ≤ C) (hc : |c| ≤ C)
    (hp_floor : rho ≤ |p|)
    (hclose : |phat - p| ≤ g) (hg0 : 0 ≤ g) (hg : g < rho / 2)
    (hu : fp.u ≤ 1) :
    let l := a / p
    let lhat := fp.fl_div a phat
    let pnext := d - l * c
    let phatnext := fp.fl_sub d (fp.fl_mul lhat c)
    |phatnext - pnext| ≤
      (8 * C ^ 2 / rho ^ 2) * g +
        higham9_14_pivotRound fp.u C rho := by
  dsimp only
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hp_abs_pos : 0 < |p| := lt_of_lt_of_le hrho hp_floor
  have hp0 : p ≠ 0 := abs_pos.mp hp_abs_pos
  have hphat_abs : rho / 2 < |phat| := by
    have htri : |p| ≤ |phat| + |phat - p| := by
      have heq : p = phat - (phat - p) := by ring
      calc
        |p| = |phat - (phat - p)| := congrArg abs heq
        _ ≤ |phat| + |phat - p| := abs_sub _ _
    linarith
  have hphat_abs_pos : 0 < |phat| := (half_pos hrho).trans hphat_abs
  have hphat0 : phat ≠ 0 := abs_pos.mp hphat_abs_pos
  obtain ⟨δd, hδd, hlhat⟩ := fp.model_div a phat hphat0
  obtain ⟨δm, hδm, hprod⟩ := fp.model_mul (fp.fl_div a phat) c
  obtain ⟨δs, hδs, hpnext⟩ :=
    fp.model_sub d (fp.fl_mul (fp.fl_div a phat) c)
  have hu0 : 0 ≤ fp.u := fp.u_nonneg
  have hδd_one : |1 + δd| ≤ 2 := by
    calc
      |1 + δd| ≤ |(1 : ℝ)| + |δd| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hδm_one : |1 + δm| ≤ 2 := by
    calc
      |1 + δm| ≤ |(1 : ℝ)| + |δm| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hδs_one : |1 + δs| ≤ 2 := by
    calc
      |1 + δs| ≤ |(1 : ℝ)| + |δs| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hdiv_input : |a / phat - a / p| ≤ 2 * C * g / rho ^ 2 :=
    higham9_14_div_input_stability hC0 hrho ha hp_floor hclose hg
  have hinv_phat : |a / phat| ≤ 2 * C / rho := by
    rw [abs_div]
    apply (div_le_iff₀ hphat_abs_pos).2
    have hcoef0 : 0 ≤ 2 * C / rho := by positivity
    calc
      |a| ≤ C := ha
      _ = (2 * C / rho) * (rho / 2) := by field_simp [ne_of_gt hrho]
      _ ≤ (2 * C / rho) * |phat| :=
        mul_le_mul_of_nonneg_left (le_of_lt hphat_abs) hcoef0
  have hinv_p : |a / p| ≤ C / rho := by
    rw [abs_div]
    apply (div_le_iff₀ hp_abs_pos).2
    have hcoef0 : 0 ≤ C / rho := by positivity
    calc
      |a| ≤ C := ha
      _ = (C / rho) * rho := by field_simp [ne_of_gt hrho]
      _ ≤ (C / rho) * |p| :=
        mul_le_mul_of_nonneg_left hp_floor hcoef0
  have hlhat_abs : |fp.fl_div a phat| ≤ 4 * C / rho := by
    rw [hlhat, abs_mul]
    calc
      |a / phat| * |1 + δd| ≤ (2 * C / rho) * 2 :=
        mul_le_mul hinv_phat hδd_one (abs_nonneg _) (by positivity)
      _ = 4 * C / rho := by ring
  have hlerr : |fp.fl_div a phat - a / p| ≤
      4 * C * g / rho ^ 2 + C / rho * fp.u := by
    have hid :
        fp.fl_div a phat - a / p =
          (a / phat - a / p) * (1 + δd) + (a / p) * δd := by
      rw [hlhat]
      ring
    rw [hid]
    calc
      |(a / phat - a / p) * (1 + δd) + (a / p) * δd| ≤
          |a / phat - a / p| * |1 + δd| + |a / p| * |δd| := by
            simpa [abs_mul] using
              abs_add_le ((a / phat - a / p) * (1 + δd)) ((a / p) * δd)
      _ ≤ (2 * C * g / rho ^ 2) * 2 + (C / rho) * fp.u :=
        add_le_add
          (mul_le_mul hdiv_input hδd_one (abs_nonneg _) (by positivity))
          (mul_le_mul hinv_p hδd (abs_nonneg _) (by positivity))
      _ = 4 * C * g / rho ^ 2 + C / rho * fp.u := by ring
  have hprod_abs : |fp.fl_mul (fp.fl_div a phat) c| ≤ 8 * C ^ 2 / rho := by
    rw [hprod, abs_mul, abs_mul]
    calc
      |fp.fl_div a phat| * |c| * |1 + δm| ≤
          (4 * C / rho) * C * 2 :=
        mul_le_mul
          (mul_le_mul hlhat_abs hc (abs_nonneg _) (by positivity))
          hδm_one (by positivity) (by positivity)
      _ = 8 * C ^ 2 / rho := by ring
  have hprod_err :
      |fp.fl_mul (fp.fl_div a phat) c - (a / p) * c| ≤
        8 * C ^ 2 / rho ^ 2 * g + 3 * C ^ 2 / rho * fp.u := by
    have hid :
        fp.fl_mul (fp.fl_div a phat) c - (a / p) * c =
          (fp.fl_div a phat - a / p) * c * (1 + δm) +
            (a / p) * c * δm := by
      rw [hprod]
      ring
    rw [hid]
    calc
      |(fp.fl_div a phat - a / p) * c * (1 + δm) +
          (a / p) * c * δm| ≤
          |fp.fl_div a phat - a / p| * |c| * |1 + δm| +
            |a / p| * |c| * |δm| := by
        simpa [abs_mul] using
          abs_add_le
            ((fp.fl_div a phat - a / p) * c * (1 + δm))
            ((a / p) * c * δm)
      _ ≤
          (4 * C * g / rho ^ 2 + C / rho * fp.u) * C * 2 +
            (C / rho) * C * fp.u := by
        exact add_le_add
          (mul_le_mul
            (mul_le_mul hlerr hc (abs_nonneg _) (by positivity))
            hδm_one (by positivity) (by positivity))
          (mul_le_mul
            (mul_le_mul hinv_p hc (abs_nonneg _) (by positivity))
            hδm (by positivity) (by positivity))
      _ = 8 * C ^ 2 / rho ^ 2 * g + 3 * C ^ 2 / rho * fp.u := by ring
  have hsub_abs :
      |d - fp.fl_mul (fp.fl_div a phat) c| ≤ C + 8 * C ^ 2 / rho := by
    calc
      |d - fp.fl_mul (fp.fl_div a phat) c| ≤
          |d| + |fp.fl_mul (fp.fl_div a phat) c| := abs_sub _ _
      _ ≤ C + 8 * C ^ 2 / rho := add_le_add hd hprod_abs
  have hidfinal :
      fp.fl_sub d (fp.fl_mul (fp.fl_div a phat) c) -
          (d - (a / p) * c) =
        - (fp.fl_mul (fp.fl_div a phat) c - (a / p) * c) +
          (d - fp.fl_mul (fp.fl_div a phat) c) * δs := by
    rw [hpnext]
    ring
  rw [hidfinal]
  calc
    |- (fp.fl_mul (fp.fl_div a phat) c - (a / p) * c) +
        (d - fp.fl_mul (fp.fl_div a phat) c) * δs| ≤
      |fp.fl_mul (fp.fl_div a phat) c - (a / p) * c| +
        |d - fp.fl_mul (fp.fl_div a phat) c| * |δs| := by
      simpa [abs_mul, abs_sub_comm] using
        abs_add_le
          (-(fp.fl_mul (fp.fl_div a phat) c - (a / p) * c))
          ((d - fp.fl_mul (fp.fl_div a phat) c) * δs)
    _ ≤
        (8 * C ^ 2 / rho ^ 2 * g + 3 * C ^ 2 / rho * fp.u) +
          (C + 8 * C ^ 2 / rho) * fp.u :=
      add_le_add hprod_err
        (mul_le_mul hsub_abs hδs (abs_nonneg _) (by positivity))
    _ = (8 * C ^ 2 / rho ^ 2) * g +
        higham9_14_pivotRound fp.u C rho := by
      unfold higham9_14_pivotRound
      ring

/-- Explicit error budget for the first `t` primitive tridiagonal pivots. -/
noncomputable def higham9_14_pivotErrorBudget
    (fp : FPModel) (C rho : ℝ) (t : ℕ) : ℝ :=
  higham9_14_pivotRound fp.u C rho * (t : ℝ) *
    higham9_14_pivotGrowth C rho ^ t

private theorem higham9_14_pivotErrorBudget_le_final
    (fp : FPModel) {C rho : ℝ} {t N : ℕ}
    (hC : 1 ≤ C) (hrho : 0 < rho) (htN : t ≤ N) :
    higham9_14_pivotErrorBudget fp C rho t ≤
      higham9_14_pivotErrorBudget fp C rho N := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hU0 : 0 ≤ higham9_14_pivotRound fp.u C rho := by
    unfold higham9_14_pivotRound
    apply mul_nonneg fp.u_nonneg
    have : 0 ≤ 11 * C ^ 2 / rho := by positivity
    linarith
  have hK1 : 1 ≤ higham9_14_pivotGrowth C rho := by
    unfold higham9_14_pivotGrowth
    have : 0 ≤ 8 * C ^ 2 / rho ^ 2 := by positivity
    linarith
  have hcast : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast htN
  have hpow : higham9_14_pivotGrowth C rho ^ t ≤
      higham9_14_pivotGrowth C rho ^ N :=
    pow_le_pow_right₀ hK1 htN
  unfold higham9_14_pivotErrorBudget
  calc
    higham9_14_pivotRound fp.u C rho * (t : ℝ) *
          higham9_14_pivotGrowth C rho ^ t
      ≤ higham9_14_pivotRound fp.u C rho * (N : ℝ) *
          higham9_14_pivotGrowth C rho ^ t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcast hU0) (by positivity)
    _ ≤ higham9_14_pivotRound fp.u C rho * (N : ℝ) *
          higham9_14_pivotGrowth C rho ^ N := by
        exact mul_le_mul_of_nonneg_left hpow
          (mul_nonneg hU0 (Nat.cast_nonneg N))

private theorem higham9_14_pivotErrorBudget_step
    (fp : FPModel) {C rho : ℝ} (t : ℕ)
    (hC : 1 ≤ C) (hrho : 0 < rho) :
    (8 * C ^ 2 / rho ^ 2) * higham9_14_pivotErrorBudget fp C rho t +
        higham9_14_pivotRound fp.u C rho ≤
      higham9_14_pivotErrorBudget fp C rho (t + 1) := by
  have hU0 : 0 ≤ higham9_14_pivotRound fp.u C rho := by
    unfold higham9_14_pivotRound
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    apply mul_nonneg fp.u_nonneg
    have : 0 ≤ 11 * C ^ 2 / rho := by positivity
    linarith
  have hK1 : 1 ≤ higham9_14_pivotGrowth C rho := by
    unfold higham9_14_pivotGrowth
    have : 0 ≤ 8 * C ^ 2 / rho ^ 2 := by positivity
    linarith
  let U := higham9_14_pivotRound fp.u C rho
  let K := higham9_14_pivotGrowth C rho
  have hcoeff : 8 * C ^ 2 / rho ^ 2 = K - 1 := by
    dsimp [K, higham9_14_pivotGrowth]
    ring
  have hpow1 : 1 ≤ K ^ (t + 1) := one_le_pow₀ hK1
  have hfirst :
      (8 * C ^ 2 / rho ^ 2) * higham9_14_pivotErrorBudget fp C rho t + U ≤
        K * higham9_14_pivotErrorBudget fp C rho t + U := by
    have hg0 : 0 ≤ higham9_14_pivotErrorBudget fp C rho t := by
      unfold higham9_14_pivotErrorBudget
      positivity
    rw [hcoeff]
    nlinarith
  have hrec :
      K * higham9_14_pivotErrorBudget fp C rho t + U ≤
        higham9_14_pivotErrorBudget fp C rho (t + 1) := by
    unfold higham9_14_pivotErrorBudget
    change K * (U * (t : ℝ) * K ^ t) + U ≤
      U * ((t + 1 : ℕ) : ℝ) * K ^ (t + 1)
    push_cast
    have hterm : K * (U * (t : ℝ) * K ^ t) =
        U * (t : ℝ) * K ^ (t + 1) := by
      rw [pow_succ]
      ring
    rw [hterm]
    nlinarith [mul_nonneg hU0 (sub_nonneg.mpr hpow1)]
  exact hfirst.trans hrec

/-- Explicit, primitive-operation interpretation of "for sufficiently small
`u`" in Theorem 9.14.

If all exact pivots through `N` have modulus at least `rho`, the source data
are bounded by `C`, and the displayed scalar budget is below both `1` and
`rho/2`, then every actual rounded pivot through `N` is close to, has the same
sign as, and is therefore nonzero with its exact counterpart. -/
theorem higham9_14_roundedPivot_nonbreakdown_of_explicit_margin
    (fp : FPModel) (a d c : ℕ → ℝ) (N : ℕ) (C rho : ℝ)
    (hC : 1 ≤ C) (hrho : 0 < rho)
    (ha : ∀ k : ℕ, k ≤ N → |a k| ≤ C)
    (hd : ∀ k : ℕ, k ≤ N → |d k| ≤ C)
    (hc : ∀ k : ℕ, k < N → |c k| ≤ C)
    (hpivot : ∀ k : ℕ, k ≤ N →
      rho ≤ |higham9_14_exactPivot a d c k|)
    (hu : fp.u ≤ 1)
    (hsmall : higham9_14_pivotErrorBudget fp C rho N <
      min 1 (rho / 2)) :
    ∀ k : ℕ, k ≤ N →
      |higham9_14_roundedPivot fp a d c k -
          higham9_14_exactPivot a d c k| ≤
        higham9_14_pivotErrorBudget fp C rho k ∧
      0 < higham9_14_roundedPivot fp a d c k *
        higham9_14_exactPivot a d c k := by
  have hbudget_small : ∀ k : ℕ, k ≤ N →
      higham9_14_pivotErrorBudget fp C rho k < min 1 (rho / 2) := by
    intro k hk
    exact lt_of_le_of_lt
      (higham9_14_pivotErrorBudget_le_final fp hC hrho hk) hsmall
  have hclose : ∀ k : ℕ, k ≤ N →
      |higham9_14_roundedPivot fp a d c k -
          higham9_14_exactPivot a d c k| ≤
        higham9_14_pivotErrorBudget fp C rho k := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [higham9_14_pivotErrorBudget]
    | succ k ih =>
        intro hkN
        have hkN' : k ≤ N := Nat.le_trans (Nat.le_succ k) hkN
        have hih := ih hkN'
        have hbudget_nonneg :
            0 ≤ higham9_14_pivotErrorBudget fp C rho k := by
          unfold higham9_14_pivotErrorBudget higham9_14_pivotRound
          have hinner : 0 ≤ C + 11 * C ^ 2 / rho := by
            have : 0 ≤ 11 * C ^ 2 / rho := by positivity
            linarith [le_trans zero_le_one hC]
          have hK0 : 0 ≤ higham9_14_pivotGrowth C rho := by
            unfold higham9_14_pivotGrowth
            have : 0 ≤ 8 * C ^ 2 / rho ^ 2 := by positivity
            linarith
          exact mul_nonneg
            (mul_nonneg (mul_nonneg fp.u_nonneg hinner) (Nat.cast_nonneg k))
            (pow_nonneg hK0 k)
        have hbudget_half :
            higham9_14_pivotErrorBudget fp C rho k < rho / 2 :=
          lt_of_lt_of_le (hbudget_small k hkN') (min_le_right _ _)
        have hstep := higham9_14_roundedPivot_step_error
          fp hC hrho (ha (k + 1) hkN) (hd (k + 1) hkN)
          (hc k (Nat.lt_of_succ_le hkN)) (hpivot k hkN')
          hih hbudget_nonneg hbudget_half hu
        rw [higham9_14_roundedPivot_succ, higham9_14_exactPivot_succ]
        exact hstep.trans (higham9_14_pivotErrorBudget_step fp k hC hrho)
  intro k hkN
  have hkclose := hclose k hkN
  refine ⟨hkclose, ?_⟩
  have hbudget_half : higham9_14_pivotErrorBudget fp C rho k < rho / 2 :=
    lt_of_lt_of_le (hbudget_small k hkN) (min_le_right _ _)
  let p := higham9_14_exactPivot a d c k
  let phat := higham9_14_roundedPivot fp a d c k
  have hpabs : rho ≤ |p| := hpivot k hkN
  have herr : |phat - p| < rho / 2 := lt_of_le_of_lt hkclose hbudget_half
  have hp0 : p ≠ 0 := abs_ne_zero.mp (ne_of_gt (lt_of_lt_of_le hrho hpabs))
  rcases lt_or_gt_of_ne hp0 with hpneg | hppos
  · have hpabs_eq : |p| = -p := abs_of_neg hpneg
    have hupper : phat < 0 := by
      have hle : phat - p ≤ |phat - p| := le_abs_self _
      rw [hpabs_eq] at hpabs
      linarith
    exact mul_pos_of_neg_of_neg hupper hpneg
  · have hpabs_eq : |p| = p := abs_of_pos hppos
    have hlower : 0 < phat := by
      have hle : -|phat - p| ≤ phat - p := neg_abs_le _
      rw [hpabs_eq] at hpabs
      linarith
    exact mul_pos hlower hppos

/-- Nonzero-pivot projection of the explicit primitive margin theorem. -/
theorem higham9_14_roundedPivot_ne_zero_of_explicit_margin
    (fp : FPModel) (a d c : ℕ → ℝ) (N : ℕ) (C rho : ℝ)
    (hC : 1 ≤ C) (hrho : 0 < rho)
    (ha : ∀ k : ℕ, k ≤ N → |a k| ≤ C)
    (hd : ∀ k : ℕ, k ≤ N → |d k| ≤ C)
    (hc : ∀ k : ℕ, k < N → |c k| ≤ C)
    (hpivot : ∀ k : ℕ, k ≤ N →
      rho ≤ |higham9_14_exactPivot a d c k|)
    (hu : fp.u ≤ 1)
    (hsmall : higham9_14_pivotErrorBudget fp C rho N <
      min 1 (rho / 2)) :
    ∀ k : ℕ, k ≤ N → higham9_14_roundedPivot fp a d c k ≠ 0 := by
  intro k hk
  have hprod :=
    (higham9_14_roundedPivot_nonbreakdown_of_explicit_margin
      fp a d c N C rho hC hrho ha hd hc hpivot hu hsmall k hk).2
  exact (mul_ne_zero_iff.mp (ne_of_gt hprod)).1

/-- Qualitative "sufficiently small unit roundoff" corollary of the explicit
margin theorem.  Once finite source bounds `C` and `rho` are fixed, a positive
unit-roundoff threshold exists and is uniform over every `FPModel` satisfying
the primitive forward-relative laws. -/
theorem higham9_14_exists_unitRoundoff_threshold_of_margin
    (a d c : ℕ → ℝ) (N : ℕ) (C rho : ℝ)
    (hC : 1 ≤ C) (hrho : 0 < rho)
    (ha : ∀ k : ℕ, k ≤ N → |a k| ≤ C)
    (hd : ∀ k : ℕ, k ≤ N → |d k| ≤ C)
    (hc : ∀ k : ℕ, k < N → |c k| ≤ C)
    (hpivot : ∀ k : ℕ, k ≤ N →
      rho ≤ |higham9_14_exactPivot a d c k|) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∀ k : ℕ, k ≤ N →
          |higham9_14_roundedPivot fp a d c k -
              higham9_14_exactPivot a d c k| ≤
            higham9_14_pivotErrorBudget fp C rho k ∧
          0 < higham9_14_roundedPivot fp a d c k *
            higham9_14_exactPivot a d c k := by
  let M : ℝ := min 1 (rho / 2)
  let Q : ℝ :=
    (C + 11 * C ^ 2 / rho) * (N : ℝ) *
      higham9_14_pivotGrowth C rho ^ N
  have hM : 0 < M := by
    dsimp [M]
    exact lt_min one_pos (half_pos hrho)
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    have hinner : 0 ≤ C + 11 * C ^ 2 / rho := by positivity
    have hK0 : 0 ≤ higham9_14_pivotGrowth C rho := by
      unfold higham9_14_pivotGrowth
      have : 0 ≤ 8 * C ^ 2 / rho ^ 2 := by positivity
      linarith
    positivity
  have hQ1 : 0 < Q + 1 := by linarith
  let epsilon : ℝ := min 1 (M / (Q + 1))
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min one_pos (div_pos hM hQ1)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro fp hfp
  have hfu1 : fp.u ≤ 1 := by
    have heps_le : epsilon ≤ 1 := min_le_left _ _
    exact le_trans (le_of_lt hfp) heps_le
  have hfuQ : fp.u * Q < M := by
    by_cases hQzero : Q = 0
    · rw [hQzero, mul_zero]
      exact hM
    · have hQpos : 0 < Q := lt_of_le_of_ne hQ0 (Ne.symm hQzero)
      have heps_le : epsilon ≤ M / (Q + 1) := min_le_right _ _
      have hfu_lt : fp.u < M / (Q + 1) := hfp.trans_le heps_le
      have hmul_lt : fp.u * Q < (M / (Q + 1)) * Q :=
        mul_lt_mul_of_pos_right hfu_lt hQpos
      have hfrac_lt : (M / (Q + 1)) * Q < M := by
        have hident : (M / (Q + 1)) * Q = M - M / (Q + 1) := by
          field_simp [ne_of_gt hQ1]
          ring
        rw [hident]
        linarith [div_pos hM hQ1]
      exact hmul_lt.trans hfrac_lt
  have hsmall : higham9_14_pivotErrorBudget fp C rho N < M := by
    have hbudget : higham9_14_pivotErrorBudget fp C rho N = fp.u * Q := by
      dsimp [higham9_14_pivotErrorBudget, higham9_14_pivotRound, Q]
      ring
    rw [hbudget]
    exact hfuQ
  exact higham9_14_roundedPivot_nonbreakdown_of_explicit_margin
    fp a d c N C rho hC hrho ha hd hc hpivot hfu1 (by simpa [M] using hsmall)

/-- On a finite recurrence prefix, coefficient caps and a positive exact-pivot
floor are automatic once every exact pivot is nonzero. -/
private theorem higham9_14_exists_finite_source_bounds
    (a d c : ℕ → ℝ) (N : ℕ)
    (hpivot_ne : ∀ k : ℕ, k ≤ N → higham9_14_exactPivot a d c k ≠ 0) :
    ∃ C rho : ℝ,
      1 ≤ C ∧ 0 < rho ∧
      (∀ k : ℕ, k ≤ N → |a k| ≤ C) ∧
      (∀ k : ℕ, k ≤ N → |d k| ≤ C) ∧
      (∀ k : ℕ, k < N → |c k| ≤ C) ∧
      ∀ k : ℕ, k ≤ N → rho ≤ |higham9_14_exactPivot a d c k| := by
  classical
  let C : ℝ := 1 + ∑ i : Fin (N + 1), (|a i.val| + |d i.val| + |c i.val|)
  let gaps : Finset ℝ :=
    (Finset.univ : Finset (Fin (N + 1))).image
      (fun i => |higham9_14_exactPivot a d c i.val|)
  have hgaps : gaps.Nonempty := by
    let i0 : Fin (N + 1) := ⟨0, by omega⟩
    refine ⟨|higham9_14_exactPivot a d c i0.val|, ?_⟩
    exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩
  let rho : ℝ := gaps.min' hgaps
  have hC : 1 ≤ C := by
    dsimp [C]
    have hsum : 0 ≤ ∑ i : Fin (N + 1),
        (|a i.val| + |d i.val| + |c i.val|) := by positivity
    linarith
  have hterm_le : ∀ k : ℕ, k ≤ N →
      |a k| + |d k| + |c k| ≤ C - 1 := by
    intro k hk
    let ik : Fin (N + 1) := ⟨k, by omega⟩
    have hsingle : |a ik.val| + |d ik.val| + |c ik.val| ≤
        ∑ i : Fin (N + 1), (|a i.val| + |d i.val| + |c i.val|) :=
      Finset.single_le_sum
        (f := fun i : Fin (N + 1) => |a i.val| + |d i.val| + |c i.val|)
        (fun i _ => by positivity) (Finset.mem_univ ik)
    simpa [C, ik] using hsingle
  have ha : ∀ k : ℕ, k ≤ N → |a k| ≤ C := by
    intro k hk
    have h := hterm_le k hk
    have hd0 : 0 ≤ |d k| := abs_nonneg _
    have hc0 : 0 ≤ |c k| := abs_nonneg _
    linarith
  have hd : ∀ k : ℕ, k ≤ N → |d k| ≤ C := by
    intro k hk
    have h := hterm_le k hk
    have ha0 : 0 ≤ |a k| := abs_nonneg _
    have hc0 : 0 ≤ |c k| := abs_nonneg _
    linarith
  have hc : ∀ k : ℕ, k < N → |c k| ≤ C := by
    intro k hk
    have h := hterm_le k (Nat.le_trans (Nat.le_of_lt hk) (Nat.le_refl N))
    have ha0 : 0 ≤ |a k| := abs_nonneg _
    have hd0 : 0 ≤ |d k| := abs_nonneg _
    linarith
  have hrho : 0 < rho := by
    have hmem : gaps.min' hgaps ∈ gaps := Finset.min'_mem gaps hgaps
    obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hmem
    have hne : higham9_14_exactPivot a d c i.val ≠ 0 :=
      hpivot_ne i.val (by omega)
    simpa [rho, hi] using abs_pos.mpr hne
  have hpivot : ∀ k : ℕ, k ≤ N →
      rho ≤ |higham9_14_exactPivot a d c k| := by
    intro k hk
    let ik : Fin (N + 1) := ⟨k, by omega⟩
    exact Finset.min'_le gaps _
      (Finset.mem_image.mpr ⟨ik, Finset.mem_univ ik, by simp [ik]⟩)
  exact ⟨C, rho, hC, hrho, ha, hd, hc, hpivot⟩

/-- Source-level qualitative nonbreakdown for the primitive tridiagonal
recurrence: on every finite prefix with nonzero exact pivots, there is a
positive unit-roundoff threshold below which all rounded pivots preserve the
exact signs.  No computed-pivot or computed-sign premise occurs. -/
theorem higham9_14_exists_unitRoundoff_threshold_of_exact_pivots_ne_zero
    (a d c : ℕ → ℝ) (N : ℕ)
    (hpivot_ne : ∀ k : ℕ, k ≤ N → higham9_14_exactPivot a d c k ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∀ k : ℕ, k ≤ N →
          0 < higham9_14_roundedPivot fp a d c k *
            higham9_14_exactPivot a d c k := by
  obtain ⟨C, rho, hC, hrho, ha, hd, hc, hpivot⟩ :=
    higham9_14_exists_finite_source_bounds a d c N hpivot_ne
  obtain ⟨epsilon, hepsilon, hthreshold⟩ :=
    higham9_14_exists_unitRoundoff_threshold_of_margin
      a d c N C rho hC hrho ha hd hc hpivot
  refine ⟨epsilon, hepsilon, ?_⟩
  intro fp hfp k hk
  exact (hthreshold fp hfp k hk).2

/-- Quantitative finite-prefix form of the small-unit-roundoff bridge.  In
addition to preserving every exact pivot sign, the actual primitive
recurrence can be made uniformly closer than any prescribed positive
tolerance.  The tolerance is source-independent; the resulting threshold is
allowed to depend on the finite source prefix. -/
theorem higham9_14_exists_unitRoundoff_threshold_of_exact_pivots_ne_zero_with_tolerance
    (a d c : ℕ → ℝ) (N : ℕ)
    (hpivot_ne : ∀ k : ℕ, k ≤ N → higham9_14_exactPivot a d c k ≠ 0)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∀ k : ℕ, k ≤ N →
          |higham9_14_roundedPivot fp a d c k -
              higham9_14_exactPivot a d c k| < eta ∧
          0 < higham9_14_roundedPivot fp a d c k *
            higham9_14_exactPivot a d c k := by
  obtain ⟨C, rho, hC, hrho, ha, hd, hc, hpivot⟩ :=
    higham9_14_exists_finite_source_bounds a d c N hpivot_ne
  obtain ⟨epsilon₀, hepsilon₀, hthreshold⟩ :=
    higham9_14_exists_unitRoundoff_threshold_of_margin
      a d c N C rho hC hrho ha hd hc hpivot
  let Q : ℝ :=
    (C + 11 * C ^ 2 / rho) * (N : ℝ) *
      higham9_14_pivotGrowth C rho ^ N
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    have hinner : 0 ≤ C + 11 * C ^ 2 / rho := by positivity
    have hK0 : 0 ≤ higham9_14_pivotGrowth C rho := by
      unfold higham9_14_pivotGrowth
      have : 0 ≤ 8 * C ^ 2 / rho ^ 2 := by positivity
      linarith
    positivity
  have hQ1 : 0 < Q + 1 := by linarith
  let epsilon : ℝ := min epsilon₀ (eta / (Q + 1))
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min hepsilon₀ (div_pos heta hQ1)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro fp hfp k hk
  have hfp₀ : fp.u < epsilon₀ := hfp.trans_le (min_le_left _ _)
  have hfp_eta : fp.u < eta / (Q + 1) :=
    hfp.trans_le (min_le_right _ _)
  have hbase := hthreshold fp hfp₀ k hk
  have huQ1 : fp.u * (Q + 1) < eta :=
    (lt_div_iff₀ hQ1).mp hfp_eta
  have huQ : fp.u * Q < eta := by
    have hle : fp.u * Q ≤ fp.u * (Q + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) fp.u_nonneg
    exact hle.trans_lt huQ1
  have hbudget : higham9_14_pivotErrorBudget fp C rho k = fp.u *
      ((C + 11 * C ^ 2 / rho) * (k : ℝ) *
        higham9_14_pivotGrowth C rho ^ k) := by
    dsimp [higham9_14_pivotErrorBudget, higham9_14_pivotRound]
    ring
  have hbudget_le : higham9_14_pivotErrorBudget fp C rho k ≤
      higham9_14_pivotErrorBudget fp C rho N :=
    higham9_14_pivotErrorBudget_le_final fp hC hrho hk
  have hbudgetN : higham9_14_pivotErrorBudget fp C rho N = fp.u * Q := by
    dsimp [higham9_14_pivotErrorBudget, higham9_14_pivotRound, Q]
    ring
  refine ⟨lt_of_le_of_lt hbase.1 (hbudget_le.trans_lt ?_), hbase.2⟩
  rw [hbudgetN]
  exact huQ

/-! ## The primitive-model correction used by the PDF proof -/

/-- A forward relative error `z = q(1+delta)` gives a backward relative
error with coefficient `u/(1-u)`.  Bare `FPModel` does not, in general,
preserve the coefficient `u` when the equation is inverted. -/
theorem higham9_14_backward_relative_correction
    {u delta q z : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hdelta : |delta| ≤ u) (hz : z = q * (1 + delta)) :
    ∃ epsilon : ℝ,
      |epsilon| ≤ u / (1 - u) ∧ (1 + epsilon) * z = q := by
  have hdelta_lower : -u ≤ delta := by
    have := neg_abs_le delta
    linarith
  have hden_pos : 0 < 1 + delta := by linarith
  have hone_sub_pos : 0 < 1 - u := by linarith
  refine ⟨-delta / (1 + delta), ?_, ?_⟩
  · rw [abs_div, abs_neg, abs_of_pos hden_pos]
    apply (div_le_iff₀ hden_pos).2
    have hcoef0 : 0 ≤ u / (1 - u) := by positivity
    calc
      |delta| ≤ u := hdelta
      _ = (u / (1 - u)) * (1 - u) := by
        field_simp [ne_of_gt hone_sub_pos]
      _ ≤ (u / (1 - u)) * (1 + delta) :=
        mul_le_mul_of_nonneg_left (by linarith) hcoef0
  · rw [hz]
    field_simp [ne_of_gt hden_pos]
    ring

/-- Correct backward form of a primitive rounded division in the repository's
forward-relative `FPModel`. -/
theorem higham9_14_model_div_backward_corrected
    (fp : FPModel) {x y : ℝ} (hy : y ≠ 0) (hu1 : fp.u < 1) :
    ∃ epsilon : ℝ,
      |epsilon| ≤ fp.u / (1 - fp.u) ∧
        (1 + epsilon) * fp.fl_div x y = x / y := by
  obtain ⟨delta, hdelta, hfl⟩ := fp.model_div x y hy
  exact higham9_14_backward_relative_correction
    fp.u_nonneg hu1 hdelta hfl

/-- Corrected primitive subdiagonal residual for (9.20).  The computed
division product is backward stable with coefficient `u/(1-u)` relative to
the computed product, which is the orientation used by the PDF's matrix
inequality. -/
theorem higham9_20_primitive_division_residual_corrected
    (fp : FPModel) {a phat : ℝ} (hphat : phat ≠ 0) (hu1 : fp.u < 1) :
    |fp.fl_div a phat * phat - a| ≤
      (fp.u / (1 - fp.u)) * |fp.fl_div a phat * phat| := by
  obtain ⟨epsilon, hepsilon, heq⟩ :=
    higham9_14_model_div_backward_corrected fp hphat hu1
  have hprod_eq :
      fp.fl_div a phat * phat - a =
        -epsilon * (fp.fl_div a phat * phat) := by
    have heq' : (1 + epsilon) * (fp.fl_div a phat * phat) = a := by
      calc
        (1 + epsilon) * (fp.fl_div a phat * phat) =
            ((1 + epsilon) * fp.fl_div a phat) * phat := by ring
        _ = (a / phat) * phat := by rw [heq]
        _ = a := div_mul_cancel₀ a hphat
    linarith
  rw [hprod_eq, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_right hepsilon (abs_nonneg _)

/-- Corrected primitive diagonal residual for (9.20).  One rounded multiply
and one rounded subtraction give the same `u/(1-u)` coefficient against the
two computed-factor contributions. -/
theorem higham9_20_primitive_diagonal_residual_corrected
    (fp : FPModel) (l d c : ℝ) (hu1 : fp.u < 1) :
    |fp.fl_sub d (fp.fl_mul l c) + l * c - d| ≤
      (fp.u / (1 - fp.u)) *
        (|fp.fl_sub d (fp.fl_mul l c)| + |l * c|) := by
  obtain ⟨delta, hdelta, hmul⟩ := fp.model_mul l c
  obtain ⟨theta, htheta, hsub⟩ :=
    fp.model_sub d (fp.fl_mul l c)
  obtain ⟨epsilon, hepsilon, heq⟩ :=
    higham9_14_backward_relative_correction
      fp.u_nonneg hu1 htheta hsub
  have hone_sub_pos : 0 < 1 - fp.u := by linarith
  have hu_le_beta : fp.u ≤ fp.u / (1 - fp.u) := by
    apply (le_div_iff₀ hone_sub_pos).2
    nlinarith [fp.u_nonneg]
  have hid :
      fp.fl_sub d (fp.fl_mul l c) + l * c - d =
        -epsilon * fp.fl_sub d (fp.fl_mul l c) - delta * (l * c) := by
    rw [hmul] at heq ⊢
    linarith
  rw [hid]
  calc
    |-epsilon * fp.fl_sub d (fp.fl_mul l c) - delta * (l * c)| ≤
        |epsilon| * |fp.fl_sub d (fp.fl_mul l c)| +
          |delta| * |l * c| := by
      simpa [sub_eq_add_neg, abs_mul, abs_neg] using
        abs_add_le
          (-epsilon * fp.fl_sub d (fp.fl_mul l c))
          (-(delta * (l * c)))
    _ ≤ (fp.u / (1 - fp.u)) *
          |fp.fl_sub d (fp.fl_mul l c)| +
        (fp.u / (1 - fp.u)) * |l * c| :=
      add_le_add
        (mul_le_mul_of_nonneg_right hepsilon (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hdelta.trans hu_le_beta) (abs_nonneg _))
    _ = (fp.u / (1 - fp.u)) *
        (|fp.fl_sub d (fp.fl_mul l c)| + |l * c|) := by ring

/-- An `FPModel` whose division always rounds downward by one half while all
other primitives are exact.  It is a valid witness because `FPModel` assumes
only the forward-relative standard law. -/
noncomputable def higham9_14_halfUnitDownwardDivisionModel : FPModel where
  u := (1 : ℝ) / 2
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => (x / y) * ((1 : ℝ) - 1 / 2)
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; ring
  model_add := by
    intro x y
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_sub := by
    intro x y
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_mul := by
    intro x y
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_div := by
    intro x y _hy
    refine ⟨-(1 : ℝ) / 2, by norm_num, ?_⟩
    ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, ?_⟩
    ring

/-- Formal model-strength discrepancy behind the remaining source-coefficient
gate in Theorem 9.14.

The PDF rewrites rounded division as
`(1+epsilon) * fl(x/y) = x/y` with `|epsilon| <= u`.  That same-`u` backward
law does not follow from the repository's bare forward-relative `FPModel`:
the valid model above maps `1/1` to `1/2`, which needs `epsilon = 1`. -/
theorem higham9_14_same_u_div_backward_not_from_bare_FPModel :
    ¬ ∃ epsilon : ℝ,
      |epsilon| ≤ higham9_14_halfUnitDownwardDivisionModel.u ∧
        (1 + epsilon) *
            higham9_14_halfUnitDownwardDivisionModel.fl_div 1 1 = 1 := by
  rintro ⟨epsilon, hepsilon, heq⟩
  change |epsilon| ≤ (1 : ℝ) / 2 at hepsilon
  change (1 + epsilon) * ((1 / 1 : ℝ) * (1 - 1 / 2)) = 1 at heq
  have hupper : epsilon ≤ 1 / 2 := le_trans (le_abs_self epsilon) hepsilon
  norm_num at heq
  linarith

end NumStability
