import NumStability.Algorithms.Cholesky.Higham11Chapter9BridgeClosure
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Higham Chapter 11: block-boundary sharp-growth analysis

The last paragraph of Higham section 11.1.1 cites Bunch's detailed analysis:
the element growth of symmetric complete pivoting is at most

`3.07 * (n - 1)^0.446`

times Wilkinson's complete-pivoting LU bound (9.14).  A two-by-two pivot must
remain atomic in that argument.  In particular, duplicating the square root
of its determinant at two fictitious scalar stages is unsound: a one-element
subsegment can cut the block and need not satisfy Hadamard's estimate.

The certificate below therefore records only genuine block boundaries.  A
one-by-one block contributes `detAbs`, while a two-by-two block contributes
`detAbs` with degree two.  Every suffix is certified by the determinant
identity and Hadamard at its *whole* block boundary.  The adjacent-stage field
is the elementary source growth estimate from Higham section 11.1.1.  The
final theorem derives the printed comparison from those local facts; neither
the comparison nor an equivalent ratio estimate is a premise.
-/

open scoped BigOperators

namespace NumStability

private lemma higham11_1_bunchAlpha_ge_6403_div_10000 :
    (6403 : ℝ) / 10000 ≤ higham11_1_bunchParlettAlpha := by
  unfold higham11_1_bunchParlettAlpha bunchParlettAlpha
  have hsqrt : (41224 : ℝ) / 10000 ≤ Real.sqrt 17 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt 17) ^ 2 = 17 := by norm_num
    nlinarith
  linarith

private lemma higham11_1_bunchAlpha_ge_16_div_25 :
    (16 : ℝ) / 25 ≤ higham11_1_bunchParlettAlpha := by
  unfold higham11_1_bunchParlettAlpha bunchParlettAlpha
  have hsqrt : (103 : ℝ) / 25 ≤ Real.sqrt 17 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt 17) ^ 2 = 17 := by norm_num
    nlinarith
  linarith

private lemma higham11_1_neg_log_bunchAlpha_le_223_div_500 :
    -Real.log higham11_1_bunchParlettAlpha ≤ (223 : ℝ) / 500 := by
  let a : ℝ := (6403 : ℝ) / 10000
  let x : ℝ := (3597 : ℝ) / 16403
  have ha_pos : 0 < a := by norm_num [a]
  have hα_pos : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have ha_le : a ≤ higham11_1_bunchParlettAlpha := by
    simpa [a] using higham11_1_bunchAlpha_ge_6403_div_10000
  have hlog_mono : Real.log a ≤ Real.log higham11_1_bunchParlettAlpha :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr ha_pos)
      (Set.mem_Ioi.mpr hα_pos) ha_le
  have hx_nonneg : 0 ≤ x := by norm_num [x]
  have hx_lt_one : x < 1 := by norm_num [x]
  have hseries := Real.log_div_le_sum_range_add hx_nonneg hx_lt_one 3
  have hratio : (1 + x) / (1 - x) = a⁻¹ := by
    norm_num [x, a]
  rw [hratio, Real.log_inv] at hseries
  have hrat :
      2 * ((∑ i ∈ Finset.range 3, x ^ (2 * i + 1) / (2 * i + 1)) +
        x ^ (2 * 3 + 1) / (1 - x ^ 2)) ≤ (223 : ℝ) / 500 := by
    norm_num [x, Finset.sum_range_succ]
  have hnegloga : -Real.log a ≤ (223 : ℝ) / 500 := by
    nlinarith
  linarith

private lemma higham11_1_bunchAlpha_inv_sq_le_307_div_100 :
    higham11_1_bunchParlettAlpha⁻¹ ^ 2 ≤ (307 : ℝ) / 100 := by
  have hα_pos : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hα_lower := higham11_1_bunchAlpha_ge_16_div_25
  rw [inv_pow, inv_eq_one_div, div_le_iff₀ (sq_pos_of_pos hα_pos)]
  nlinarith [sq_nonneg (higham11_1_bunchParlettAlpha - (16 : ℝ) / 25)]

/-- Bunch's modified form of Wilkinson's logarithmic pivot argument.

Compared with the Chapter 9 theorem, the segment maximum is divided by the
pivot threshold `alpha`.  The extra term telescopes as a harmonic sum; this is
the analytic origin of the printed exponent `0.446`. -/
theorem higham11_1_bunch_modified_wilkinson_ratio_bound {n : ℕ} (hn : 1 ≤ n)
    (p : ℕ → ℝ) (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < p k)
    (hpiv : ∀ k, 1 ≤ k → k ≤ n →
      ∏ i ∈ Finset.Icc 1 k, p i ≤
        Real.sqrt ((k : ℝ) ^ k) *
          (p k / higham11_1_bunchParlettAlpha) ^ k) :
    p 1 / p n ≤
      higham9_14_completePivotWilkinsonBound n *
        Real.exp ((-Real.log higham11_1_bunchParlettAlpha) *
          ((harmonic (n - 1) : ℝ) + 1)) := by
  classical
  have hα_pos : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  set q : ℕ → ℝ := fun k => Real.log (p k) with hq
  set Ssum : ℕ → ℝ := fun k => ∑ i ∈ Finset.Icc 1 k, q i with hSsum
  set T : ℕ → ℝ := fun k => Ssum k / (k : ℝ) with hT
  set Hsum : ℝ := ∑ j ∈ Finset.range (n - 1), (1 : ℝ) / ((j : ℝ) + 1) with hHsum
  have hSsucc : ∀ m : ℕ, Ssum (m + 1) = Ssum m + q (m + 1) := by
    intro m
    simp only [hSsum]
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ m + 1)]
  have hlog : ∀ k, 1 ≤ k → k ≤ n →
      Ssum k ≤ (k : ℝ) / 2 * Real.log k + k * q k -
        k * Real.log higham11_1_bunchParlettAlpha := by
    intro k hk1 hkn
    have hmem : ∀ i ∈ Finset.Icc 1 k, 0 < p i := by
      intro i hi
      exact hpos i (Finset.mem_Icc.mp hi).1
        ((Finset.mem_Icc.mp hi).2.trans hkn)
    have hprodpos : 0 < ∏ i ∈ Finset.Icc 1 k, p i := Finset.prod_pos hmem
    have hkpos : (0 : ℝ) < (k : ℝ) ^ k := by positivity
    have hsqrtpos : 0 < Real.sqrt ((k : ℝ) ^ k) := Real.sqrt_pos.mpr hkpos
    have hquotpos : 0 < p k / higham11_1_bunchParlettAlpha :=
      div_pos (hpos k hk1 hkn) hα_pos
    have hquotpowpos : 0 < (p k / higham11_1_bunchParlettAlpha) ^ k :=
      pow_pos hquotpos k
    have hlogle : Real.log (∏ i ∈ Finset.Icc 1 k, p i) ≤
        Real.log (Real.sqrt ((k : ℝ) ^ k) *
          (p k / higham11_1_bunchParlettAlpha) ^ k) :=
      Real.log_le_log hprodpos (hpiv k hk1 hkn)
    have hLHS : Real.log (∏ i ∈ Finset.Icc 1 k, p i) = Ssum k := by
      rw [Real.log_prod (fun i hi => ne_of_gt (hmem i hi)), hSsum]
    have hRHS : Real.log (Real.sqrt ((k : ℝ) ^ k) *
          (p k / higham11_1_bunchParlettAlpha) ^ k) =
        (k : ℝ) / 2 * Real.log k + k * q k -
          k * Real.log higham11_1_bunchParlettAlpha := by
      rw [Real.log_mul (ne_of_gt hsqrtpos) (ne_of_gt hquotpowpos),
        Real.log_sqrt (le_of_lt hkpos), Real.log_pow, Real.log_pow,
        Real.log_div (ne_of_gt (hpos k hk1 hkn)) (ne_of_gt hα_pos), hq]
      push_cast
      ring
    rw [hLHS, hRHS] at hlogle
    exact hlogle
  have hstep : ∀ m : ℕ, 1 ≤ m → m + 1 ≤ n →
      T m - T (m + 1) ≤
        Real.log ((m : ℝ) + 1) / (2 * (m : ℝ)) -
          Real.log higham11_1_bunchParlettAlpha / (m : ℝ) := by
    intro m hm1 hmn
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hm1R : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hc := hlog (m + 1) (by omega) hmn
    rw [hSsucc m] at hc
    push_cast at hc
    have hTm : T m * (m : ℝ) = Ssum m := by
      simp only [hT]
      field_simp
    have hTm1 : T (m + 1) * ((m : ℝ) + 1) = Ssum (m + 1) := by
      simp only [hT]
      push_cast
      field_simp
    rw [hSsucc m] at hTm1
    rw [show Real.log ((m : ℝ) + 1) / (2 * (m : ℝ)) -
        Real.log higham11_1_bunchParlettAlpha / (m : ℝ) =
          (Real.log ((m : ℝ) + 1) / 2 -
            Real.log higham11_1_bunchParlettAlpha) / (m : ℝ) by field_simp]
    rw [le_div_iff₀ hmR]
    nlinarith [hc, hTm, hTm1, hmR, hm1R, mul_pos hmR hm1R]
  have hlast : T n - q n ≤
      Real.log n / 2 - Real.log higham11_1_bunchParlettAlpha := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hc := hlog n hn (le_refl n)
    have hTn : T n * (n : ℝ) = Ssum n := by
      simp only [hT]
      field_simp
    nlinarith [hc, hTn, hnR]
  set F : ℕ → ℝ := fun j => T (j + 1) with hF
  have htele : F 0 - F (n - 1) =
      ∑ j ∈ Finset.range (n - 1), (F j - F (j + 1)) :=
    (Finset.sum_range_sub' F (n - 1)).symm
  have hsum_le : ∑ j ∈ Finset.range (n - 1), (F j - F (j + 1)) ≤
      ∑ j ∈ Finset.range (n - 1),
        (Real.log ((j : ℝ) + 2) / (2 * ((j : ℝ) + 1)) -
          Real.log higham11_1_bunchParlettAlpha / ((j : ℝ) + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjlt : j < n - 1 := Finset.mem_range.mp hj
    have hstepj := hstep (j + 1) (by omega) (by omega)
    have hcast1 : ((j : ℝ) + 1 + 1) = (j : ℝ) + 2 := by ring
    simp only [hF]
    push_cast at hstepj ⊢
    rw [hcast1] at hstepj
    convert hstepj using 2
  have hF0 : F 0 = q 1 := by simp [hF, hT, hSsum]
  have hFn : F (n - 1) = T n := by
    simp only [hF]
    congr 1
    omega
  have hmain : q 1 - q n ≤
      (∑ j ∈ Finset.range (n - 1),
        (Real.log ((j : ℝ) + 2) / (2 * ((j : ℝ) + 1)) -
          Real.log higham11_1_bunchParlettAlpha / ((j : ℝ) + 1))) +
        Real.log n / 2 - Real.log higham11_1_bunchParlettAlpha := by
    have h1 : q 1 - T n ≤
        ∑ j ∈ Finset.range (n - 1),
          (Real.log ((j : ℝ) + 2) / (2 * ((j : ℝ) + 1)) -
            Real.log higham11_1_bunchParlettAlpha / ((j : ℝ) + 1)) := by
      rw [← hF0, ← hFn, htele]
      exact hsum_le
    linarith [h1, hlast]
  have hbound_pos : 0 < higham9_14_completePivotWilkinsonBound n :=
    higham9_14_completePivotWilkinsonBound_pos hn
  have hprod_pos : 0 < higham9_14_completePivotWilkinsonProduct n :=
    higham9_14_completePivotWilkinsonProduct_pos n
  have hprodlog : Real.log (higham9_14_completePivotWilkinsonProduct n) =
      ∑ j ∈ Finset.range (n - 1),
        Real.log ((j : ℝ) + 2) / ((j : ℝ) + 1) := by
    rw [higham9_14_completePivotWilkinsonProduct,
      Real.log_prod (fun k hk => by have := (Finset.mem_Icc.mp hk).1; positivity),
      ← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
      Finset.sum_Ico_eq_sum_range, show n + 1 - 2 = n - 1 from by omega]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.log_rpow (by positivity)]
    push_cast
    rw [show (2 : ℝ) + (j : ℝ) - 1 = (j : ℝ) + 1 from by ring]
    ring
  have hlogbound : Real.log (higham9_14_completePivotWilkinsonBound n) =
      Real.log n / 2 +
        (∑ j ∈ Finset.range (n - 1),
          Real.log ((j : ℝ) + 2) / (2 * ((j : ℝ) + 1))) := by
    rw [higham9_14_completePivotWilkinsonBound,
      Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn)))
        (ne_of_gt (Real.sqrt_pos.mpr hprod_pos)),
      Real.log_sqrt (by positivity), Real.log_sqrt (le_of_lt hprod_pos),
      hprodlog, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [div_div, mul_comm ((j : ℝ) + 1) 2]
  have hHsum_cast : Hsum = (harmonic (n - 1) : ℝ) := by
    simp only [hHsum, harmonic, Rat.cast_sum, Rat.cast_inv]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    rw [one_div]
  have hpositive_extra :
      (∑ j ∈ Finset.range (n - 1),
        Real.log higham11_1_bunchParlettAlpha / ((j : ℝ) + 1)) =
          Real.log higham11_1_bunchParlettAlpha * Hsum := by
    rw [hHsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hmain' : q 1 - q n ≤
      Real.log (higham9_14_completePivotWilkinsonBound n) +
        (-Real.log higham11_1_bunchParlettAlpha) *
          ((harmonic (n - 1) : ℝ) + 1) := by
    rw [Finset.sum_sub_distrib] at hmain
    rw [hpositive_extra, hHsum_cast] at hmain
    rw [hlogbound]
    linarith
  have hp1 : 0 < p 1 := hpos 1 (le_refl 1) hn
  have hpn : 0 < p n := hpos n hn (le_refl n)
  have htarget_pos :
      0 < higham9_14_completePivotWilkinsonBound n *
        Real.exp ((-Real.log higham11_1_bunchParlettAlpha) *
          ((harmonic (n - 1) : ℝ) + 1)) :=
    mul_pos hbound_pos (Real.exp_pos _)
  have hlogtarget :
      Real.log (higham9_14_completePivotWilkinsonBound n *
        Real.exp ((-Real.log higham11_1_bunchParlettAlpha) *
          ((harmonic (n - 1) : ℝ) + 1))) =
      Real.log (higham9_14_completePivotWilkinsonBound n) +
        (-Real.log higham11_1_bunchParlettAlpha) *
          ((harmonic (n - 1) : ℝ) + 1) := by
    rw [Real.log_mul (ne_of_gt hbound_pos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have hlogratio : Real.log (p 1 / p n) ≤
      Real.log (higham9_14_completePivotWilkinsonBound n *
        Real.exp ((-Real.log higham11_1_bunchParlettAlpha) *
          ((harmonic (n - 1) : ℝ) + 1))) := by
    rw [Real.log_div (ne_of_gt hp1) (ne_of_gt hpn), hlogtarget]
    have hqq : q 1 - q n = Real.log (p 1) - Real.log (p n) := by simp [hq]
    rw [← hqq]
    exact hmain'
  have hfin := Real.exp_le_exp.mpr hlogratio
  rwa [Real.exp_log (div_pos hp1 hpn), Real.exp_log htarget_pos] at hfin

/-- The harmonic penalty in the modified Wilkinson argument is bounded by
the two exact rational constants printed in Higham's citation of Bunch. -/
private theorem higham11_1_bunch_harmonic_penalty_le_sharp
    {m : ℕ} (hm : 1 ≤ m) :
    Real.exp ((-Real.log higham11_1_bunchParlettAlpha) *
        ((harmonic m : ℝ) + 1)) ≤
      (307 : ℝ) / 100 * Real.rpow (m : ℝ) ((223 : ℝ) / 500) := by
  have hα_pos : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hα_le_one : higham11_1_bunchParlettAlpha ≤ 1 := by
    exact le_of_lt (by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one)
  have hc_nonneg : 0 ≤ -Real.log higham11_1_bunchParlettAlpha := by
    exact neg_nonneg.mpr (Real.log_nonpos (le_of_lt hα_pos) hα_le_one)
  have hc_le :
      -Real.log higham11_1_bunchParlettAlpha ≤ (223 : ℝ) / 500 :=
    higham11_1_neg_log_bunchAlpha_le_223_div_500
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlogm_nonneg : 0 ≤ Real.log (m : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hm)
  have hH : (harmonic m : ℝ) ≤ 1 + Real.log (m : ℝ) :=
    harmonic_le_one_add_log m
  have hHplus : (harmonic m : ℝ) + 1 ≤ 2 + Real.log (m : ℝ) := by
    linarith
  have hcH :
      (-Real.log higham11_1_bunchParlettAlpha) * ((harmonic m : ℝ) + 1) ≤
        (-Real.log higham11_1_bunchParlettAlpha) *
          (2 + Real.log (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hHplus hc_nonneg
  have hcLog :
      (-Real.log higham11_1_bunchParlettAlpha) * Real.log (m : ℝ) ≤
        ((223 : ℝ) / 500) * Real.log (m : ℝ) :=
    mul_le_mul_of_nonneg_right hc_le hlogm_nonneg
  have hexponent :
      (-Real.log higham11_1_bunchParlettAlpha) * ((harmonic m : ℝ) + 1) ≤
        2 * (-Real.log higham11_1_bunchParlettAlpha) +
          ((223 : ℝ) / 500) * Real.log (m : ℝ) := by
    nlinarith
  have hsingle_exp :
      Real.exp (-Real.log higham11_1_bunchParlettAlpha) =
        higham11_1_bunchParlettAlpha⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hα_pos]
  have hdouble_exp :
      Real.exp (2 * (-Real.log higham11_1_bunchParlettAlpha)) =
        higham11_1_bunchParlettAlpha⁻¹ ^ 2 := by
    calc
      Real.exp (2 * (-Real.log higham11_1_bunchParlettAlpha)) =
          Real.exp (-Real.log higham11_1_bunchParlettAlpha) *
            Real.exp (-Real.log higham11_1_bunchParlettAlpha) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = higham11_1_bunchParlettAlpha⁻¹ ^ 2 := by
        rw [hsingle_exp]
        ring
  calc
    Real.exp ((-Real.log higham11_1_bunchParlettAlpha) *
          ((harmonic m : ℝ) + 1)) ≤
        Real.exp (2 * (-Real.log higham11_1_bunchParlettAlpha) +
          ((223 : ℝ) / 500) * Real.log (m : ℝ)) :=
      Real.exp_le_exp.mpr hexponent
    _ = higham11_1_bunchParlettAlpha⁻¹ ^ 2 *
          Real.rpow (m : ℝ) ((223 : ℝ) / 500) := by
      rw [Real.exp_add, hdouble_exp]
      change higham11_1_bunchParlettAlpha⁻¹ ^ 2 *
          Real.exp (((223 : ℝ) / 500) * Real.log (m : ℝ)) =
        higham11_1_bunchParlettAlpha⁻¹ ^ 2 *
          ((m : ℝ) ^ ((223 : ℝ) / 500))
      rw [Real.rpow_def_of_pos hm_pos]
      congr 1
      ring
    _ ≤ (307 : ℝ) / 100 * Real.rpow (m : ℝ) ((223 : ℝ) / 500) :=
      mul_le_mul_of_nonneg_right higham11_1_bunchAlpha_inv_sq_le_307_div_100
        (Real.rpow_nonneg (le_of_lt hm_pos) _)

/-! ## Genuine block-boundary determinant schedules -/

/-- The elementary one-step growth factor from Higham section 11.1.1.  The
choice of `alpha` makes one two-by-two step no worse than two one-by-one
steps. -/
noncomputable def higham11_1_bunchLocalGrowthFactor : ℝ :=
  1 + higham11_1_bunchParlettAlpha⁻¹

/-- The logarithmic determinant penalty of a one-by-one accepted block. -/
noncomputable def higham11_1_bunchPenaltyOne : ℝ :=
  -Real.log higham11_1_bunchParlettAlpha

/-- The logarithmic determinant penalty per scalar dimension of a genuine
two-by-two accepted block.  The determinant lower bound is
`(1-alpha^2) * stageMax^2`, so this is intentionally not `-log alpha`. -/
noncomputable def higham11_1_bunchPenaltyTwo : ℝ :=
  -Real.log (1 - higham11_1_bunchParlettAlpha ^ 2) / 2

private lemma higham11_1_one_sub_bunchAlpha_sq_ge_589_div_1000 :
    (589 : ℝ) / 1000 ≤ 1 - higham11_1_bunchParlettAlpha ^ 2 := by
  have hsqrt : Real.sqrt 17 ≤ (33 : ℝ) / 8 := by
    rw [show (33 : ℝ) / 8 = Real.sqrt ((33 / 8 : ℝ) ^ 2) from
      (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 33 / 8)).symm]
    exact Real.sqrt_le_sqrt (by norm_num : (17 : ℝ) ≤ (33 / 8) ^ 2)
  have ha_nonneg : 0 ≤ higham11_1_bunchParlettAlpha := by
    exact le_of_lt (by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  have ha_le : higham11_1_bunchParlettAlpha ≤ (41 : ℝ) / 64 := by
    unfold higham11_1_bunchParlettAlpha bunchParlettAlpha
    linarith
  nlinarith [sq_nonneg (higham11_1_bunchParlettAlpha - (41 : ℝ) / 64)]

private lemma higham11_1_bunchPenaltyTwo_le_27_div_100 :
    higham11_1_bunchPenaltyTwo ≤ (27 : ℝ) / 100 := by
  let a : ℝ := (589 : ℝ) / 1000
  let x : ℝ := (411 : ℝ) / 1589
  have ha_pos : 0 < a := by norm_num [a]
  have hactual_pos : 0 < 1 - higham11_1_bunchParlettAlpha ^ 2 := by
    have ha_lt : higham11_1_bunchParlettAlpha < 1 := by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
    have ha_nonneg : 0 ≤ higham11_1_bunchParlettAlpha := by
      exact le_of_lt (by
        simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
    nlinarith
  have ha_le : a ≤ 1 - higham11_1_bunchParlettAlpha ^ 2 := by
    simpa [a] using higham11_1_one_sub_bunchAlpha_sq_ge_589_div_1000
  have hlog_mono : Real.log a ≤
      Real.log (1 - higham11_1_bunchParlettAlpha ^ 2) :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr ha_pos)
      (Set.mem_Ioi.mpr hactual_pos) ha_le
  have hx_nonneg : 0 ≤ x := by norm_num [x]
  have hx_lt_one : x < 1 := by norm_num [x]
  have hseries := Real.log_div_le_sum_range_add hx_nonneg hx_lt_one 2
  have hratio : (1 + x) / (1 - x) = a⁻¹ := by
    norm_num [x, a]
  rw [hratio, Real.log_inv] at hseries
  have hrat :
      2 * ((∑ i ∈ Finset.range 2, x ^ (2 * i + 1) / (2 * i + 1)) +
        x ^ (2 * 2 + 1) / (1 - x ^ 2)) ≤ (54 : ℝ) / 100 := by
    norm_num [x, Finset.sum_range_succ]
  have hnega : -Real.log a ≤ (54 : ℝ) / 100 := by
    nlinarith
  unfold higham11_1_bunchPenaltyTwo
  nlinarith

private lemma higham11_1_bunchPenaltyOne_le_exponent :
    higham11_1_bunchPenaltyOne ≤ (223 : ℝ) / 500 := by
  exact higham11_1_neg_log_bunchAlpha_le_223_div_500

private lemma higham11_1_bunchPenaltyTwo_le_exponent :
    higham11_1_bunchPenaltyTwo ≤ (223 : ℝ) / 500 := by
  exact higham11_1_bunchPenaltyTwo_le_27_div_100.trans (by norm_num)

private lemma higham11_1_bunchLocalGrowthFactor_pos :
    0 < higham11_1_bunchLocalGrowthFactor := by
  unfold higham11_1_bunchLocalGrowthFactor
  have ha : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  positivity

private lemma higham11_1_bunchLocalGrowthFactor_ge_one :
    1 ≤ higham11_1_bunchLocalGrowthFactor := by
  unfold higham11_1_bunchLocalGrowthFactor
  have ha : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  exact le_add_of_nonneg_right (inv_nonneg.mpr (le_of_lt ha))

private lemma higham11_1_log_bunchLocalGrowthFactor_le_19_div_20 :
    Real.log higham11_1_bunchLocalGrowthFactor ≤ (19 : ℝ) / 20 := by
  have ha : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have halower := higham11_1_bunchAlpha_ge_16_div_25
  have hg_le : higham11_1_bunchLocalGrowthFactor ≤ (41 : ℝ) / 16 := by
    unfold higham11_1_bunchLocalGrowthFactor
    have hinv : higham11_1_bunchParlettAlpha⁻¹ ≤ (25 : ℝ) / 16 := by
      rw [inv_le_iff_one_le_mul₀ ha]
      nlinarith
    linarith
  let x : ℝ := (25 : ℝ) / 57
  have hx_nonneg : 0 ≤ x := by norm_num [x]
  have hx_lt_one : x < 1 := by norm_num [x]
  have hseries := Real.log_div_le_sum_range_add hx_nonneg hx_lt_one 3
  have hratio : (1 + x) / (1 - x) = (41 : ℝ) / 16 := by
    norm_num [x]
  rw [hratio] at hseries
  have hrat :
      2 * ((∑ i ∈ Finset.range 3, x ^ (2 * i + 1) / (2 * i + 1)) +
        x ^ (2 * 3 + 1) / (1 - x ^ 2)) ≤ (19 : ℝ) / 20 := by
    norm_num [x, Finset.sum_range_succ]
  have hlog_upper : Real.log ((41 : ℝ) / 16) ≤ (19 : ℝ) / 20 := by
    nlinarith [hseries, hrat]
  have hg_pos := higham11_1_bunchLocalGrowthFactor_pos
  have hfortyone_pos : (0 : ℝ) < 41 / 16 := by norm_num
  exact (Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hg_pos)
    (Set.mem_Ioi.mpr hfortyone_pos) hg_le).trans hlog_upper

private lemma higham11_1_log_two_ge_two_thirds :
    (2 : ℝ) / 3 ≤ Real.log 2 := by
  let x : ℝ := (1 : ℝ) / 3
  have h := Real.sum_range_le_log_div (by norm_num [x] : 0 ≤ x)
    (by norm_num [x] : x < 1) 1
  have hratio : (1 + x) / (1 - x) = (2 : ℝ) := by norm_num [x]
  rw [hratio] at h
  norm_num [x, Finset.sum_range_succ] at h ⊢
  linarith

private lemma higham11_1_log_three_ge_one :
    (1 : ℝ) ≤ Real.log 3 := by
  let x : ℝ := (1 : ℝ) / 2
  have h := Real.sum_range_le_log_div (by norm_num [x] : 0 ≤ x)
    (by norm_num [x] : x < 1) 1
  have hratio : (1 + x) / (1 - x) = (3 : ℝ) := by norm_num [x]
  rw [hratio] at h
  norm_num [x, Finset.sum_range_succ] at h ⊢
  linarith

private lemma higham11_1_log_307_div_100_ge_one :
    (1 : ℝ) ≤ Real.log ((307 : ℝ) / 100) := by
  have hthree_pos : (0 : ℝ) < 3 := by norm_num
  have h307_pos : (0 : ℝ) < 307 / 100 := by norm_num
  have hmono : Real.log (3 : ℝ) ≤ Real.log ((307 : ℝ) / 100) :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hthree_pos)
      (Set.mem_Ioi.mpr h307_pos) (by norm_num)
  exact higham11_1_log_three_ge_one.trans hmono

/-- One genuine Algorithm 11.1 pivot block. -/
structure Higham11BunchSharpBlock where
  width : ℕ
  stageMax : ℝ
  detAbs : ℝ
  width_one_or_two : width = 1 ∨ width = 2
  stageMax_pos : 0 < stageMax
  detAbs_pos : 0 < detAbs
  one_det_lower : width = 1 →
    higham11_1_bunchParlettAlpha * stageMax ≤ detAbs
  two_det_lower : width = 2 →
    (1 - higham11_1_bunchParlettAlpha ^ 2) * stageMax ^ 2 ≤ detAbs

namespace Higham11BunchSharpBlock

noncomputable def penalty (b : Higham11BunchSharpBlock) : ℝ :=
  if b.width = 1 then higham11_1_bunchPenaltyOne
  else higham11_1_bunchPenaltyTwo

theorem width_pos (b : Higham11BunchSharpBlock) : 0 < b.width := by
  rcases b.width_one_or_two with h | h <;> omega

theorem width_le_two (b : Higham11BunchSharpBlock) : b.width ≤ 2 := by
  rcases b.width_one_or_two with h | h <;> omega

end Higham11BunchSharpBlock

/-- A nonempty elimination-order chain from an earlier active matrix (the
head) to a later active matrix (the last block).  Every constructor records a
Hadamard bound for the whole suffix ending at that last block.  Consequently
no hypothesis ever cuts a two-by-two block. -/
inductive Higham11BunchSharpBlockCertificate :
    List Higham11BunchSharpBlock → Prop
  | singleton (b : Higham11BunchSharpBlock)
      (hadamard : b.detAbs ≤
        Real.sqrt (((b.width : ℝ) ^ b.width)) *
          b.stageMax ^ b.width) :
      Higham11BunchSharpBlockCertificate [b]
  | cons (b next : Higham11BunchSharpBlock)
      (rest : List Higham11BunchSharpBlock)
      (tail : Higham11BunchSharpBlockCertificate (next :: rest))
      (local_growth : next.stageMax ≤
        higham11_1_bunchLocalGrowthFactor ^ b.width * b.stageMax)
      (hadamard : b.detAbs * ((next :: rest).map (·.detAbs)).prod ≤
        Real.sqrt (((b.width + ((next :: rest).map (·.width)).sum : ℕ) : ℝ) ^
          (b.width + ((next :: rest).map (·.width)).sum)) *
        b.stageMax ^ (b.width + ((next :: rest).map (·.width)).sum)) :
      Higham11BunchSharpBlockCertificate (b :: next :: rest)

namespace Higham11BunchSharpBlockCertificate

noncomputable def totalWidth (blocks : List Higham11BunchSharpBlock) : ℕ :=
  (blocks.map (·.width)).sum

noncomputable def detProduct (blocks : List Higham11BunchSharpBlock) : ℝ :=
  (blocks.map (·.detAbs)).prod

noncomputable def adjustedLogSum
    (blocks : List Higham11BunchSharpBlock) : ℝ :=
  (blocks.map (fun b =>
    (b.width : ℝ) * (Real.log b.stageMax - b.penalty))).sum

def eliminatedWidth : List Higham11BunchSharpBlock → ℕ
  | [] => 0
  | [_] => 0
  | b :: next :: rest => b.width + eliminatedWidth (next :: rest)

def boundaryMoment : List Higham11BunchSharpBlock → ℕ
  | [] => 0
  | [_] => 0
  | b :: next :: rest =>
      b.width * (b.width + eliminatedWidth (next :: rest)) +
        boundaryMoment (next :: rest)

def firstMax : List Higham11BunchSharpBlock → ℝ
  | [] => 0
  | b :: _ => b.stageMax

def lastMax : List Higham11BunchSharpBlock → ℝ
  | [] => 0
  | [b] => b.stageMax
  | _ :: next :: rest => lastMax (next :: rest)

theorem nonempty {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) : blocks ≠ [] := by
  cases cert <;> simp

theorem totalWidth_pos {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    0 < totalWidth blocks := by
  cases cert with
  | singleton b _ => simpa [totalWidth] using b.width_pos
  | cons b next rest tail _ _ =>
      simp only [totalWidth, List.map_cons, List.sum_cons]
      exact Nat.add_pos_left b.width_pos _

theorem firstMax_pos {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    0 < firstMax blocks := by
  cases cert with
  | singleton b _ => simpa [firstMax] using b.stageMax_pos
  | cons b next rest tail local_growth hadamard =>
      simpa [firstMax] using b.stageMax_pos

theorem lastMax_pos {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    0 < lastMax blocks := by
  induction cert with
  | singleton b _ => simpa [lastMax] using b.stageMax_pos
  | cons b next rest tail _ _ ih => simpa [lastMax] using ih

private theorem one_sub_alpha_sq_pos :
    0 < 1 - higham11_1_bunchParlettAlpha ^ 2 := by
  have ha0 : 0 ≤ higham11_1_bunchParlettAlpha := by
    exact le_of_lt (by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  have ha1 : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  nlinarith

private theorem block_adjusted_log_le_log_det
    (b : Higham11BunchSharpBlock) :
    (b.width : ℝ) * (Real.log b.stageMax - b.penalty) ≤
      Real.log b.detAbs := by
  rcases b.width_one_or_two with hw | hw
  · have hw' : b.width = 1 := hw
    have ha : 0 < higham11_1_bunchParlettAlpha := by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
    have hprod : 0 < higham11_1_bunchParlettAlpha * b.stageMax :=
      mul_pos ha b.stageMax_pos
    have hlog := Real.log_le_log hprod (b.one_det_lower hw')
    rw [Real.log_mul (ne_of_gt ha) (ne_of_gt b.stageMax_pos)] at hlog
    simpa [Higham11BunchSharpBlock.penalty, hw',
      higham11_1_bunchPenaltyOne, add_comm] using hlog
  · have hw' : b.width = 2 := hw
    have hbeta := one_sub_alpha_sq_pos
    have hprod : 0 <
        (1 - higham11_1_bunchParlettAlpha ^ 2) * b.stageMax ^ 2 :=
      mul_pos hbeta (sq_pos_of_pos b.stageMax_pos)
    have hlog := Real.log_le_log hprod (b.two_det_lower hw')
    rw [Real.log_mul (ne_of_gt hbeta) (ne_of_gt (sq_pos_of_pos b.stageMax_pos)),
      Real.log_pow] at hlog
    simp only [Higham11BunchSharpBlock.penalty, hw',
      if_neg (by norm_num : (2 : ℕ) ≠ 1),
      higham11_1_bunchPenaltyTwo, Nat.cast_ofNat]
    convert hlog using 1 <;> ring

private theorem detProduct_pos
    (blocks : List Higham11BunchSharpBlock) :
    0 < detProduct blocks := by
  induction blocks with
  | nil => simp [detProduct]
  | cons b rest ih =>
      simpa [detProduct] using mul_pos b.detAbs_pos ih

private theorem adjustedLogSum_le_log_detProduct
    (blocks : List Higham11BunchSharpBlock) :
    adjustedLogSum blocks ≤ Real.log (detProduct blocks) := by
  induction blocks with
  | nil => simp [adjustedLogSum, detProduct]
  | cons b rest ih =>
      have hb := block_adjusted_log_le_log_det b
      have htail := detProduct_pos rest
      rw [show detProduct (b :: rest) = b.detAbs * detProduct rest by
        simp [detProduct], Real.log_mul (ne_of_gt b.detAbs_pos) (ne_of_gt htail)]
      simpa [adjustedLogSum] using add_le_add hb ih

private theorem certificate_hadamard
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    detProduct blocks ≤
      Real.sqrt (((totalWidth blocks : ℕ) : ℝ) ^ totalWidth blocks) *
        firstMax blocks ^ totalWidth blocks := by
  cases cert with
  | singleton b h => simpa [detProduct, totalWidth, firstMax] using h
  | cons b next rest tail local_growth h =>
      simpa [detProduct, totalWidth, firstMax] using h

/-- Determinant acceptance plus Hadamard at a genuine block boundary, in the
weighted logarithmic form used by Bunch's argument. -/
theorem adjustedLogSum_le_boundary
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    adjustedLogSum blocks ≤
      (totalWidth blocks : ℝ) / 2 * Real.log (totalWidth blocks : ℝ) +
        (totalWidth blocks : ℝ) * Real.log (firstMax blocks) := by
  let d := totalWidth blocks
  have hdN : 0 < d := totalWidth_pos cert
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdN
  have hm := firstMax_pos cert
  have hpow : 0 < (d : ℝ) ^ d := pow_pos hdR _
  have hsqrt : 0 < Real.sqrt ((d : ℝ) ^ d) := Real.sqrt_pos.mpr hpow
  have hrhs : 0 < Real.sqrt ((d : ℝ) ^ d) * firstMax blocks ^ d :=
    mul_pos hsqrt (pow_pos hm _)
  have hlogdet : Real.log (detProduct blocks) ≤
      Real.log (Real.sqrt ((d : ℝ) ^ d) * firstMax blocks ^ d) :=
    Real.log_le_log (detProduct_pos blocks) (by
      simpa [d] using certificate_hadamard cert)
  have hlogrhs :
      Real.log (Real.sqrt ((d : ℝ) ^ d) * firstMax blocks ^ d) =
        (d : ℝ) / 2 * Real.log (d : ℝ) +
          (d : ℝ) * Real.log (firstMax blocks) := by
    rw [Real.log_mul (ne_of_gt hsqrt) (ne_of_gt (pow_pos hm d)),
      Real.log_sqrt (le_of_lt hpow), Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [hlogrhs] at hlogdet
  exact (adjustedLogSum_le_log_detProduct blocks).trans hlogdet

private theorem block_penalty_le_exponent (b : Higham11BunchSharpBlock) :
    b.penalty ≤ (223 : ℝ) / 500 := by
  rcases b.width_one_or_two with hw | hw
  · simpa [Higham11BunchSharpBlock.penalty, hw] using
      higham11_1_bunchPenaltyOne_le_exponent
  · simp only [Higham11BunchSharpBlock.penalty, hw,
      if_neg (by norm_num : (2 : ℕ) ≠ 1)]
    exact higham11_1_bunchPenaltyTwo_le_exponent

private theorem local_log_growth
    (b next : Higham11BunchSharpBlock)
    (h : next.stageMax ≤
      higham11_1_bunchLocalGrowthFactor ^ b.width * b.stageMax) :
    Real.log next.stageMax - Real.log b.stageMax ≤
      (b.width : ℝ) * Real.log higham11_1_bunchLocalGrowthFactor := by
  have hg := higham11_1_bunchLocalGrowthFactor_pos
  have hpow := pow_pos hg b.width
  have hrhs := mul_pos hpow b.stageMax_pos
  have hlog := Real.log_le_log next.stageMax_pos h
  rw [Real.log_mul (ne_of_gt hpow) (ne_of_gt b.stageMax_pos),
    Real.log_pow] at hlog
  push_cast at hlog
  linarith

private theorem eliminatedWidth_lt_totalWidth
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    eliminatedWidth blocks < totalWidth blocks := by
  induction cert with
  | singleton b hadamard =>
      simp [eliminatedWidth, totalWidth, b.width_pos]
  | cons b next rest tail local_growth hadamard ih =>
      change b.width + eliminatedWidth (next :: rest) <
        b.width + totalWidth (next :: rest)
      exact Nat.add_lt_add_left ih b.width

private theorem last_log_sub_first_log_le
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    Real.log (lastMax blocks) - Real.log (firstMax blocks) ≤
      (eliminatedWidth blocks : ℝ) *
        Real.log higham11_1_bunchLocalGrowthFactor := by
  induction cert with
  | singleton b hadamard => simp [lastMax, firstMax, eliminatedWidth]
  | cons b next rest tail local_growth hadamard ih =>
      have hlocal := local_log_growth b next local_growth
      have ih' : Real.log (lastMax (next :: rest)) - Real.log next.stageMax ≤
          (eliminatedWidth (next :: rest) : ℝ) *
            Real.log higham11_1_bunchLocalGrowthFactor := by
        simpa [firstMax] using ih
      calc
        Real.log (lastMax (b :: next :: rest)) -
            Real.log (firstMax (b :: next :: rest)) =
          (Real.log (lastMax (next :: rest)) - Real.log next.stageMax) +
            (Real.log next.stageMax - Real.log b.stageMax) := by
              simp only [lastMax, firstMax]
              ring
        _ ≤ (eliminatedWidth (next :: rest) : ℝ) *
              Real.log higham11_1_bunchLocalGrowthFactor +
            (b.width : ℝ) *
              Real.log higham11_1_bunchLocalGrowthFactor :=
          add_le_add ih' hlocal
        _ = (eliminatedWidth (b :: next :: rest) : ℝ) *
              Real.log higham11_1_bunchLocalGrowthFactor := by
          simp only [eliminatedWidth, Nat.cast_add]
          ring

private theorem boundaryMoment_core_bound
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    2 * boundaryMoment blocks ≤
      eliminatedWidth blocks ^ 2 + 2 * eliminatedWidth blocks := by
  induction cert with
  | singleton b hadamard => simp [boundaryMoment, eliminatedWidth]
  | cons b next rest tail local_growth hadamard ih =>
      simp only [boundaryMoment, eliminatedWidth]
      rcases b.width_one_or_two with hw | hw
      · simp only [hw]
        nlinarith
      · simp only [hw]
        nlinarith

private theorem boundaryMoment_total_bound
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    2 * boundaryMoment blocks ≤ totalWidth blocks ^ 2 - 1 := by
  have hcore := boundaryMoment_core_bound cert
  have hlt := eliminatedWidth_lt_totalWidth cert
  have hsucc : eliminatedWidth blocks + 1 ≤ totalWidth blocks := by omega
  have hsq : (eliminatedWidth blocks + 1) ^ 2 ≤
      totalWidth blocks ^ 2 := Nat.pow_le_pow_left hsucc 2
  apply Nat.le_sub_of_add_le
  calc
    2 * boundaryMoment blocks + 1 ≤
        (eliminatedWidth blocks ^ 2 + 2 * eliminatedWidth blocks) + 1 :=
      Nat.add_le_add_right hcore 1
    _ = (eliminatedWidth blocks + 1) ^ 2 := by ring
    _ ≤ totalWidth blocks ^ 2 := hsq

/-- The elementary exponential growth estimate controls the adjusted
logarithmic gap at the small boundary totals where the sharp potential has not
yet entered its monotone regime. -/
private theorem local_adjusted_gap_scaled
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    (totalWidth blocks : ℝ) * Real.log (lastMax blocks) -
        adjustedLogSum blocks ≤
      (boundaryMoment blocks : ℝ) *
          Real.log higham11_1_bunchLocalGrowthFactor +
        (totalWidth blocks : ℝ) * ((223 : ℝ) / 500) := by
  induction cert with
  | singleton b hadamard =>
      have hp := block_penalty_le_exponent b
      have hmul := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg b.width)
      convert hmul using 1 <;>
        simp [totalWidth, adjustedLogSum, lastMax, boundaryMoment] <;> ring
  | cons b next rest tail local_growth hadamard ih =>
      have hg := last_log_sub_first_log_le
        (Higham11BunchSharpBlockCertificate.cons b next rest tail
          local_growth hadamard)
      simp only [lastMax, firstMax, eliminatedWidth, Nat.cast_add] at hg
      have hp := block_penalty_le_exponent b
      have hhead :
          (b.width : ℝ) *
              (Real.log (lastMax (next :: rest)) - Real.log b.stageMax +
                b.penalty) ≤
            (b.width : ℝ) *
              (((b.width + eliminatedWidth (next :: rest) : ℕ) : ℝ) *
                  Real.log higham11_1_bunchLocalGrowthFactor +
                (223 : ℝ) / 500) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        push_cast
        linarith
      calc
        (totalWidth (b :: next :: rest) : ℝ) *
              Real.log (lastMax (b :: next :: rest)) -
            adjustedLogSum (b :: next :: rest) =
          ((totalWidth (next :: rest) : ℝ) *
              Real.log (lastMax (next :: rest)) -
            adjustedLogSum (next :: rest)) +
          (b.width : ℝ) *
            (Real.log (lastMax (next :: rest)) - Real.log b.stageMax +
              b.penalty) := by
          simp only [totalWidth, adjustedLogSum, lastMax, List.map_cons,
            List.sum_cons, Nat.cast_add]
          ring
        _ ≤ ((boundaryMoment (next :: rest) : ℝ) *
              Real.log higham11_1_bunchLocalGrowthFactor +
            (totalWidth (next :: rest) : ℝ) * ((223 : ℝ) / 500)) +
          (b.width : ℝ) *
            (((b.width + eliminatedWidth (next :: rest) : ℕ) : ℝ) *
                Real.log higham11_1_bunchLocalGrowthFactor +
              (223 : ℝ) / 500) := add_le_add ih hhead
        _ = (boundaryMoment (b :: next :: rest) : ℝ) *
              Real.log higham11_1_bunchLocalGrowthFactor +
            (totalWidth (b :: next :: rest) : ℝ) *
              ((223 : ℝ) / 500) := by
          simp only [boundaryMoment, totalWidth, eliminatedWidth,
            List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul]
          ring

/-! ## The block-boundary sharp potential -/

noncomputable def wilkinsonLogSteps (d : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (d - 1),
    Real.log ((j + 2 : ℕ) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ))

noncomputable def sharpLogPotential (d : ℕ) : ℝ :=
  wilkinsonLogSteps d +
    ((223 : ℝ) / 500) * Real.log ((d - 1 : ℕ) : ℝ) +
    Real.log ((307 : ℝ) / 100)

noncomputable def adjustedMean
    (blocks : List Higham11BunchSharpBlock) : ℝ :=
  adjustedLogSum blocks / (totalWidth blocks : ℝ)

private theorem adjustedMean_cons_step
    (b next : Higham11BunchSharpBlock)
    (rest : List Higham11BunchSharpBlock)
    (tail : Higham11BunchSharpBlockCertificate (next :: rest))
    (local_growth : next.stageMax ≤
      higham11_1_bunchLocalGrowthFactor ^ b.width * b.stageMax)
    (hadamard : b.detAbs * ((next :: rest).map (·.detAbs)).prod ≤
      Real.sqrt (((b.width + ((next :: rest).map (·.width)).sum : ℕ) : ℝ) ^
        (b.width + ((next :: rest).map (·.width)).sum)) *
      b.stageMax ^ (b.width + ((next :: rest).map (·.width)).sum)) :
    adjustedMean (next :: rest) - adjustedMean (b :: next :: rest) ≤
      (b.width : ℝ) *
          Real.log ((b.width + totalWidth (next :: rest) : ℕ) : ℝ) /
            (2 * (totalWidth (next :: rest) : ℝ)) +
        (b.width : ℝ) * b.penalty /
          (totalWidth (next :: rest) : ℝ) := by
  let d : ℝ := totalWidth (next :: rest)
  let w : ℝ := b.width
  let D : ℝ := b.width + totalWidth (next :: rest)
  let A : ℝ := adjustedLogSum (next :: rest)
  let q : ℝ := Real.log b.stageMax
  let c : ℝ := b.penalty
  have hdN : 0 < totalWidth (next :: rest) := totalWidth_pos tail
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hdN
  have hw : 0 < w := by
    dsimp [w]
    exact_mod_cast b.width_pos
  have hD : 0 < D := by dsimp [D, d, w]; positivity
  let whole := Higham11BunchSharpBlockCertificate.cons b next rest tail
    local_growth hadamard
  have hboundary := adjustedLogSum_le_boundary whole
  have hboundary' :
      w * (q - c) + A ≤ D / 2 * Real.log D + D * q := by
    simpa [w, q, c, A, D, d, totalWidth, adjustedLogSum, firstMax,
      Nat.cast_add] using hboundary
  have hcore : A - d * (q - c) ≤
      D / 2 * Real.log D + D * c := by
    have hDw : D = w + d := by rfl
    nlinarith
  have hfactor : 0 ≤ w / (d * D) := by positivity
  have htailWidth : (totalWidth (next :: rest) : ℝ) = d := rfl
  have hwholeWidth : (totalWidth (b :: next :: rest) : ℝ) = D := by
    simp [totalWidth, D, w, d]
  have hwholeAdjusted : adjustedLogSum (b :: next :: rest) =
      w * (q - c) + A := by
    simp only [adjustedLogSum, List.map_cons, List.sum_cons]
    rfl
  calc
    adjustedMean (next :: rest) - adjustedMean (b :: next :: rest) =
        (w / (d * D)) * (A - d * (q - c)) := by
      unfold adjustedMean
      rw [htailWidth, hwholeWidth, hwholeAdjusted]
      change A / d - (w * (q - c) + A) / D =
        (w / (d * D)) * (A - d * (q - c))
      field_simp [ne_of_gt hd, ne_of_gt hD]
      ring
    _ ≤ (w / (d * D)) *
        (D / 2 * Real.log D + D * c) :=
      mul_le_mul_of_nonneg_left hcore hfactor
    _ = (b.width : ℝ) *
          Real.log ((b.width + totalWidth (next :: rest) : ℕ) : ℝ) /
            (2 * (totalWidth (next :: rest) : ℝ)) +
        (b.width : ℝ) * b.penalty /
          (totalWidth (next :: rest) : ℝ) := by
      rw [show (((b.width + totalWidth (next :: rest) : ℕ) : ℝ)) = D by
          simp [D, w, d], htailWidth]
      change (w / (d * D)) * (D / 2 * Real.log D + D * c) =
        w * Real.log D / (2 * d) + w * c / d
      field_simp [ne_of_gt hd, ne_of_gt hD]

private theorem wilkinsonLogSteps_succ {d : ℕ} (hd : 1 ≤ d) :
    wilkinsonLogSteps (d + 1) = wilkinsonLogSteps d +
      Real.log ((d + 1 : ℕ) : ℝ) / (2 * (d : ℝ)) := by
  unfold wilkinsonLogSteps
  rw [show d + 1 - 1 = d by omega, show d = (d - 1) + 1 by omega,
    Finset.sum_range_succ]
  push_cast
  ring

private theorem log_symmetric_ratio_lower {d : ℕ} (hd : 1 < d) :
    (2 : ℝ) / d ≤
      Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
  let x : ℝ := 1 / (d : ℝ)
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hx_nonneg : 0 ≤ x := by positivity
  have hx_lt_one : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by positivity)]
    exact hdR
  have hseries := Real.sum_range_le_log_div hx_nonneg hx_lt_one 1
  have hratio : (1 + x) / (1 - x) =
      (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
    dsimp [x]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    field_simp
    <;> nlinarith
  rw [hratio] at hseries
  norm_num [Finset.sum_range_succ] at hseries
  dsimp [x] at hseries
  have hseries' :
      1 / (d : ℝ) ≤ 1 / 2 *
        Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hseries
  calc
    (2 : ℝ) / d = 2 * (1 / (d : ℝ)) := by ring
    _ ≤ 2 * (1 / 2 *
        Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hseries' (by norm_num)
    _ = Real.log (((d + 1 : ℕ) : ℝ) /
        ((d - 1 : ℕ) : ℝ)) := by ring

private theorem one_div_le_log_self_div_pred {d : ℕ} (hd : 2 ≤ d) :
    (1 : ℝ) / d ≤
      Real.log ((d : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
  have h := log_symmetric_ratio_lower (d := 2 * d - 1) (by omega)
  have hdenN : 0 < 2 * d - 1 := by omega
  have hdenR : (0 : ℝ) < ((2 * d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hdenN
  have hdR : (0 : ℝ) < d := by positivity
  have hleft : (1 : ℝ) / d ≤ (2 : ℝ) / (2 * d - 1 : ℕ) := by
    rw [div_le_div_iff₀ hdR hdenR]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * d)]
    push_cast
    nlinarith
  have hratio :
      ((((2 * d - 1) + 1 : ℕ) : ℝ) /
          (((2 * d - 1) - 1 : ℕ) : ℝ)) =
        (d : ℝ) / ((d - 1 : ℕ) : ℝ) := by
    rw [show (2 * d - 1) + 1 = 2 * d by omega,
      show (2 * d - 1) - 1 = 2 * (d - 1) by omega]
    push_cast
    field_simp
  rw [hratio] at h
  exact hleft.trans h

private theorem width_one_potential_step {d : ℕ} (hd : 2 ≤ d) :
    sharpLogPotential d +
        (Real.log ((d + 1 : ℕ) : ℝ) / (2 * (d : ℝ)) +
          higham11_1_bunchPenaltyOne / (d : ℝ)) ≤
      sharpLogPotential (d + 1) := by
  have hdR : (0 : ℝ) < d := by positivity
  have hlog := one_div_le_log_self_div_pred hd
  have hc := higham11_1_bunchPenaltyOne_le_exponent
  have hcdiv : higham11_1_bunchPenaltyOne / (d : ℝ) ≤
      ((223 : ℝ) / 500) *
        Real.log ((d : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
    have h1 : higham11_1_bunchPenaltyOne / (d : ℝ) ≤
        ((223 : ℝ) / 500) / (d : ℝ) :=
      div_le_div_of_nonneg_right hc (le_of_lt hdR)
    have h2 : ((223 : ℝ) / 500) / (d : ℝ) ≤
        ((223 : ℝ) / 500) *
          Real.log ((d : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hlog)
        (by norm_num)
    exact h1.trans h2
  have hlogdiv :
      Real.log ((d : ℝ) / ((d - 1 : ℕ) : ℝ)) =
        Real.log (d : ℝ) - Real.log ((d - 1 : ℕ) : ℝ) := by
    have hpred : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < d - 1)
    rw [Real.log_div (ne_of_gt hdR) (ne_of_gt hpred)]
  rw [hlogdiv] at hcdiv
  have hs := wilkinsonLogSteps_succ (d := d) (by omega : 1 ≤ d)
  rw [sharpLogPotential, sharpLogPotential, hs]
  have hsub : d + 1 - 1 = d := by omega
  rw [hsub]
  linarith

private theorem log_five_le_five_thirds :
    Real.log 5 ≤ (5 : ℝ) / 3 := by
  let x : ℝ := (2 : ℝ) / 3
  have hx_nonneg : 0 ≤ x := by norm_num [x]
  have hx_lt_one : x < 1 := by norm_num [x]
  have hseries := Real.log_div_le_sum_range_add hx_nonneg hx_lt_one 5
  have hratio : (1 + x) / (1 - x) = (5 : ℝ) := by norm_num [x]
  rw [hratio] at hseries
  have hrat :
      2 * ((∑ i ∈ Finset.range 5, x ^ (2 * i + 1) / (2 * i + 1)) +
        x ^ (2 * 5 + 1) / (1 - x ^ 2)) ≤ (5 : ℝ) / 3 := by
    norm_num [x, Finset.sum_range_succ]
  nlinarith

private theorem log_d_add_two_div_d_add_one_le_five_twelfths
    {d : ℕ} (hd : 3 ≤ d) :
    Real.log ((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ) ≤
      (5 : ℝ) / 12 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hratio_pos : (0 : ℝ) < ((d + 2 : ℕ) : ℝ) / 5 := by positivity
  have hlogratio := Real.log_le_sub_one_of_pos hratio_pos
  have hdecomp :
      Real.log ((d + 2 : ℕ) : ℝ) =
        Real.log 5 + Real.log (((d + 2 : ℕ) : ℝ) / 5) := by
    rw [← Real.log_mul (by norm_num : (5 : ℝ) ≠ 0)
      (ne_of_gt hratio_pos)]
    congr 1
    field_simp
  rw [hdecomp]
  have hden_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hden_pos]
  push_cast at hlogratio ⊢
  nlinarith [log_five_le_five_thirds]

private theorem log_d_add_two_ratio_le_one_fourth {d : ℕ} (hd : 3 ≤ d) :
    Real.log (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) ≤
      (1 : ℝ) / 4 := by
  have hratio_pos : (0 : ℝ) <
      ((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos hratio_pos
  have hlog_nonneg : 0 ≤
      Real.log (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg (by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((d + 1 : ℕ) : ℝ))]
      push_cast
      norm_num)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  push_cast at h
  have hden : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hfrac :
      ((d : ℝ) + 2) / ((d : ℝ) + 1) - 1 = 1 / ((d : ℝ) + 1) := by
    field_simp
    ring
  rw [hfrac] at h
  have hmul :
      Real.log (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) *
          ((d : ℝ) + 1) ≤ 1 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      (le_div_iff₀ hden).mp h
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  calc
    Real.log (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) * 4 ≤
        ((d : ℝ) + 1) *
          Real.log (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
      nlinarith
    _ ≤ 1 := by simpa only [mul_comm] using hmul

private theorem width_two_raw_potential_step {d : ℕ} (hd : 3 ≤ d) :
    Real.log ((d + 2 : ℕ) : ℝ) / (d : ℝ) +
        2 * higham11_1_bunchPenaltyTwo / (d : ℝ) ≤
      Real.log ((d + 1 : ℕ) : ℝ) / (2 * (d : ℝ)) +
        Real.log ((d + 2 : ℕ) : ℝ) / (2 * ((d + 1 : ℕ) : ℝ)) +
        ((223 : ℝ) / 500) *
          Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hloglower := log_symmetric_ratio_lower (d := d) (by omega)
  have hsmall := log_d_add_two_ratio_le_one_fourth (d := d) hd
  have hlarge := log_d_add_two_div_d_add_one_le_five_twelfths (d := d) hd
  have hc := higham11_1_bunchPenaltyTwo_le_27_div_100
  have hlogeq :
      Real.log ((d + 2 : ℕ) : ℝ) -
          Real.log ((d + 1 : ℕ) : ℝ) =
        Real.log (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity)]
  have hscaled :
      Real.log (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) / 2 +
          (Real.log ((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) / 2 +
          2 * higham11_1_bunchPenaltyTwo ≤
        ((223 : ℝ) / 500) * (d : ℝ) *
          Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
    have hlrscaled :
        (2 : ℝ) ≤ (d : ℝ) *
          Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
      simpa only [mul_comm] using (div_le_iff₀ hdR).mp hloglower
    have hleftUpper :
        Real.log (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) / 2 +
            (Real.log ((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) / 2 +
            2 * higham11_1_bunchPenaltyTwo ≤ (131 : ℝ) / 150 := by
      nlinarith
    have hrightLower :
        (223 : ℝ) / 250 ≤
          ((223 : ℝ) / 500) * (d : ℝ) *
            Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
      nlinarith
    exact hleftUpper.trans ((by norm_num : (131 : ℝ) / 150 ≤ 223 / 250).trans hrightLower)
  have halgebra :
      Real.log ((d + 2 : ℕ) : ℝ) -
          (Real.log ((d + 1 : ℕ) : ℝ) / 2 +
            (d : ℝ) * Real.log ((d + 2 : ℕ) : ℝ) /
              (2 * ((d + 1 : ℕ) : ℝ))) =
        Real.log (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) / 2 +
          (Real.log ((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) / 2 := by
    rw [← hlogeq]
    rw [show (((d + 1 : ℕ) : ℝ)) = (d : ℝ) + 1 by norm_num,
      show (((d + 2 : ℕ) : ℝ)) = (d : ℝ) + 2 by norm_num]
    field_simp
    ring
  have hnum :
      Real.log ((d + 2 : ℕ) : ℝ) + 2 * higham11_1_bunchPenaltyTwo ≤
        Real.log ((d + 1 : ℕ) : ℝ) / 2 +
          (d : ℝ) * Real.log ((d + 2 : ℕ) : ℝ) /
            (2 * ((d + 1 : ℕ) : ℝ)) +
          ((223 : ℝ) / 500) * (d : ℝ) *
            Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
    nlinarith [halgebra, hscaled]
  have hleft :
      Real.log ((d + 2 : ℕ) : ℝ) / (d : ℝ) +
          2 * higham11_1_bunchPenaltyTwo / (d : ℝ) =
        (Real.log ((d + 2 : ℕ) : ℝ) +
          2 * higham11_1_bunchPenaltyTwo) / (d : ℝ) := by ring
  have hright :
      Real.log ((d + 1 : ℕ) : ℝ) / (2 * (d : ℝ)) +
          Real.log ((d + 2 : ℕ) : ℝ) /
            (2 * ((d + 1 : ℕ) : ℝ)) +
          ((223 : ℝ) / 500) *
            Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) =
        (Real.log ((d + 1 : ℕ) : ℝ) / 2 +
          (d : ℝ) * Real.log ((d + 2 : ℕ) : ℝ) /
            (2 * ((d + 1 : ℕ) : ℝ)) +
          ((223 : ℝ) / 500) * (d : ℝ) *
            Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ))) /
          (d : ℝ) := by field_simp
  rw [hleft, hright]
  exact (div_le_div_iff_of_pos_right hdR).2 hnum

private theorem width_two_potential_step {d : ℕ} (hd : 3 ≤ d) :
    sharpLogPotential d +
        (Real.log ((d + 2 : ℕ) : ℝ) / (d : ℝ) +
          2 * higham11_1_bunchPenaltyTwo / (d : ℝ)) ≤
      sharpLogPotential (d + 2) := by
  have hraw := width_two_raw_potential_step hd
  have hs1 := wilkinsonLogSteps_succ (d := d) (by omega)
  have hs2 : wilkinsonLogSteps (d + 2) = wilkinsonLogSteps (d + 1) +
      Real.log ((d + 2 : ℕ) : ℝ) / (2 * ((d + 1 : ℕ) : ℝ)) := by
    simpa [Nat.add_assoc] using
      (wilkinsonLogSteps_succ (d := d + 1) (by omega))
  have hratio :
      Real.log (((d + 1 : ℕ) : ℝ) / ((d - 1 : ℕ) : ℝ)) =
        Real.log ((d + 1 : ℕ) : ℝ) -
          Real.log ((d - 1 : ℕ) : ℝ) := by
    rw [Real.log_div (by positivity) (ne_of_gt (by
      exact_mod_cast (by omega : 0 < d - 1)))]
  rw [hratio] at hraw
  rw [sharpLogPotential, sharpLogPotential, hs2, hs1]
  have hsub : d + 2 - 1 = d + 1 := by omega
  rw [hsub]
  linarith

private theorem log_four_ge_four_thirds :
    (4 : ℝ) / 3 ≤ Real.log 4 := by
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  rw [hlog]
  linarith [higham11_1_log_two_ge_two_thirds]

private theorem small_numeric_gap_le_potential {d : ℕ}
    (hd2 : 2 ≤ d) (hd4 : d ≤ 4) :
    ((((d : ℝ) ^ 2 - 1) / 2) * ((19 : ℝ) / 20) +
        (d : ℝ) * ((223 : ℝ) / 500)) / (d : ℝ) ≤
      sharpLogPotential d := by
  interval_cases d
  · simp only [sharpLogPotential, wilkinsonLogSteps, Finset.sum_range_succ]
    norm_num
    nlinarith [higham11_1_log_two_ge_two_thirds,
      higham11_1_log_307_div_100_ge_one]
  · simp only [sharpLogPotential, wilkinsonLogSteps, Finset.sum_range_succ]
    norm_num
    nlinarith [higham11_1_log_two_ge_two_thirds,
      higham11_1_log_three_ge_one,
      higham11_1_log_307_div_100_ge_one]
  · simp only [sharpLogPotential, wilkinsonLogSteps, Finset.sum_range_succ]
    norm_num
    nlinarith [higham11_1_log_two_ge_two_thirds,
      higham11_1_log_three_ge_one, log_four_ge_four_thirds,
      higham11_1_log_307_div_100_ge_one]

private theorem small_adjusted_gap_le_potential
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks)
    (hd2 : 2 ≤ totalWidth blocks) (hd4 : totalWidth blocks ≤ 4) :
    Real.log (lastMax blocks) - adjustedMean blocks ≤
      sharpLogPotential (totalWidth blocks) := by
  let d : ℝ := totalWidth blocks
  let R : ℝ := boundaryMoment blocks
  let gLog : ℝ := Real.log higham11_1_bunchLocalGrowthFactor
  let e : ℝ := (223 : ℝ) / 500
  have hdN : 0 < totalWidth blocks := by omega
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hdN
  have hscaled := local_adjusted_gap_scaled cert
  have hscaled' :
      d * Real.log (lastMax blocks) - adjustedLogSum blocks ≤
        R * gLog + d * e := by
    simpa [d, R, gLog, e] using hscaled
  have hmomentN := boundaryMoment_total_bound cert
  have hmoment : R ≤ (d ^ 2 - 1) / 2 := by
    have hcast : (2 : ℝ) * R ≤ d ^ 2 - 1 := by
      have hsqN : 1 ≤ totalWidth blocks ^ 2 := by
        nlinarith [hd2]
      have hcast0 : ((2 * boundaryMoment blocks : ℕ) : ℝ) ≤
          ((totalWidth blocks ^ 2 - 1 : ℕ) : ℝ) := by
        exact_mod_cast hmomentN
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hsqN,
        Nat.cast_pow, Nat.cast_one] at hcast0
      simpa [R, d] using hcast0
    linarith
  have hg_nonneg : 0 ≤ gLog := by
    dsimp [gLog]
    exact Real.log_nonneg higham11_1_bunchLocalGrowthFactor_ge_one
  have hg_upper : gLog ≤ (19 : ℝ) / 20 := by
    simpa [gLog] using higham11_1_log_bunchLocalGrowthFactor_le_19_div_20
  have hquad_nonneg : 0 ≤ (d ^ 2 - 1) / 2 := by
    have hd1 : (1 : ℝ) ≤ d := by
      dsimp [d]
      exact_mod_cast (by omega : 1 ≤ totalWidth blocks)
    nlinarith
  have hmomentlog : R * gLog ≤
      ((d ^ 2 - 1) / 2) * ((19 : ℝ) / 20) :=
    mul_le_mul hmoment hg_upper hg_nonneg hquad_nonneg
  have hgap : Real.log (lastMax blocks) - adjustedMean blocks ≤
      ((((d ^ 2 - 1) / 2) * ((19 : ℝ) / 20) + d * e) / d) := by
    have hnum : d * Real.log (lastMax blocks) - adjustedLogSum blocks ≤
        ((d ^ 2 - 1) / 2) * ((19 : ℝ) / 20) + d * e :=
      hscaled'.trans (by
        simpa only [add_comm] using (add_le_add_right hmomentlog (d * e)))
    unfold adjustedMean
    rw [show (totalWidth blocks : ℝ) = d by rfl]
    calc
      Real.log (lastMax blocks) - adjustedLogSum blocks / d =
          (d * Real.log (lastMax blocks) - adjustedLogSum blocks) / d := by
        field_simp [ne_of_gt hd]
      _ ≤ (((d ^ 2 - 1) / 2) * ((19 : ℝ) / 20) + d * e) / d :=
        div_le_div_of_nonneg_right hnum (le_of_lt hd)
  exact hgap.trans (by
    simpa [d, e] using small_numeric_gap_le_potential hd2 hd4)

/-- Bunch's sharp logarithmic potential, proved by induction over genuine
block boundaries.  Width two is handled by one atomic step and never by a
fictitious scalar midpoint. -/
private theorem adjusted_gap_le_potential
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks)
    (hd2 : 2 ≤ totalWidth blocks) :
    Real.log (lastMax blocks) - adjustedMean blocks ≤
      sharpLogPotential (totalWidth blocks) := by
  induction cert with
  | singleton b hadamard =>
      apply small_adjusted_gap_le_potential
        (Higham11BunchSharpBlockCertificate.singleton b hadamard) hd2
      simp only [totalWidth, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      exact b.width_le_two.trans (by omega)
  | cons b next rest tail local_growth hadamard ih =>
      let whole := Higham11BunchSharpBlockCertificate.cons b next rest tail
        local_growth hadamard
      by_cases hsmall : totalWidth (b :: next :: rest) ≤ 4
      · exact small_adjusted_gap_le_potential whole hd2 hsmall
      · have hD5 : 5 ≤ totalWidth (b :: next :: rest) := by omega
        have hd3 : 3 ≤ totalWidth (next :: rest) := by
          have hw := b.width_le_two
          have hwidth : totalWidth (b :: next :: rest) =
              b.width + totalWidth (next :: rest) := by
            simp [totalWidth]
          rw [hwidth] at hD5
          omega
        have ih' := ih (by omega : 2 ≤ totalWidth (next :: rest))
        have hmean := adjustedMean_cons_step b next rest tail local_growth hadamard
        have hgap :
            Real.log (lastMax (b :: next :: rest)) -
                adjustedMean (b :: next :: rest) ≤
              sharpLogPotential (totalWidth (next :: rest)) +
                ((b.width : ℝ) *
                    Real.log ((b.width + totalWidth (next :: rest) : ℕ) : ℝ) /
                      (2 * (totalWidth (next :: rest) : ℝ)) +
                  (b.width : ℝ) * b.penalty /
                    (totalWidth (next :: rest) : ℝ)) := by
          calc
            Real.log (lastMax (b :: next :: rest)) -
                adjustedMean (b :: next :: rest) =
              (Real.log (lastMax (next :: rest)) -
                  adjustedMean (next :: rest)) +
                (adjustedMean (next :: rest) -
                  adjustedMean (b :: next :: rest)) := by
                simp only [lastMax]
                ring
            _ ≤ sharpLogPotential (totalWidth (next :: rest)) +
                ((b.width : ℝ) *
                    Real.log ((b.width + totalWidth (next :: rest) : ℕ) : ℝ) /
                      (2 * (totalWidth (next :: rest) : ℝ)) +
                  (b.width : ℝ) * b.penalty /
                    (totalWidth (next :: rest) : ℝ)) :=
              add_le_add ih' hmean
        rcases b.width_one_or_two with hw | hw
        · have hstep := width_one_potential_step
            (d := totalWidth (next :: rest)) (by omega)
          have hgap' :
              Real.log (lastMax (b :: next :: rest)) -
                  adjustedMean (b :: next :: rest) ≤
                sharpLogPotential (totalWidth (next :: rest)) +
                  (Real.log ((totalWidth (next :: rest) + 1 : ℕ) : ℝ) /
                      (2 * (totalWidth (next :: rest) : ℝ)) +
                    higham11_1_bunchPenaltyOne /
                      (totalWidth (next :: rest) : ℝ)) := by
            simpa [hw, Higham11BunchSharpBlock.penalty, add_comm] using hgap
          have hout := hgap'.trans hstep
          simpa [totalWidth, hw, add_comm] using hout
        · have hstep := width_two_potential_step
            (d := totalWidth (next :: rest)) hd3
          have hden : (0 : ℝ) < totalWidth (next :: rest) := by positivity
          have heq :
              (2 : ℝ) *
                    Real.log ((2 + totalWidth (next :: rest) : ℕ) : ℝ) /
                      (2 * (totalWidth (next :: rest) : ℝ)) +
                  2 * higham11_1_bunchPenaltyTwo /
                    (totalWidth (next :: rest) : ℝ) =
                Real.log ((totalWidth (next :: rest) + 2 : ℕ) : ℝ) /
                    (totalWidth (next :: rest) : ℝ) +
                  2 * higham11_1_bunchPenaltyTwo /
                    (totalWidth (next :: rest) : ℝ) := by
            rw [add_comm 2 (totalWidth (next :: rest))]
            field_simp
          have hgap' :
              Real.log (lastMax (b :: next :: rest)) -
                  adjustedMean (b :: next :: rest) ≤
                sharpLogPotential (totalWidth (next :: rest)) +
                  (Real.log ((totalWidth (next :: rest) + 2 : ℕ) : ℝ) /
                      (totalWidth (next :: rest) : ℝ) +
                    2 * higham11_1_bunchPenaltyTwo /
                      (totalWidth (next :: rest) : ℝ)) := by
            have htmp := hgap
            simp only [hw, Nat.cast_ofNat,
              Higham11BunchSharpBlock.penalty,
              if_neg (by norm_num : (2 : ℕ) ≠ 1)] at htmp
            rw [heq] at htmp
            exact htmp
          have hout := hgap'.trans hstep
          simpa [totalWidth, hw, add_comm] using hout

private theorem log_wilkinson_bound_eq_steps {n : ℕ} (hn : 1 ≤ n) :
    Real.log (higham9_14_completePivotWilkinsonBound n) =
      Real.log (n : ℝ) / 2 + wilkinsonLogSteps n := by
  have hprod_pos : 0 < higham9_14_completePivotWilkinsonProduct n :=
    higham9_14_completePivotWilkinsonProduct_pos n
  have hprodlog : Real.log (higham9_14_completePivotWilkinsonProduct n) =
      ∑ j ∈ Finset.range (n - 1),
        Real.log ((j : ℝ) + 2) / ((j : ℝ) + 1) := by
    rw [higham9_14_completePivotWilkinsonProduct,
      Real.log_prod (fun k hk => by
        have := (Finset.mem_Icc.mp hk).1
        positivity),
      ← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
      Finset.sum_Ico_eq_sum_range, show n + 1 - 2 = n - 1 from by omega]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.log_rpow (by positivity)]
    push_cast
    rw [show (2 : ℝ) + (j : ℝ) - 1 = (j : ℝ) + 1 from by ring]
    ring
  rw [higham9_14_completePivotWilkinsonBound,
    Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn)))
      (ne_of_gt (Real.sqrt_pos.mpr hprod_pos)),
    Real.log_sqrt (by positivity), Real.log_sqrt (le_of_lt hprod_pos),
    hprodlog, Finset.sum_div]
  unfold wilkinsonLogSteps
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  rw [div_div, mul_comm ((j : ℝ) + 1) 2]

private theorem sharp_potential_add_half_log_eq_log_bound {n : ℕ}
    (hn : 2 ≤ n) :
    sharpLogPotential n + Real.log (n : ℝ) / 2 =
      Real.log (higham11_1_bunchSharpGrowthBound n) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hmR : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  have hW : 0 < higham9_14_completePivotWilkinsonBound n :=
    higham9_14_completePivotWilkinsonBound_pos (by omega)
  have hC : (0 : ℝ) < (307 : ℝ) / 100 := by norm_num
  have hrpow : 0 < Real.rpow ((n - 1 : ℕ) : ℝ) ((223 : ℝ) / 500) :=
    Real.rpow_pos_of_pos hmR _
  have hlogW := log_wilkinson_bound_eq_steps (n := n) (by omega)
  have hlogRpow :
      Real.log (Real.rpow ((n - 1 : ℕ) : ℝ) ((223 : ℝ) / 500)) =
        ((223 : ℝ) / 500) * Real.log ((n - 1 : ℕ) : ℝ) := by
    exact Real.log_rpow hmR _
  unfold higham11_1_bunchSharpGrowthBound
  unfold higham11_1_bunchSharpGrowthMultiplier
  rw [Real.log_mul (ne_of_gt (mul_pos hC hrpow)) (ne_of_gt hW),
    Real.log_mul (ne_of_gt hC) (ne_of_gt hrpow),
    hlogRpow]
  rw [hlogW]
  unfold sharpLogPotential
  ring

private theorem adjustedMean_sub_log_first_le_half_log
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks) :
    adjustedMean blocks - Real.log (firstMax blocks) ≤
      Real.log (totalWidth blocks : ℝ) / 2 := by
  have hdN := totalWidth_pos cert
  have hd : (0 : ℝ) < totalWidth blocks := by exact_mod_cast hdN
  have h := adjustedLogSum_le_boundary cert
  unfold adjustedMean
  rw [sub_le_iff_le_add]
  rw [div_le_iff₀ hd]
  nlinarith

/-- **Higham section 11.1.1 (Bunch [175, 1971]), faithful sharp comparison.**

For an order-`n` genuine block-boundary determinant schedule, every selected
later boundary maximum is at most
`3.07 * (n-1)^0.446` times the Chapter 9 (9.14) complete-pivoting bound,
relative to the original maximum.  The explicit `2 ≤ n` guard is necessary:
the printed multiplier vanishes at order one. -/
theorem higham11_1_bunchSharpGrowth_ratio_bound
    {n : ℕ} (hn : 2 ≤ n)
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks)
    (hwidth : totalWidth blocks = n) :
    lastMax blocks / firstMax blocks ≤
      higham11_1_bunchSharpGrowthBound n := by
  have hd2 : 2 ≤ totalWidth blocks := by omega
  have hgap := adjusted_gap_le_potential cert hd2
  have hfirst := adjustedMean_sub_log_first_le_half_log cert
  have hlog : Real.log (lastMax blocks) - Real.log (firstMax blocks) ≤
      sharpLogPotential (totalWidth blocks) +
        Real.log (totalWidth blocks : ℝ) / 2 := by
    linarith
  have hpotential := sharp_potential_add_half_log_eq_log_bound hn
  rw [hwidth] at hlog
  rw [hpotential] at hlog
  have hlastPos := lastMax_pos cert
  have hfirstPos := firstMax_pos cert
  have hboundPos : 0 < higham11_1_bunchSharpGrowthBound n := by
    unfold higham11_1_bunchSharpGrowthBound
    unfold higham11_1_bunchSharpGrowthMultiplier
    have hm : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < n - 1)
    exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hm _))
      (higham9_14_completePivotWilkinsonBound_pos (by omega))
  have hlogratio : Real.log (lastMax blocks / firstMax blocks) ≤
      Real.log (higham11_1_bunchSharpGrowthBound n) := by
    rw [Real.log_div (ne_of_gt hlastPos) (ne_of_gt hfirstPos)]
    exact hlog
  have hexp := Real.exp_le_exp.mpr hlogratio
  rwa [Real.exp_log (div_pos hlastPos hfirstPos),
    Real.exp_log hboundPos] at hexp

/-- Product-form adapter for the faithful block-boundary comparison. -/
theorem higham11_1_bunchSharpGrowth_stageMax_le_bound_mul
    {n : ℕ} (hn : 2 ≤ n)
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks)
    (hwidth : totalWidth blocks = n) :
    lastMax blocks ≤
      higham11_1_bunchSharpGrowthBound n * firstMax blocks := by
  have hratio := higham11_1_bunchSharpGrowth_ratio_bound hn cert hwidth
  exact (div_le_iff₀ (firstMax_pos cert)).mp hratio

/-- **Order-one source discrepancy.**  Read literally at `n = 1`, the
printed right-hand side is zero although the original/only stage has growth
ratio one.  Thus the sharp comparison is faithfully stated only for `2 ≤ n`. -/
theorem higham11_1_bunchSharpGrowth_n_one_source_discrepancy :
    higham11_1_bunchSharpGrowthBound 1 = 0 ∧
      ¬ ((1 : ℝ) / 1 ≤ higham11_1_bunchSharpGrowthBound 1) := by
  have hzero : higham11_1_bunchSharpGrowthBound 1 = 0 := by
    unfold higham11_1_bunchSharpGrowthBound
    unfold higham11_1_bunchSharpGrowthMultiplier
    norm_num
  rw [hzero]
  norm_num

end Higham11BunchSharpBlockCertificate

open Higham11BunchSharpBlockCertificate

/-- Root-namespace public alias for the faithful block-boundary sharp
comparison. -/
theorem higham11_1_bunchSharpGrowth_ratio_bound
    {n : ℕ} (hn : 2 ≤ n)
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks)
    (hwidth : totalWidth blocks = n) :
    lastMax blocks / firstMax blocks ≤
      higham11_1_bunchSharpGrowthBound n :=
  Higham11BunchSharpBlockCertificate.higham11_1_bunchSharpGrowth_ratio_bound
    hn cert hwidth

/-- Root-namespace public product-form alias. -/
theorem higham11_1_bunchSharpGrowth_stageMax_le_bound_mul
    {n : ℕ} (hn : 2 ≤ n)
    {blocks : List Higham11BunchSharpBlock}
    (cert : Higham11BunchSharpBlockCertificate blocks)
    (hwidth : totalWidth blocks = n) :
    lastMax blocks ≤
      higham11_1_bunchSharpGrowthBound n * firstMax blocks :=
  Higham11BunchSharpBlockCertificate.higham11_1_bunchSharpGrowth_stageMax_le_bound_mul
    hn cert hwidth

/-- Root-namespace public order-one source-discrepancy alias. -/
theorem higham11_1_bunchSharpGrowth_n_one_source_discrepancy :
    higham11_1_bunchSharpGrowthBound 1 = 0 ∧
      ¬ ((1 : ℝ) / 1 ≤ higham11_1_bunchSharpGrowthBound 1) :=
  Higham11BunchSharpBlockCertificate.higham11_1_bunchSharpGrowth_n_one_source_discrepancy

end NumStability
