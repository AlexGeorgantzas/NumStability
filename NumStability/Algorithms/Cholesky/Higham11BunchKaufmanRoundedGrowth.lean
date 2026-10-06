/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Product growth for the literal rounded Bunch--Kaufman execution

Higham [608, 1997, sec. 4.3] proves the constant `36` first for the exact
stage factors.  Replacing those factors by computed factors incurs a finite
precision correction.  This file keeps that distinction explicit and derives
the stage scale used by the literal rounded executor from its actual active
matrices; no target-shaped product-growth hypothesis is built into the scale.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGlobal

open scoped BigOperators

namespace NumStability

open Ch11Closure.Mixed

/-- Maximum magnitude of an entry of a finite active matrix.  The empty
matrix has maximum zero. -/
noncomputable def higham11_4_roundedActiveMax : {n : Nat} ->
    Higham11RoundedBunchKaufmanMatrix n -> Real
  | 0, _ => 0
  | n + 1, A =>
      maxEntryNorm (by omega : 0 < n + 1)
        (Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)

theorem higham11_4_roundedActiveMax_nonneg {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix n) :
    0 <= higham11_4_roundedActiveMax A := by
  cases n with
  | zero => simp [higham11_4_roundedActiveMax]
  | succ n =>
      exact maxEntryNorm_nonneg (by omega)
        (Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)

theorem higham11_4_entry_le_roundedActiveMax {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix n) (i j : Fin n) :
    |A i j| <= higham11_4_roundedActiveMax A := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      simpa [higham11_4_roundedActiveMax] using
        (entry_le_maxEntryNorm (by omega : 0 < n + 1)
          (Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real) i j)

theorem higham11_4_omegaOne_le_roundedActiveMax {n : Nat} (hn : 0 < n)
    (A : Higham11RoundedBunchKaufmanMatrix n) :
    higham11_2_bunchKaufmanOmegaOne hn A <=
      higham11_4_roundedActiveMax A := by
  unfold higham11_2_bunchKaufmanOmegaOne higham11_5_rookColumnMax
  split_ifs
  · simpa using higham11_4_roundedActiveMax_nonneg A
  · exact higham11_4_entry_le_roundedActiveMax A _ _

theorem higham11_4_omegaRow_le_roundedActiveMax {n : Nat} (hn : 0 < n)
    (A : Higham11RoundedBunchKaufmanMatrix n) :
    higham11_2_bunchKaufmanOmegaRow hn A <=
      higham11_4_roundedActiveMax A := by
  unfold higham11_2_bunchKaufmanOmegaRow higham11_5_rookColumnMax
  split_ifs
  · simpa using higham11_4_roundedActiveMax_nonneg A
  · exact higham11_4_entry_le_roundedActiveMax A _ _

theorem higham11_4_omegaRow_nonneg {n : Nat} (hn : 0 < n)
    (A : Higham11RoundedBunchKaufmanMatrix n) :
    0 <= higham11_2_bunchKaufmanOmegaRow hn A := by
  unfold higham11_2_bunchKaufmanOmegaRow higham11_5_rookColumnMax
  exact abs_nonneg _

theorem higham11_4_omegaOne_le_omegaRow {n : Nat} (hn : 0 < n)
    (A : Higham11RoundedBunchKaufmanMatrix n)
    (hA : IsSymmetricFiniteMatrix A) :
    higham11_2_bunchKaufmanOmegaOne hn A <=
      higham11_2_bunchKaufmanOmegaRow hn A := by
  let i₀ := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  by_cases hri : r = i₀
  · simpa [higham11_2_bunchKaufmanOmegaOne,
      higham11_2_bunchKaufmanOmegaRow, i₀, r, hri]
  · have hattain :=
      higham11_2_bunchKaufmanMaxRow_attains_omegaOne_if hn A
    have hspec := higham11_5_rookColumnMax_spec A r i₀
    rw [if_neg (Ne.symm hri), hA i₀ r] at hspec
    have hattain' : |A r i₀| =
        higham11_2_bunchKaufmanOmegaOne hn A := by
      simpa [i₀, r, hri] using hattain
    calc
      higham11_2_bunchKaufmanOmegaOne hn A = |A r i₀| := hattain'.symm
      _ ≤ higham11_5_rookColumnMax A r := hspec
      _ = higham11_2_bunchKaufmanOmegaRow hn A := by
        rfl

/-- Two rounded scalar divisions inflate the exact scalar pivot path by at
most four when `u <= 1`. -/
theorem higham11_4_fl_div_pair_pivot_abs_le_four
    (fp : FPModel) {c₁ c₂ e : Real} (he : e ≠ 0) (hu : fp.u <= 1) :
    |fp.fl_div c₁ e| * |e| * |fp.fl_div c₂ e| <=
      4 * |c₁ * c₂ / e| := by
  obtain ⟨δ₁, hδ₁, hfl₁⟩ := fp.model_div c₁ e he
  obtain ⟨δ₂, hδ₂, hfl₂⟩ := fp.model_div c₂ e he
  have hfac₁ : |1 + δ₁| <= 2 := by
    calc
      |1 + δ₁| <= |(1 : Real)| + |δ₁| := abs_add_le _ _
      _ <= 1 + fp.u := by simpa using add_le_add_left hδ₁ 1
      _ <= 2 := by linarith
  have hfac₂ : |1 + δ₂| <= 2 := by
    calc
      |1 + δ₂| <= |(1 : Real)| + |δ₂| := abs_add_le _ _
      _ <= 1 + fp.u := by simpa using add_le_add_left hδ₂ 1
      _ <= 2 := by linarith
  rw [hfl₁, hfl₂]
  have hrewrite :
      |c₁ / e * (1 + δ₁)| * |e| * |c₂ / e * (1 + δ₂)| =
        |c₁ * c₂ / e| * |1 + δ₁| * |1 + δ₂| := by
    rw [abs_mul, abs_mul, abs_div, abs_div, abs_div, abs_mul]
    have heabs : |e| ≠ 0 := abs_ne_zero.mpr he
    field_simp [heabs]
  rw [hrewrite]
  have hcorr0 : 0 <= |c₁ * c₂ / e| := abs_nonneg _
  calc
    |c₁ * c₂ / e| * |1 + δ₁| * |1 + δ₂|
        <= |c₁ * c₂ / e| * 2 * 2 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hfac₁ hcorr0) hfac₂
            (abs_nonneg _) (mul_nonneg hcorr0 (by norm_num))
    _ = 4 * |c₁ * c₂ / e| := by ring

theorem higham11_4_pivotPathOneAbs_le_eight_of_correction
    (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin (n + 1)) (hu : fp.u <= 1)
    (hpivot : higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0)
    {M : Real}
    (hcorr :
      |higham11_2_bunchKaufmanRoundedActive A i.succ 0 *
          higham11_2_bunchKaufmanRoundedActive A j.succ 0 /
          higham11_2_bunchKaufmanRoundedActive A 0 0| <= 2 * M) :
    higham11_2_bunchKaufmanPivotPathOneAbs fp A i j <= 8 * M := by
  let B := higham11_2_bunchKaufmanRoundedActive A
  have hamp := higham11_4_fl_div_pair_pivot_abs_le_four fp
    (c₁ := B i.succ 0) (c₂ := B j.succ 0) (e := B 0 0) hpivot hu
  change |fp.fl_div (B i.succ 0) (B 0 0)| * |B 0 0| *
      |fp.fl_div (B j.succ 0) (B 0 0)| <= 8 * M
  exact hamp.trans (by nlinarith)

private theorem higham11_4_two_mul_currentMax_of_omega_div_alpha
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix n)
    {ω : Real} (hω0 : 0 <= ω)
    (hω : ω <= higham11_4_roundedActiveMax A) :
    ω / higham11_1_bunchParlettAlpha <=
      2 * higham11_4_roundedActiveMax A := by
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hM0 := higham11_4_roundedActiveMax_nonneg A
  calc
    ω / higham11_1_bunchParlettAlpha =
        (1 / higham11_1_bunchParlettAlpha) * ω := by ring
    _ <= 2 * higham11_4_roundedActiveMax A :=
      mul_le_mul (le_of_lt higham11_4_recip_alpha_lt_two) hω
        hω0 (by positivity)

theorem higham11_4_active_offdiag_le_omegaOne_case1_or_case2
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hbranch :
      higham11_2_bunchKaufmanFirstBranch (by omega)
          higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case1 ∨
        higham11_2_bunchKaufmanFirstBranch (by omega)
          higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case2)
    (i : Fin (n + 1)) :
    |higham11_2_bunchKaufmanRoundedActive A i.succ 0| <=
      higham11_2_bunchKaufmanOmegaOne (by omega) A := by
  rw [higham11_2_bunchKaufmanRoundedActive,
    higham11_2_bunchKaufmanExactActive_eq_of_case1_or_case2 A hbranch]
  have h := higham11_2_bunchKaufmanOmegaOne_spec (by omega) A i.succ
  simpa [higham11_2_firstIndex] using h

theorem higham11_4_active_offdiag_le_omegaRow_case3
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case3)
    (i : Fin (n + 1)) :
    |higham11_2_bunchKaufmanRoundedActive A i.succ 0| <=
      higham11_2_bunchKaufmanOmegaRow (by omega) A := by
  let p := higham11_2_bunchKaufmanFirstPerm (by omega)
    higham11_1_bunchParlettAlpha A
  let r := higham11_2_bunchKaufmanMaxRow (by omega) A
  have hp0 : p (0 : Fin (n + 2)) = r := by
    simp [p, r, higham11_2_bunchKaufmanFirstPerm, hbranch,
      higham11_2_firstIndex]
  have hpi : p i.succ ≠ r := by
    intro h
    have heq : p i.succ = p 0 := h.trans hp0.symm
    have := p.injective heq
    exact Fin.succ_ne_zero i this
  have h := higham11_5_rookColumnMax_spec A r (p i.succ)
  rw [if_neg hpi] at h
  change |A (p i.succ) (p 0)| <=
    higham11_2_bunchKaufmanOmegaRow (by omega) A
  rw [hp0]
  simpa [r, higham11_2_bunchKaufmanOmegaRow] using h

theorem higham11_4_pivotPathOneAbs_le_eight_case1
    (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case1)
    (i j : Fin (n + 1)) (hu : fp.u <= 1) :
    higham11_2_bunchKaufmanPivotPathOneAbs fp A i j <=
      8 * higham11_4_roundedActiveMax A := by
  let ω₁ := higham11_2_bunchKaufmanOmegaOne (by omega) A
  let ωr := higham11_2_bunchKaufmanOmegaRow (by omega) A
  let i₀ := higham11_2_firstIndex (by omega : 0 < n + 2)
  let r := higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega : 0 < n + 2) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hω₁0 : 0 <= ω₁ := higham11_2_bunchKaufmanOmegaOne_nonneg _ _
  have hω₁ : 0 < ω₁ := lt_of_le_of_ne hω₁0 (Ne.symm hcase.1)
  have hci := higham11_4_active_offdiag_le_omegaOne_case1_or_case2
    A (Or.inl hbranch) i
  have hcj := higham11_4_active_offdiag_le_omegaOne_case1_or_case2
    A (Or.inl hbranch) j
  have hcorr := higham11_4_bunch_kaufman_case1_schur_correction_bound
    higham11_1_bunchParlettAlpha (A i₀ i₀) (A r r) ω₁ ωr
    (higham11_2_bunchKaufmanRoundedActive A i.succ 0)
    (higham11_2_bunchKaufmanRoundedActive A j.succ 0)
    (by simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
    hω₁ hcase hci hcj
  have hωM := higham11_4_omegaOne_le_roundedActiveMax
    (by omega : 0 < n + 2) A
  have hcorrM := hcorr.trans
    (higham11_4_two_mul_currentMax_of_omega_div_alpha A hω₁0 hωM)
  apply higham11_4_pivotPathOneAbs_le_eight_of_correction fp A i j hu
    (Higham11RoundedBunchKaufmanExecution.roundedActive_pivot_ne_zero_case1
      A hbranch)
  simpa [i₀, higham11_2_firstIndex,
    higham11_2_bunchKaufmanRoundedActive,
    higham11_2_bunchKaufmanExactActive_eq_of_case1_or_case2 A (Or.inl hbranch)]
    using hcorrM

theorem higham11_4_pivotPathOneAbs_le_eight_case2
    (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case2)
    (i j : Fin (n + 1)) (hu : fp.u <= 1) :
    higham11_2_bunchKaufmanPivotPathOneAbs fp A i j <=
      8 * higham11_4_roundedActiveMax A := by
  let ω₁ := higham11_2_bunchKaufmanOmegaOne (by omega) A
  let ωr := higham11_2_bunchKaufmanOmegaRow (by omega) A
  let i₀ := higham11_2_firstIndex (by omega : 0 < n + 2)
  let r := higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega : 0 < n + 2) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hω₁0 : 0 <= ω₁ := higham11_2_bunchKaufmanOmegaOne_nonneg _ _
  have hω₁ : 0 < ω₁ := lt_of_le_of_ne hω₁0 (Ne.symm hcase.1)
  have hci := higham11_4_active_offdiag_le_omegaOne_case1_or_case2
    A (Or.inr hbranch) i
  have hcj := higham11_4_active_offdiag_le_omegaOne_case1_or_case2
    A (Or.inr hbranch) j
  have hcorr := higham11_4_bunch_kaufman_case2_schur_correction_bound
    higham11_1_bunchParlettAlpha (A i₀ i₀) (A r r) ω₁ ωr
    (higham11_2_bunchKaufmanRoundedActive A i.succ 0)
    (higham11_2_bunchKaufmanRoundedActive A j.succ 0)
    (by simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
    hω₁ hcase hci hcj
  have hωr0 : 0 <= ωr := higham11_4_omegaRow_nonneg _ _
  have hωM := higham11_4_omegaRow_le_roundedActiveMax
    (by omega : 0 < n + 2) A
  have hcorrM := hcorr.trans
    (higham11_4_two_mul_currentMax_of_omega_div_alpha A hωr0 hωM)
  apply higham11_4_pivotPathOneAbs_le_eight_of_correction fp A i j hu
    (Higham11RoundedBunchKaufmanExecution.roundedActive_pivot_ne_zero_case2
      A hbranch)
  simpa [i₀, higham11_2_firstIndex,
    higham11_2_bunchKaufmanRoundedActive,
    higham11_2_bunchKaufmanExactActive_eq_of_case1_or_case2 A (Or.inr hbranch)]
    using hcorrM

theorem higham11_4_pivotPathOneAbs_le_eight_case3
    (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case3)
    (i j : Fin (n + 1)) (hu : fp.u <= 1) :
    higham11_2_bunchKaufmanPivotPathOneAbs fp A i j <=
      8 * higham11_4_roundedActiveMax A := by
  let ω₁ := higham11_2_bunchKaufmanOmegaOne (by omega) A
  let ωr := higham11_2_bunchKaufmanOmegaRow (by omega) A
  let i₀ := higham11_2_firstIndex (by omega : 0 < n + 2)
  let r := higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega : 0 < n + 2) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hωr := higham11_2_bunchKaufmanOmegaRow_pos_of_branch
    (by omega : 0 < n + 2) A hA (by simp) hbranch
  have hci := higham11_4_active_offdiag_le_omegaRow_case3 A hbranch i
  have hcj := higham11_4_active_offdiag_le_omegaRow_case3 A hbranch j
  have hcorr := higham11_4_bunch_kaufman_case3_schur_correction_bound
    higham11_1_bunchParlettAlpha (A i₀ i₀) (A r r) ω₁ ωr
    (higham11_2_bunchKaufmanRoundedActive A i.succ 0)
    (higham11_2_bunchKaufmanRoundedActive A j.succ 0)
    (by simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
    hωr hcase hci hcj
  have hωM := higham11_4_omegaRow_le_roundedActiveMax
    (by omega : 0 < n + 2) A
  have hcorrM := hcorr.trans
    (higham11_4_two_mul_currentMax_of_omega_div_alpha A
      (le_of_lt hωr) hωM)
  apply higham11_4_pivotPathOneAbs_le_eight_of_correction fp A i j hu
    (Higham11RoundedBunchKaufmanExecution.roundedActive_pivot_ne_zero_case3
      A hA hbranch)
  simpa [higham11_2_bunchKaufmanRoundedActive,
    higham11_2_bunchKaufmanExactActive_case3_pivot A hbranch]
    using hcorrM

private theorem higham11_4_bunchAlpha_le_two_thirds :
    higham11_1_bunchParlettAlpha <= (2 : Real) / 3 := by
  have hαsq : higham11_1_bunchParlettAlpha ^ 2 =
      (higham11_1_bunchParlettAlpha + 1) / 4 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_sq
  have hαle : higham11_1_bunchParlettAlpha <= (5 : Real) / 7 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_le_5_7
  have hα0 : 0 <= higham11_1_bunchParlettAlpha := by
    exact le_of_lt (by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  nlinarith

private theorem higham11_4_relative_product_perturbation
    {a b da db ε : Real} (hε : 0 <= ε)
    (hda : |da| <= ε * |a|) (hdb : |db| <= ε * |b|) :
    |(a + da) * (b + db) - a * b| <=
      (2 * ε + ε ^ 2) * (|a| * |b|) := by
  have ha0 : 0 <= |a| := abs_nonneg _
  have hb0 : 0 <= |b| := abs_nonneg _
  have hda0 : 0 <= |da| := abs_nonneg _
  have hdb0 : 0 <= |db| := abs_nonneg _
  have h1 : |a * db| <= ε * (|a| * |b|) := by
    rw [abs_mul]
    calc
      |a| * |db| <= |a| * (ε * |b|) :=
        mul_le_mul_of_nonneg_left hdb ha0
      _ = ε * (|a| * |b|) := by ring
  have h2 : |da * b| <= ε * (|a| * |b|) := by
    rw [abs_mul]
    calc
      |da| * |b| <= (ε * |a|) * |b| :=
        mul_le_mul_of_nonneg_right hda hb0
      _ = ε * (|a| * |b|) := by ring
  have h3 : |da * db| <= ε ^ 2 * (|a| * |b|) := by
    rw [abs_mul]
    calc
      |da| * |db| <= (ε * |a|) * (ε * |b|) :=
        mul_le_mul hda hdb hdb0 (mul_nonneg hε ha0)
      _ = ε ^ 2 * (|a| * |b|) := by ring
  calc
    |(a + da) * (b + db) - a * b| =
        |a * db + (da * b + da * db)| := by
          congr 1
          ring
    _ <= |a * db| + |da * b + da * db| := abs_add_le _ _
    _ <= |a * db| + (|da * b| + |da * db|) :=
      add_le_add (le_refl _) (abs_add_le _ _)
    _ <= ε * (|a| * |b|) +
        (ε * (|a| * |b|) + ε ^ 2 * (|a| * |b|)) :=
      add_le_add h1 (add_le_add h2 h3)
    _ = (2 * ε + ε ^ 2) * (|a| * |b|) := by ring

/-!
The next lemma is the finite-u replacement for Higham [608, 1997, A.3] at
one accepted case-(4) block.  The exact determinant gap is reduced by the
actual equation-(11.5) perturbation.  At `ε <= 10^-3` the gap still leaves a
strict numerical margin: both computed multiplier components have constant
`31/10`, which later gives a local absolute pivot-path constant below `33`,
not merely below `36`.
-/
set_option maxHeartbeats 1000000 in
private theorem higham11_4_perturbed_case4_solve_component_bounds
    (a11 a1r arr ω₁ ωr c₀ c₁ w₀ w₁
      d00 d01 d10 d11 ε : Real)
    (hε0 : 0 <= ε) (hε : ε <= (1 : Real) / 1000)
    (hω₁ : 0 < ω₁) (hωr : 0 < ωr)
    (ha1r : |a1r| = ω₁)
    (hdet : (1 - higham11_1_bunchParlettAlpha ^ 2) * ω₁ ^ 2 <=
      |a11 * arr - a1r ^ 2|)
    (ha11prod : |a11| * ωr <=
      higham11_1_bunchParlettAlpha * ω₁ ^ 2)
    (harr : |arr| <= higham11_1_bunchParlettAlpha * ωr)
    (hc₀ : |c₀| <= ω₁) (hc₁ : |c₁| <= ωr)
    (hd00 : |d00| <= ε * |a11|)
    (hd01 : |d01| <= ε * |a1r|)
    (hd10 : |d10| <= ε * |a1r|)
    (hd11 : |d11| <= ε * |arr|)
    (heq0 : (a11 + d00) * w₀ + (a1r + d01) * w₁ = c₀)
    (heq1 : (a1r + d10) * w₀ + (arr + d11) * w₁ = c₁) :
    ω₁ * |w₀| <= (31 : Real) / 10 * ωr ∧
      |w₁| <= (31 : Real) / 10 := by
  let α := higham11_1_bunchParlettAlpha
  let f00 := a11 + d00
  let f01 := a1r + d01
  let f10 := a1r + d10
  let f11 := arr + d11
  let det0 := a11 * arr - a1r ^ 2
  let detf := f00 * f11 - f01 * f10
  have hα0 : 0 <= α := by
    exact le_of_lt (by
      simpa [α, higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  have hαle : α <= (2 : Real) / 3 := by
    simpa [α] using higham11_4_bunchAlpha_le_two_thirds
  have hαsq : α ^ 2 <= (4 : Real) / 9 := by nlinarith
  have hdiagprod : |a11| * |arr| <= α ^ 2 * ω₁ ^ 2 := by
    calc
      |a11| * |arr| <= |a11| * (α * ωr) :=
        mul_le_mul_of_nonneg_left harr (abs_nonneg _)
      _ = α * (|a11| * ωr) := by ring
      _ <= α * (α * ω₁ ^ 2) :=
        mul_le_mul_of_nonneg_left ha11prod hα0
      _ = α ^ 2 * ω₁ ^ 2 := by ring
  have hdiagdiff := higham11_4_relative_product_perturbation
    hε0 hd00 hd11
  have hoffdiff := higham11_4_relative_product_perturbation
    hε0 hd01 hd10
  have ht0 : 0 <= 2 * ε + ε ^ 2 := by positivity
  have hdiff : |detf - det0| <=
      (2 * ε + ε ^ 2) * ((1 + α ^ 2) * ω₁ ^ 2) := by
    have hdiagdiff' :
        |f00 * f11 - a11 * arr| <=
          (2 * ε + ε ^ 2) * (α ^ 2 * ω₁ ^ 2) := by
      exact hdiagdiff.trans
        (mul_le_mul_of_nonneg_left hdiagprod ht0)
    have hoffdiff' :
        |f01 * f10 - a1r ^ 2| <=
          (2 * ε + ε ^ 2) * ω₁ ^ 2 := by
      have habs : |a1r| * |a1r| = ω₁ ^ 2 := by rw [ha1r]; ring
      simpa [f01, f10, habs, pow_two] using hoffdiff
    have htri : |detf - det0| <=
        |f00 * f11 - a11 * arr| + |f01 * f10 - a1r ^ 2| := by
      have h := abs_sub (f00 * f11 - a11 * arr)
        (f01 * f10 - a1r ^ 2)
      convert h using 1 <;> simp [detf, det0] <;> ring
    calc
      |detf - det0| <=
          |f00 * f11 - a11 * arr| + |f01 * f10 - a1r ^ 2| := htri
      _ <= (2 * ε + ε ^ 2) * (α ^ 2 * ω₁ ^ 2) +
          (2 * ε + ε ^ 2) * ω₁ ^ 2 :=
        add_le_add hdiagdiff' hoffdiff'
      _ = (2 * ε + ε ^ 2) * ((1 + α ^ 2) * ω₁ ^ 2) := by ring
  have hεsq : ε ^ 2 <= ε / 1000 := by nlinarith
  have ht : 2 * ε + ε ^ 2 <= (3 : Real) / 1000 := by nlinarith
  have hαfac : 1 + α ^ 2 <= (3 : Real) / 2 := by nlinarith
  have hcoeff : (2 * ε + ε ^ 2) * (1 + α ^ 2) <=
      (9 : Real) / 2000 := by
    calc
      (2 * ε + ε ^ 2) * (1 + α ^ 2) <=
          ((3 : Real) / 1000) * ((3 : Real) / 2) :=
        mul_le_mul ht hαfac (by positivity) (by positivity)
      _ = (9 : Real) / 2000 := by norm_num
  have hdiff' : |detf - det0| <= (9 : Real) / 2000 * ω₁ ^ 2 := by
    calc
      |detf - det0| <=
          ((2 * ε + ε ^ 2) * (1 + α ^ 2)) * ω₁ ^ 2 := by
        simpa [mul_assoc] using hdiff
      _ <= ((9 : Real) / 2000) * ω₁ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
  have hdetf : (11 : Real) / 20 * ω₁ ^ 2 <= |detf| := by
    have htri : |det0| <= |detf| + |detf - det0| := by
      calc
        |det0| = |detf - (detf - det0)| := by congr 1 <;> ring
        _ <= |detf| + |detf - det0| := abs_sub _ _
    have hdet0 : (1 - α ^ 2) * ω₁ ^ 2 <= |det0| := by
      simpa [α, det0] using hdet
    have hlower : (5 : Real) / 9 * ω₁ ^ 2 <= |det0| := by
      calc
        (5 : Real) / 9 * ω₁ ^ 2 <= (1 - α ^ 2) * ω₁ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        _ <= |det0| := hdet0
    have hnumeric : (11 : Real) / 20 * ω₁ ^ 2 +
        (9 : Real) / 2000 * ω₁ ^ 2 <= (5 : Real) / 9 * ω₁ ^ 2 := by
      nlinarith [sq_nonneg ω₁]
    linarith
  have hf11 : |f11| <= (1 + ε) * (α * ωr) := by
    calc
      |f11| <= |arr| + |d11| := by simpa [f11] using abs_add_le arr d11
      _ <= |arr| + ε * |arr| := add_le_add_right hd11 _
      _ = (1 + ε) * |arr| := by ring
      _ <= (1 + ε) * (α * ωr) :=
        mul_le_mul_of_nonneg_left harr (by positivity)
  have hf01 : |f01| <= (1 + ε) * ω₁ := by
    calc
      |f01| <= |a1r| + |d01| := by simpa [f01] using abs_add_le a1r d01
      _ <= |a1r| + ε * |a1r| := add_le_add_right hd01 _
      _ = (1 + ε) * |a1r| := by ring
      _ = (1 + ε) * ω₁ := by rw [ha1r]
  have hf10 : |f10| <= (1 + ε) * ω₁ := by
    calc
      |f10| <= |a1r| + |d10| := by simpa [f10] using abs_add_le a1r d10
      _ <= |a1r| + ε * |a1r| := add_le_add_right hd10 _
      _ = (1 + ε) * |a1r| := by ring
      _ = (1 + ε) * ω₁ := by rw [ha1r]
  have hf00ωr : |f00| * ωr <= (1 + ε) * (α * ω₁ ^ 2) := by
    have hf00 : |f00| <= (1 + ε) * |a11| := by
      calc
        |f00| <= |a11| + |d00| := by simpa [f00] using abs_add_le a11 d00
        _ <= |a11| + ε * |a11| := add_le_add_right hd00 _
        _ = (1 + ε) * |a11| := by ring
    calc
      |f00| * ωr <= ((1 + ε) * |a11|) * ωr :=
        mul_le_mul_of_nonneg_right hf00 (le_of_lt hωr)
      _ = (1 + ε) * (|a11| * ωr) := by ring
      _ <= (1 + ε) * (α * ω₁ ^ 2) :=
        mul_le_mul_of_nonneg_left ha11prod (by positivity)
  have hw0eq : detf * w₀ = c₀ * f11 - f01 * c₁ := by
    dsimp [detf, f00, f01, f10, f11]
    linear_combination (arr + d11) * heq0 - (a1r + d01) * heq1
  have hw1eq : detf * w₁ = f00 * c₁ - c₀ * f10 := by
    dsimp [detf, f00, f01, f10, f11]
    linear_combination (a11 + d00) * heq1 - (a1r + d10) * heq0
  have hnum0 : |c₀ * f11 - f01 * c₁| <=
      (1 + ε) * (1 + α) * (ω₁ * ωr) := by
    calc
      |c₀ * f11 - f01 * c₁| <=
          |c₀| * |f11| + |f01| * |c₁| := by
        simpa [abs_mul] using abs_sub (c₀ * f11) (f01 * c₁)
      _ <= ω₁ * ((1 + ε) * (α * ωr)) +
          ((1 + ε) * ω₁) * ωr :=
        add_le_add
          (mul_le_mul hc₀ hf11 (abs_nonneg _) (le_of_lt hω₁))
          (mul_le_mul hf01 hc₁ (abs_nonneg _) (by positivity))
      _ = (1 + ε) * (1 + α) * (ω₁ * ωr) := by ring
  have hnum1 : |f00 * c₁ - c₀ * f10| <=
      (1 + ε) * (1 + α) * ω₁ ^ 2 := by
    have hfirst : |f00| * |c₁| <= (1 + ε) * (α * ω₁ ^ 2) :=
      (mul_le_mul_of_nonneg_left hc₁ (abs_nonneg f00)).trans hf00ωr
    have hsecond : |c₀| * |f10| <=
        ω₁ * ((1 + ε) * ω₁) :=
      mul_le_mul hc₀ hf10 (abs_nonneg _) (le_of_lt hω₁)
    calc
      |f00 * c₁ - c₀ * f10| <=
          |f00| * |c₁| + |c₀| * |f10| := by
        simpa [abs_mul] using abs_sub (f00 * c₁) (c₀ * f10)
      _ <= (1 + ε) * (α * ω₁ ^ 2) +
          ω₁ * ((1 + ε) * ω₁) := add_le_add hfirst hsecond
      _ = (1 + ε) * (1 + α) * ω₁ ^ 2 := by ring
  have hfactor : (1 + ε) * (1 + α) <= (341 : Real) / 200 := by
    have h1 : 1 + ε <= (1001 : Real) / 1000 := by linarith
    have h2 : 1 + α <= (5 : Real) / 3 := by linarith
    calc
      (1 + ε) * (1 + α) <=
          ((1001 : Real) / 1000) * ((5 : Real) / 3) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      _ <= (341 : Real) / 200 := by norm_num
  have hmul0 : (11 : Real) / 20 * ω₁ ^ 2 * |w₀| <=
      (341 : Real) / 200 * (ω₁ * ωr) := by
    calc
      (11 : Real) / 20 * ω₁ ^ 2 * |w₀| <= |detf| * |w₀| :=
        mul_le_mul_of_nonneg_right hdetf (abs_nonneg _)
      _ = |detf * w₀| := by rw [abs_mul]
      _ = |c₀ * f11 - f01 * c₁| := by rw [hw0eq]
      _ <= (1 + ε) * (1 + α) * (ω₁ * ωr) := hnum0
      _ <= (341 : Real) / 200 * (ω₁ * ωr) :=
        mul_le_mul_of_nonneg_right hfactor
          (mul_nonneg (le_of_lt hω₁) (le_of_lt hωr))
  have hmul1 : (11 : Real) / 20 * ω₁ ^ 2 * |w₁| <=
      (341 : Real) / 200 * ω₁ ^ 2 := by
    calc
      (11 : Real) / 20 * ω₁ ^ 2 * |w₁| <= |detf| * |w₁| :=
        mul_le_mul_of_nonneg_right hdetf (abs_nonneg _)
      _ = |detf * w₁| := by rw [abs_mul]
      _ = |f00 * c₁ - c₀ * f10| := by rw [hw1eq]
      _ <= (1 + ε) * (1 + α) * ω₁ ^ 2 := hnum1
      _ <= (341 : Real) / 200 * ω₁ ^ 2 :=
        mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
  constructor
  · have hpos : 0 < (11 : Real) / 20 * ω₁ := by positivity
    apply le_of_mul_le_mul_left ?_ hpos
    calc
      ((11 : Real) / 20 * ω₁) * (ω₁ * |w₀|) =
          (11 : Real) / 20 * ω₁ ^ 2 * |w₀| := by ring
      _ <= (341 : Real) / 200 * (ω₁ * ωr) := hmul0
      _ = ((11 : Real) / 20 * ω₁) * ((31 : Real) / 10 * ωr) := by ring
  · have hpos : 0 < (11 : Real) / 20 * ω₁ ^ 2 := by positivity
    apply le_of_mul_le_mul_left ?_ hpos
    calc
      ((11 : Real) / 20 * ω₁ ^ 2) * |w₁| =
          (11 : Real) / 20 * ω₁ ^ 2 * |w₁| := by ring
      _ <= (341 : Real) / 200 * ω₁ ^ 2 := hmul1
      _ = ((11 : Real) / 20 * ω₁ ^ 2) * ((31 : Real) / 10) := by ring

theorem higham11_4_case4_active_trailing_first_le_omegaOne
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (i : Fin n) :
    |higham11_2_bunchKaufmanRoundedActive A i.succ.succ 0| <=
      higham11_2_bunchKaufmanOmegaOne (by omega) A := by
  let p := higham11_2_bunchKaufmanFirstPerm (by omega)
    higham11_1_bunchParlettAlpha A
  let i₀ := higham11_2_firstIndex (by omega : 0 < n + 2)
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega : 0 < n + 2) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hr := higham11_2_bunchKaufmanMaxRow_ne_first_of_omegaOne_ne_zero
    (by omega : 0 < n + 2) A hcase.1
  have hr0 : higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A ≠
      (0 : Fin (n + 2)) := by
    simpa [higham11_2_firstIndex] using hr
  have hswap0 :
      Equiv.swap (1 : Fin (n + 2))
          (higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A) 0 = 0 := by
    exact Equiv.swap_apply_of_ne_of_ne (x := (0 : Fin (n + 2)))
      (show (0 : Fin (n + 2)) ≠ (1 : Fin (n + 2)) by
        apply Fin.ne_of_val_ne
        norm_num)
      (Ne.symm hr0)
  have hp0 : p (0 : Fin (n + 2)) = i₀ := by
    simp [p, i₀, higham11_2_bunchKaufmanFirstPerm, hbranch,
      higham11_2_firstIndex, hswap0]
  have hpi : p i.succ.succ ≠ i₀ := by
    intro h
    have heq : p i.succ.succ = p 0 := h.trans hp0.symm
    have := p.injective heq
    exact Fin.succ_ne_zero i.succ this
  have h := higham11_2_bunchKaufmanOmegaOne_spec
    (by omega : 0 < n + 2) A (p i.succ.succ)
  rw [if_neg hpi] at h
  change |A (p i.succ.succ) (p 0)| <=
    higham11_2_bunchKaufmanOmegaOne (by omega) A
  rw [hp0]
  simpa [i₀] using h

theorem higham11_4_case4_active_trailing_second_le_omegaRow
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (i : Fin n) :
    |higham11_2_bunchKaufmanRoundedActive A i.succ.succ (Fin.succ 0)| <=
      higham11_2_bunchKaufmanOmegaRow (by omega) A := by
  let p := higham11_2_bunchKaufmanFirstPerm (by omega)
    higham11_1_bunchParlettAlpha A
  let r := higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A
  have hp1 : p (Fin.succ 0 : Fin (n + 2)) = r := by
    simp [p, r, higham11_2_bunchKaufmanFirstPerm, hbranch]
  have hpi : p i.succ.succ ≠ r := by
    intro h
    have heq : p i.succ.succ = p (Fin.succ 0) := h.trans hp1.symm
    have := p.injective heq
    have hval := congrArg Fin.val this
    simp at hval
  have h := higham11_5_rookColumnMax_spec A r (p i.succ.succ)
  rw [if_neg hpi] at h
  change |A (p i.succ.succ) (p (Fin.succ 0))| <=
    higham11_2_bunchKaufmanOmegaRow (by omega) A
  rw [hp1]
  simpa [r, higham11_2_bunchKaufmanOmegaRow] using h

/-- The equation-(11.5) certificate for the actual case-(4) GEPP solve,
combined with the strict determinant margin left by Algorithm 11.2, gives
component bounds for the multipliers actually stored by the rounded
executor.  The smallness condition is stated on the certificate's genuine
entrywise perturbation coefficient `36u`. -/
theorem higham11_4_case4_flMultTwo_component_bounds
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000) (i : Fin n) :
    let ω₁ := higham11_2_bunchKaufmanOmegaOne (by omega) A
    let ωr := higham11_2_bunchKaufmanOmegaRow (by omega) A
    ω₁ * |higham11_2_bunchKaufmanFlMultTwo fp A i 0| <=
        (31 : Real) / 10 * ωr ∧
      |higham11_2_bunchKaufmanFlMultTwo fp A i 1| <= (31 : Real) / 10 := by
  let B := higham11_2_bunchKaufmanRoundedActive A
  let ω₁ := higham11_2_bunchKaufmanOmegaOne (by omega) A
  let ωr := higham11_2_bunchKaufmanOmegaRow (by omega) A
  let i₀ := higham11_2_firstIndex (by omega : 0 < n + 2)
  let r := higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A
  let w := higham11_2_bunchKaufmanFlMultTwo fp A i
  obtain ⟨DeltaE, hDelta, heq⟩ :=
    higham11_2_bunchKaufmanFlMultTwo_active_certificate
      fp hval9 hsmall9 A hA hbranch hsecond i
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega : 0 < n + 2) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hω₁0 : 0 <= ω₁ := higham11_2_bunchKaufmanOmegaOne_nonneg _ _
  have hω₁ : 0 < ω₁ := lt_of_le_of_ne hω₁0 (Ne.symm hcase.1)
  have hω₁r : ω₁ <= ωr := higham11_4_omegaOne_le_omegaRow _ A hA
  have hωr : 0 < ωr := lt_of_lt_of_le hω₁ hω₁r
  have hBsymm : IsSymmetricFiniteMatrix B := by
    exact higham11_2_bunchKaufmanRoundedActive_symmetric A hA
  have hlead := higham11_2_bunchKaufmanSelectedTwoBlock_eq_activeLeading
    A hbranch
  have hB00 : B 0 0 = A i₀ i₀ := by
    change higham11_2_bunchKaufmanExactActive A
      (embedTwo n 0) (embedTwo n 0) = A i₀ i₀
    rw [← hlead 0 0]
    simp [B, higham11_2_bunchKaufmanSelectedTwoBlock, i₀]
  have hB01 : B 0 1 = A i₀ r := by
    change higham11_2_bunchKaufmanExactActive A
      (embedTwo n 0) (embedTwo n 1) = A i₀ r
    rw [← hlead 0 1]
    rfl
  have hB01r : B 0 1 = A r i₀ := by
    rw [hB01, hA i₀ r]
  have hB11 : B 1 1 = A r r := by
    change higham11_2_bunchKaufmanExactActive A
      (embedTwo n 1) (embedTwo n 1) = A r r
    rw [← hlead 1 1]
    rfl
  have ha1r : |B 0 1| = ω₁ := by
    rw [hB01r]
    exact higham11_2_bunchKaufmanMaxRow_attains_omegaOne
      (by omega : 0 < n + 2) A hcase.1
  have hdet :
      (1 - higham11_1_bunchParlettAlpha ^ 2) * ω₁ ^ 2 <=
        |B 0 0 * B 1 1 - B 0 1 ^ 2| := by
    simpa [hB00, hB01r, hB11] using
      (higham11_4_bunch_kaufman_case4_twoByTwo_absdet_lower
        (A i₀ i₀) (A r i₀) (A r r) ω₁ ωr hcase
        (higham11_2_bunchKaufmanMaxRow_attains_omegaOne
          (by omega : 0 < n + 2) A hcase.1))
  rcases higham11_2_bunch_kaufman_case4_tests
      higham11_1_bunchParlettAlpha (A i₀ i₀) (A r r) ω₁ ωr
      hcase with ⟨_, _, hprod, harr⟩
  have hprod' : |B 0 0| * ωr <=
      higham11_1_bunchParlettAlpha * ω₁ ^ 2 := by
    simpa [hB00] using le_of_lt hprod
  have harr' : |B 1 1| <=
      higham11_1_bunchParlettAlpha * ωr := by
    simpa [hB11] using le_of_lt harr
  have hc0 : |B i.succ.succ (0 : Fin (n + 2))| <= ω₁ :=
    higham11_4_case4_active_trailing_first_le_omegaOne A hbranch i
  have hc1 : |B i.succ.succ (Fin.succ 0 : Fin (n + 2))| <= ωr :=
    higham11_4_case4_active_trailing_second_le_omegaRow A hbranch i
  have hDelta00 : |DeltaE (0 : Fin 2) 0| <=
      (36 * fp.u) * |B 0 0| := hDelta 0 0
  have hDelta01 : |DeltaE (0 : Fin 2) 1| <=
      (36 * fp.u) * |B 0 1| := hDelta 0 1
  have hDelta10 : |DeltaE (1 : Fin 2) 0| <=
      (36 * fp.u) * |B 0 1| := by
    calc
      |DeltaE (1 : Fin 2) 0| <= (36 * fp.u) * |B 1 0| := by
        simpa [B] using hDelta (1 : Fin 2) 0
      _ = (36 * fp.u) * |B 0 1| := by
        rw [hBsymm (1 : Fin (n + 2)) 0]
  have hDelta11 : |DeltaE (1 : Fin 2) 1| <=
      (36 * fp.u) * |B 1 1| := hDelta 1 1
  have heq0 :
      (B 0 0 + DeltaE 0 0) * w 0 +
          (B 0 1 + DeltaE 0 1) * w 1 = B i.succ.succ 0 := by
    simpa [B, w, Fin.sum_univ_two] using heq (0 : Fin 2)
  have heq1 :
      (B 0 1 + DeltaE 1 0) * w 0 +
          (B 1 1 + DeltaE 1 1) * w 1 = B i.succ.succ (Fin.succ 0) := by
    simpa [B, w, Fin.sum_univ_two, hBsymm (1 : Fin (n + 2)) 0] using
      heq (1 : Fin 2)
  have hu0 : 0 <= 36 * fp.u := mul_nonneg (by norm_num) fp.u_nonneg
  exact higham11_4_perturbed_case4_solve_component_bounds
    (B 0 0) (B 0 1) (B 1 1) ω₁ ωr
    (B i.succ.succ 0) (B i.succ.succ (Fin.succ 0)) (w 0) (w 1)
    (DeltaE 0 0) (DeltaE 0 1) (DeltaE 1 0) (DeltaE 1 1) (36 * fp.u)
    hu0 huSmall hω₁ hωr ha1r hdet hprod' harr' hc0 hc1
    hDelta00 hDelta01 hDelta10 hDelta11 heq0 heq1

private theorem higham11_4_case4_four_term_path_le_thirtyThree
    (e00 e01 e10 e11 xi0 xi1 xj0 xj1 ω₁ ωr M : Real)
    (hω₁ : 0 < ω₁) (hωr : 0 < ωr) (hωrM : ωr <= M)
    (he00 : e00 * ωr <= higham11_1_bunchParlettAlpha * ω₁ ^ 2)
    (he01 : e01 = ω₁) (he10 : e10 = ω₁)
    (he11 : e11 <= higham11_1_bunchParlettAlpha * ωr)
    (hxi0 : ω₁ * xi0 <= (31 : Real) / 10 * ωr)
    (hxi1 : xi1 <= (31 : Real) / 10)
    (hxj0 : ω₁ * xj0 <= (31 : Real) / 10 * ωr)
    (hxj1 : xj1 <= (31 : Real) / 10)
    (he00nonneg : 0 <= e00) (he01nonneg : 0 <= e01)
    (he10nonneg : 0 <= e10) (he11nonneg : 0 <= e11)
    (hxi0nonneg : 0 <= xi0) (hxi1nonneg : 0 <= xi1)
    (hxj0nonneg : 0 <= xj0) (hxj1nonneg : 0 <= xj1) :
    (xi0 * e00 * xj0 + xi0 * e01 * xj1) +
        (xi1 * e10 * xj0 + xi1 * e11 * xj1) <= 33 * M := by
  let c : Real := (31 : Real) / 10
  let α : Real := higham11_1_bunchParlettAlpha
  have hα0 : 0 <= α := by
    exact le_of_lt (by
      simpa [α, higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  have hα : α <= (2 : Real) / 3 := by
    simpa [α] using higham11_4_bunchAlpha_le_two_thirds
  have hxi0' : xi0 <= c * ωr / ω₁ := by
    apply (le_div_iff₀ hω₁).2
    simpa [c, mul_comm] using hxi0
  have hxj0' : xj0 <= c * ωr / ω₁ := by
    apply (le_div_iff₀ hω₁).2
    simpa [c, mul_comm] using hxj0
  have he00' : e00 <= α * ω₁ ^ 2 / ωr := by
    apply (le_div_iff₀ hωr).2
    simpa [α] using he00
  have ht00 : xi0 * e00 * xj0 <= c ^ 2 * α * ωr := by
    calc
      xi0 * e00 * xj0 <=
          (c * ωr / ω₁) * (α * ω₁ ^ 2 / ωr) *
            (c * ωr / ω₁) := by
        exact mul_le_mul
          (mul_le_mul hxi0' he00' he00nonneg (by positivity)) hxj0'
          hxj0nonneg (by positivity)
      _ = c ^ 2 * α * ωr := by
        field_simp [ne_of_gt hω₁, ne_of_gt hωr]
  have ht01 : xi0 * e01 * xj1 <= c ^ 2 * ωr := by
    calc
      xi0 * e01 * xj1 <= (c * ωr / ω₁) * ω₁ * c := by
        exact mul_le_mul
          (mul_le_mul hxi0' (le_of_eq he01) he01nonneg (by positivity))
          (by simpa [c] using hxj1) hxj1nonneg (by positivity)
      _ = c ^ 2 * ωr := by
        field_simp [ne_of_gt hω₁]
  have ht10 : xi1 * e10 * xj0 <= c ^ 2 * ωr := by
    calc
      xi1 * e10 * xj0 <= c * ω₁ * (c * ωr / ω₁) := by
        exact mul_le_mul
          (mul_le_mul (by simpa [c] using hxi1) (le_of_eq he10)
            he10nonneg (by positivity)) hxj0' hxj0nonneg (by positivity)
      _ = c ^ 2 * ωr := by
        field_simp [ne_of_gt hω₁]
  have ht11 : xi1 * e11 * xj1 <= c ^ 2 * α * ωr := by
    calc
      xi1 * e11 * xj1 <= c * (α * ωr) * c := by
        exact mul_le_mul
          (mul_le_mul (by simpa [c] using hxi1) (by simpa [α] using he11)
            he11nonneg (by positivity)) (by simpa [c] using hxj1)
          hxj1nonneg (by positivity)
      _ = c ^ 2 * α * ωr := by ring
  have hsum :
      (xi0 * e00 * xj0 + xi0 * e01 * xj1) +
          (xi1 * e10 * xj0 + xi1 * e11 * xj1) <=
        2 * c ^ 2 * (1 + α) * ωr := by
    calc
      (xi0 * e00 * xj0 + xi0 * e01 * xj1) +
          (xi1 * e10 * xj0 + xi1 * e11 * xj1) <=
          (c ^ 2 * α * ωr + c ^ 2 * ωr) +
            (c ^ 2 * ωr + c ^ 2 * α * ωr) :=
        add_le_add (add_le_add ht00 ht01) (add_le_add ht10 ht11)
      _ = 2 * c ^ 2 * (1 + α) * ωr := by ring
  have hconst : 2 * c ^ 2 * (1 + α) <= 33 := by
    dsimp [c]
    nlinarith
  exact hsum.trans <| (mul_le_mul_of_nonneg_right hconst (le_of_lt hωr)).trans <|
    mul_le_mul_of_nonneg_left hωrM (by norm_num)

/-- The absolute leading-block path generated by the *computed* multipliers
of an accepted case-(4) node is strictly below the source constant `36`.
The margin (`33`) is what permits a source-honest finite-precision global
bound without identifying exact and computed factors. -/
theorem higham11_4_pivotPathTwoAbs_le_thirtyThree_case4
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000) (i j : Fin n) :
    higham11_2_bunchKaufmanPivotPathTwoAbs fp A i j <=
      33 * higham11_4_roundedActiveMax A := by
  let B := higham11_2_bunchKaufmanRoundedActive A
  let ω₁ := higham11_2_bunchKaufmanOmegaOne (by omega) A
  let ωr := higham11_2_bunchKaufmanOmegaRow (by omega) A
  let i₀ := higham11_2_firstIndex (by omega : 0 < n + 2)
  let r := higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A
  let wi := higham11_2_bunchKaufmanFlMultTwo fp A i
  let wj := higham11_2_bunchKaufmanFlMultTwo fp A j
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega : 0 < n + 2) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hω₁0 : 0 <= ω₁ := higham11_2_bunchKaufmanOmegaOne_nonneg _ _
  have hω₁ : 0 < ω₁ := lt_of_le_of_ne hω₁0 (Ne.symm hcase.1)
  have hω₁r : ω₁ <= ωr := higham11_4_omegaOne_le_omegaRow _ A hA
  have hωr : 0 < ωr := lt_of_lt_of_le hω₁ hω₁r
  have hωrM : ωr <= higham11_4_roundedActiveMax A :=
    higham11_4_omegaRow_le_roundedActiveMax _ A
  have hBsymm : IsSymmetricFiniteMatrix B :=
    higham11_2_bunchKaufmanRoundedActive_symmetric A hA
  have hlead := higham11_2_bunchKaufmanSelectedTwoBlock_eq_activeLeading
    A hbranch
  have hB00 : B 0 0 = A i₀ i₀ := by
    change higham11_2_bunchKaufmanExactActive A
      (embedTwo n 0) (embedTwo n 0) = A i₀ i₀
    rw [← hlead 0 0]
    simp [higham11_2_bunchKaufmanSelectedTwoBlock, i₀]
  have hB01r : B 0 1 = A r i₀ := by
    have hB01 : B 0 1 = A i₀ r := by
      change higham11_2_bunchKaufmanExactActive A
        (embedTwo n 0) (embedTwo n 1) = A i₀ r
      rw [← hlead 0 1]
      rfl
    rw [hB01, hA i₀ r]
  have hB11 : B 1 1 = A r r := by
    change higham11_2_bunchKaufmanExactActive A
      (embedTwo n 1) (embedTwo n 1) = A r r
    rw [← hlead 1 1]
    rfl
  have he01 : |B 0 1| = ω₁ := by
    rw [hB01r]
    exact higham11_2_bunchKaufmanMaxRow_attains_omegaOne
      (by omega : 0 < n + 2) A hcase.1
  have he10 : |B 1 0| = ω₁ := by
    rw [hBsymm (1 : Fin (n + 2)) 0, he01]
  rcases higham11_2_bunch_kaufman_case4_tests
      higham11_1_bunchParlettAlpha (A i₀ i₀) (A r r) ω₁ ωr
      hcase with ⟨_, _, hprod, harr⟩
  have he00 : |B 0 0| * ωr <=
      higham11_1_bunchParlettAlpha * ω₁ ^ 2 := by
    simpa [hB00] using le_of_lt hprod
  have he11 : |B 1 1| <= higham11_1_bunchParlettAlpha * ωr := by
    simpa [hB11] using le_of_lt harr
  obtain ⟨hi0, hi1⟩ := higham11_4_case4_flMultTwo_component_bounds
    fp hval9 hsmall9 A hA hbranch hsecond huSmall i
  obtain ⟨hj0, hj1⟩ := higham11_4_case4_flMultTwo_component_bounds
    fp hval9 hsmall9 A hA hbranch hsecond huSmall j
  have hpath := higham11_4_case4_four_term_path_le_thirtyThree
    |B 0 0| |B 0 1| |B 1 0| |B 1 1|
    |wi 0| |wi 1| |wj 0| |wj 1| ω₁ ωr
    (higham11_4_roundedActiveMax A) hω₁ hωr hωrM he00 he01 he10 he11
    (by simpa [wi, ω₁, ωr] using hi0)
    (by simpa [wi] using hi1)
    (by simpa [wj, ω₁, ωr] using hj0)
    (by simpa [wj] using hj1)
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
  simpa [higham11_2_bunchKaufmanPivotPathTwoAbs, Fin.sum_univ_two,
    B, wi, wj] using hpath

/-- Each pivot row touching a computed case-(4) multiplier row contributes
at most six times the current active maximum. -/
theorem higham11_4_pivotRowTwoAbs_le_six_case4
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    (p : Fin 2) (j : Fin n) :
    higham11_2_bunchKaufmanPivotRowTwoAbs fp A p j <=
      6 * higham11_4_roundedActiveMax A := by
  let B := higham11_2_bunchKaufmanRoundedActive A
  let ω₁ := higham11_2_bunchKaufmanOmegaOne (by omega) A
  let ωr := higham11_2_bunchKaufmanOmegaRow (by omega) A
  let i₀ := higham11_2_firstIndex (by omega : 0 < n + 2)
  let r := higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A
  let w := higham11_2_bunchKaufmanFlMultTwo fp A j
  let c : Real := (31 : Real) / 10
  let α : Real := higham11_1_bunchParlettAlpha
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega : 0 < n + 2) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hω₁0 : 0 <= ω₁ := higham11_2_bunchKaufmanOmegaOne_nonneg _ _
  have hω₁ : 0 < ω₁ := lt_of_le_of_ne hω₁0 (Ne.symm hcase.1)
  have hω₁r : ω₁ <= ωr := higham11_4_omegaOne_le_omegaRow _ A hA
  have hωr : 0 < ωr := lt_of_lt_of_le hω₁ hω₁r
  have hω₁M : ω₁ <= higham11_4_roundedActiveMax A :=
    higham11_4_omegaOne_le_roundedActiveMax _ A
  have hωrM : ωr <= higham11_4_roundedActiveMax A :=
    higham11_4_omegaRow_le_roundedActiveMax _ A
  have hBsymm : IsSymmetricFiniteMatrix B :=
    higham11_2_bunchKaufmanRoundedActive_symmetric A hA
  have hlead := higham11_2_bunchKaufmanSelectedTwoBlock_eq_activeLeading
    A hbranch
  have hB00 : B 0 0 = A i₀ i₀ := by
    change higham11_2_bunchKaufmanExactActive A
      (embedTwo n 0) (embedTwo n 0) = A i₀ i₀
    rw [← hlead 0 0]
    simp [higham11_2_bunchKaufmanSelectedTwoBlock, i₀]
  have hB01r : B 0 1 = A r i₀ := by
    have hB01 : B 0 1 = A i₀ r := by
      change higham11_2_bunchKaufmanExactActive A
        (embedTwo n 0) (embedTwo n 1) = A i₀ r
      rw [← hlead 0 1]
      rfl
    rw [hB01, hA i₀ r]
  have hB11 : B 1 1 = A r r := by
    change higham11_2_bunchKaufmanExactActive A
      (embedTwo n 1) (embedTwo n 1) = A r r
    rw [← hlead 1 1]
    rfl
  have he01 : |B 0 1| = ω₁ := by
    rw [hB01r]
    exact higham11_2_bunchKaufmanMaxRow_attains_omegaOne
      (by omega : 0 < n + 2) A hcase.1
  have he10 : |B 1 0| = ω₁ := by
    rw [hBsymm (1 : Fin (n + 2)) 0, he01]
  rcases higham11_2_bunch_kaufman_case4_tests
      higham11_1_bunchParlettAlpha (A i₀ i₀) (A r r) ω₁ ωr
      hcase with ⟨_, _, hprod, harr⟩
  have he00 : |B 0 0| <= α * ω₁ ^ 2 / ωr := by
    apply (le_div_iff₀ hωr).2
    simpa [hB00, α] using le_of_lt hprod
  have he11 : |B 1 1| <= α * ωr := by
    simpa [hB11, α] using le_of_lt harr
  obtain ⟨hw0s, hw1⟩ := higham11_4_case4_flMultTwo_component_bounds
    fp hval9 hsmall9 A hA hbranch hsecond huSmall j
  have hw0 : |w 0| <= c * ωr / ω₁ := by
    apply (le_div_iff₀ hω₁).2
    simpa [w, c, ω₁, ωr, mul_comm] using hw0s
  have hw1' : |w 1| <= c := by simpa [w, c] using hw1
  have hα0 : 0 <= α := by
    exact le_of_lt (by
      simpa [α, higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  have hα : α <= (2 : Real) / 3 := by
    simpa [α] using higham11_4_bunchAlpha_le_two_thirds
  have hc6 : c * (1 + α) <= 6 := by
    dsimp [c]
    nlinarith
  fin_cases p
  · have ht0 : |B 0 0| * |w 0| <= c * α * ω₁ := by
      calc
        |B 0 0| * |w 0| <=
            (α * ω₁ ^ 2 / ωr) * (c * ωr / ω₁) :=
          mul_le_mul he00 hw0 (abs_nonneg _) (by positivity)
        _ = c * α * ω₁ := by
          field_simp [ne_of_gt hω₁, ne_of_gt hωr]
    have ht1 : |B 0 1| * |w 1| <= c * ω₁ := by
      rw [he01]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left hw1' (le_of_lt hω₁))
    simp only [higham11_2_bunchKaufmanPivotRowTwoAbs, Fin.sum_univ_two]
    calc
      |B 0 0| * |w 0| + |B 0 1| * |w 1| <=
          c * α * ω₁ + c * ω₁ := add_le_add ht0 ht1
      _ = (c * (1 + α)) * ω₁ := by ring
      _ <= 6 * ω₁ := mul_le_mul_of_nonneg_right hc6 (le_of_lt hω₁)
      _ <= 6 * higham11_4_roundedActiveMax A :=
        mul_le_mul_of_nonneg_left hω₁M (by norm_num)
  · have ht0 : |B 1 0| * |w 0| <= c * ωr := by
      rw [he10]
      calc
        ω₁ * |w 0| <= ω₁ * (c * ωr / ω₁) :=
          mul_le_mul_of_nonneg_left hw0 (le_of_lt hω₁)
        _ = c * ωr := by field_simp [ne_of_gt hω₁]
    have ht1 : |B 1 1| * |w 1| <= c * α * ωr := by
      calc
        |B 1 1| * |w 1| <= (α * ωr) * c :=
          mul_le_mul he11 hw1' (abs_nonneg _) (by positivity)
        _ = c * α * ωr := by ring
    simp only [higham11_2_bunchKaufmanPivotRowTwoAbs, Fin.sum_univ_two]
    calc
      |B 1 0| * |w 0| + |B 1 1| * |w 1| <=
          c * ωr + c * α * ωr := add_le_add ht0 ht1
      _ = (c * (1 + α)) * ωr := by ring
      _ <= 6 * ωr := mul_le_mul_of_nonneg_right hc6 (le_of_lt hωr)
      _ <= 6 * higham11_4_roundedActiveMax A :=
        mul_le_mul_of_nonneg_left hωrM (by norm_num)

/-- Column analogue of `higham11_4_pivotRowTwoAbs_le_six_case4`, obtained
from the symmetry of the actual permuted active block. -/
theorem higham11_4_pivotColTwoAbs_le_six_case4
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    (i : Fin n) (q : Fin 2) :
    higham11_2_bunchKaufmanPivotColTwoAbs fp A i q <=
      6 * higham11_4_roundedActiveMax A := by
  have hB := higham11_2_bunchKaufmanRoundedActive_symmetric A hA
  have heq :
      higham11_2_bunchKaufmanPivotColTwoAbs fp A i q =
        higham11_2_bunchKaufmanPivotRowTwoAbs fp A q i := by
    unfold higham11_2_bunchKaufmanPivotColTwoAbs
      higham11_2_bunchKaufmanPivotRowTwoAbs
    apply Finset.sum_congr rfl
    intro p _
    rw [hB (embedTwo n p) (embedTwo n q)]
    ring
  rw [heq]
  exact higham11_4_pivotRowTwoAbs_le_six_case4
    fp hval9 hsmall9 A hA hbranch hsecond huSmall q i

theorem higham11_4_roundedActive_entry_le_currentMax {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin (n + 2)) :
    |higham11_2_bunchKaufmanRoundedActive A i j| <=
      higham11_4_roundedActiveMax A := by
  exact higham11_4_entry_le_roundedActiveMax A
    (higham11_2_bunchKaufmanFirstPerm (by omega)
      higham11_1_bunchParlettAlpha A i)
    (higham11_2_bunchKaufmanFirstPerm (by omega)
      higham11_1_bunchParlettAlpha A j)

/-- One computed scalar multiplier gives a pivot-row/column absolute path of
at most twice the current active maximum when `u <= 1`. -/
theorem higham11_4_scalar_pivot_cross_le_two
    (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hpivot : higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0)
    (hu : fp.u <= 1) (i : Fin (n + 1)) :
    |higham11_2_bunchKaufmanRoundedActive A 0 0| *
        |higham11_2_bunchKaufmanFlMultOne fp A i| <=
      2 * higham11_4_roundedActiveMax A := by
  let B := higham11_2_bunchKaufmanRoundedActive A
  let w := higham11_2_bunchKaufmanFlMultOne fp A i
  have hres := higham11_2_bunchKaufmanFlMultOne_row_residual
    fp A hA hpivot i
  have hres' : |B 0 0 * w - B 0 i.succ| <=
      fp.u * |B 0 i.succ| := by
    simpa [B, w] using hres
  have hc := higham11_4_roundedActive_entry_le_currentMax A 0 i.succ
  have hprod : |B 0 0 * w| <= (1 + fp.u) * |B 0 i.succ| := by
    calc
      |B 0 0 * w| = |(B 0 0 * w - B 0 i.succ) + B 0 i.succ| := by
        congr 1
        ring
      _ <= |B 0 0 * w - B 0 i.succ| + |B 0 i.succ| := abs_add_le _ _
      _ <= fp.u * |B 0 i.succ| + |B 0 i.succ| :=
        add_le_add hres' (le_refl _)
      _ = (1 + fp.u) * |B 0 i.succ| := by ring
  calc
    |B 0 0| * |w| = |B 0 0 * w| := by rw [abs_mul]
    _ <= (1 + fp.u) * |B 0 i.succ| := hprod
    _ <= 2 * higham11_4_roundedActiveMax A :=
      mul_le_mul (by linarith) hc (abs_nonneg _) (by linarith [fp.u_nonneg])

/-! Small absolute-product reductions for entries touching the newly
embedded pivot block.  The trailing/trailing reductions already live in the
global factor module. -/

private theorem higham11_4_blockOne_absProduct_00 {n : Nat}
    (w : Fin n -> Real) (Ls : Fin n -> Fin n -> Real)
    (d : Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 1)
      (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds) 0 0 = |d| := by
  simp [higham11_4_bunchKaufmanProductEntry, Fin.sum_univ_succ]

private theorem higham11_4_blockOne_absProduct_0s {n : Nat}
    (w : Fin n -> Real) (Ls : Fin n -> Fin n -> Real)
    (d : Real) (Ds : Fin n -> Fin n -> Real) (j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1)
      (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds) 0 j.succ =
        |d| * |w j| := by
  simp [higham11_4_bunchKaufmanProductEntry, Fin.sum_univ_succ]

private theorem higham11_4_blockOne_absProduct_s0 {n : Nat}
    (w : Fin n -> Real) (Ls : Fin n -> Fin n -> Real)
    (d : Real) (Ds : Fin n -> Fin n -> Real) (i : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1)
      (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds) i.succ 0 =
        |w i| * |d| := by
  simp [higham11_4_bunchKaufmanProductEntry, Fin.sum_univ_succ]

private theorem higham11_4_blockTwo_absProduct_00 {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      0 0 = |E 0 0| := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoD_00,
    higham11_2_blockTwoD_01, higham11_2_blockTwoD_0t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

private theorem higham11_4_blockTwo_absProduct_01 {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      0 (Fin.succ 0) = |E 0 1| := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoD_00, higham11_2_blockTwoD_01,
    higham11_2_blockTwoD_0t, abs_zero, abs_one, zero_mul, mul_zero,
    one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

private theorem higham11_4_blockTwo_absProduct_10 {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      (Fin.succ 0) 0 = |E 1 0| := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoD_10, higham11_2_blockTwoD_11,
    higham11_2_blockTwoD_1t, abs_zero, abs_one, zero_mul, mul_zero,
    one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

private theorem higham11_4_blockTwo_absProduct_11 {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      (Fin.succ 0) (Fin.succ 0) = |E 1 1| := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_1t, higham11_2_blockTwoD_10,
    higham11_2_blockTwoD_11, higham11_2_blockTwoD_1t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

private theorem higham11_4_blockOne_absProduct_global_budget {n : Nat}
    (w : Fin n -> Real) (Ls : Fin n -> Fin n -> Real)
    (d : Real) (Ds : Fin n -> Fin n -> Real) (M : Real)
    (hM : 0 <= M) (h00 : |d| <= M)
    (hcross : forall i : Fin n, |d| * |w i| <= 2 * M)
    (htrail : forall i j : Fin n,
      higham11_4_bunchKaufmanProductEntry (n + 1)
        (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds)
        i.succ j.succ <= 8 * M + 40 * (n : Real) * M) :
    forall I J : Fin (n + 1),
      higham11_4_bunchKaufmanProductEntry (n + 1)
        (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds) I J <=
          40 * (n + 1 : Nat) * M := by
  have hn : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
  have hhead : M <= 40 * (n + 1 : Nat) * M := by
    have hc : (1 : Real) <= 40 * (n + 1 : Nat) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith
    simpa using mul_le_mul_of_nonneg_right hc hM
  have hcrossBudget : 2 * M <= 40 * (n + 1 : Nat) * M := by
    have hc : (2 : Real) <= 40 * (n + 1 : Nat) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith
    exact mul_le_mul_of_nonneg_right hc hM
  have htrailBudget :
      8 * M + 40 * (n : Real) * M <= 40 * (n + 1 : Nat) * M := by
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith
  intro I J
  refine Fin.cases ?_ (fun i => ?_) I
  · refine Fin.cases ?_ (fun j => ?_) J
    · rw [higham11_4_blockOne_absProduct_00]
      exact h00.trans hhead
    · rw [higham11_4_blockOne_absProduct_0s]
      exact (hcross j).trans hcrossBudget
  · refine Fin.cases ?_ (fun j => ?_) J
    · rw [higham11_4_blockOne_absProduct_s0]
      have h := hcross i
      rw [mul_comm] at h
      exact h.trans hcrossBudget
    · exact (htrail i j).trans htrailBudget

private theorem higham11_4_blockTwo_absProduct_global_budget {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real)
    (M : Real) (hM : 0 <= M)
    (hpp00 :
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        0 0 <= M)
    (hpp01 :
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        0 (Fin.succ 0) <= M)
    (hpp10 :
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        (Fin.succ 0) 0 <= M)
    (hpp11 :
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        (Fin.succ 0) (Fin.succ 0) <= M)
    (h0t : forall j : Fin n,
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        0 j.succ.succ <= 6 * M)
    (h1t : forall j : Fin n,
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        (Fin.succ 0) j.succ.succ <= 6 * M)
    (ht0 : forall i : Fin n,
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        i.succ.succ 0 <= 6 * M)
    (ht1 : forall i : Fin n,
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        i.succ.succ (Fin.succ 0) <= 6 * M)
    (htt : forall i j : Fin n,
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        i.succ.succ j.succ.succ <= 33 * M + 40 * (n : Real) * M) :
    forall I J : Fin (n + 2),
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds) I J <=
          40 * (n + 2 : Nat) * M := by
  have hn : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
  have hppBudget : M <= 40 * (n + 2 : Nat) * M := by
    have hc : (1 : Real) <= 40 * (n + 2 : Nat) := by
      norm_num [Nat.cast_add, Nat.cast_ofNat]
      nlinarith
    simpa using mul_le_mul_of_nonneg_right hc hM
  have hptBudget : 6 * M <= 40 * (n + 2 : Nat) * M := by
    have hc : (6 : Real) <= 40 * (n + 2 : Nat) := by
      norm_num [Nat.cast_add, Nat.cast_ofNat]
      nlinarith
    exact mul_le_mul_of_nonneg_right hc hM
  have httBudget :
      33 * M + 40 * (n : Real) * M <= 40 * (n + 2 : Nat) * M := by
    norm_num [Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  intro I J
  refine Fin.cases ?_ (fun K => ?_) I
  · refine Fin.cases ?_ (fun L => ?_) J
    · exact hpp00.trans hppBudget
    · refine Fin.cases ?_ (fun j => ?_) L
      · exact hpp01.trans hppBudget
      · exact (h0t j).trans hptBudget
  · refine Fin.cases ?_ (fun L => ?_) J
    · refine Fin.cases ?_ (fun i => ?_) K
      · exact hpp10.trans hppBudget
      · exact (ht0 i).trans hptBudget
    · refine Fin.cases ?_ (fun j => ?_) L
      · refine Fin.cases ?_ (fun i => ?_) K
        · exact hpp11.trans hppBudget
        · exact (ht1 i).trans hptBudget
      · refine Fin.cases ?_ (fun i => ?_) K
        · exact (h1t j).trans hptBudget
        · exact (htt i j).trans httBudget

namespace Higham11RoundedBunchKaufmanExecution

/-- Maximum entry magnitude over the actual rounded active matrices visited by
an execution.  This is the numerator in the source definition of the element
growth factor. -/
noncomputable def roundedStageMax : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    Higham11RoundedBunchKaufmanExecution fp A -> Real
  | _, _, .nil A => higham11_4_roundedActiveMax A
  | _, _, .noAction A _ _ tail =>
      max (higham11_4_roundedActiveMax A) tail.roundedStageMax
  | _, _, .case1 A _ _ tail =>
      max (higham11_4_roundedActiveMax A) tail.roundedStageMax
  | _, _, .case2 A _ _ tail =>
      max (higham11_4_roundedActiveMax A) tail.roundedStageMax
  | _, _, .case3 A _ _ tail =>
      max (higham11_4_roundedActiveMax A) tail.roundedStageMax
  | _, _, .case4 A _ _ _ tail =>
      max (higham11_4_roundedActiveMax A) tail.roundedStageMax
  | _, _, .case4Breakdown A _ _ _ => higham11_4_roundedActiveMax A

theorem roundedStageMax_nonneg : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
    0 <= exec.roundedStageMax
  | _, _, .nil A => higham11_4_roundedActiveMax_nonneg A
  | _, _, .noAction A _ _ tail =>
      le_max_of_le_left (higham11_4_roundedActiveMax_nonneg A)
  | _, _, .case1 A _ _ tail =>
      le_max_of_le_left (higham11_4_roundedActiveMax_nonneg A)
  | _, _, .case2 A _ _ tail =>
      le_max_of_le_left (higham11_4_roundedActiveMax_nonneg A)
  | _, _, .case3 A _ _ tail =>
      le_max_of_le_left (higham11_4_roundedActiveMax_nonneg A)
  | _, _, .case4 A _ _ _ tail =>
      le_max_of_le_left (higham11_4_roundedActiveMax_nonneg A)
  | _, _, .case4Breakdown A _ _ _ =>
      higham11_4_roundedActiveMax_nonneg A

theorem currentMax_le_roundedStageMax : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
    higham11_4_roundedActiveMax A <= exec.roundedStageMax
  | _, _, .nil A => le_rfl
  | _, _, .noAction A _ _ tail => le_max_left _ _
  | _, _, .case1 A _ _ tail => le_max_left _ _
  | _, _, .case2 A _ _ tail => le_max_left _ _
  | _, _, .case3 A _ _ tail => le_max_left _ _
  | _, _, .case4 A _ _ _ tail => le_max_left _ _
  | _, _, .case4Breakdown A _ _ _ => le_rfl

theorem tail_roundedStageMax_le_noAction {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) :
    tail.roundedStageMax <=
      (Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail).roundedStageMax :=
  le_max_right _ _

theorem tail_roundedStageMax_le_case1 {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
    tail.roundedStageMax <=
      (Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail).roundedStageMax :=
  le_max_right _ _

theorem tail_roundedStageMax_le_case2 {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
    tail.roundedStageMax <=
      (Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail).roundedStageMax :=
  le_max_right _ _

theorem tail_roundedStageMax_le_case3 {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
    tail.roundedStageMax <=
      (Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail).roundedStageMax :=
  le_max_right _ _

theorem tail_roundedStageMax_le_case4 {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
    tail.roundedStageMax <=
      (Higham11RoundedBunchKaufmanExecution.case4 A hA hbranch hsecond tail).roundedStageMax :=
  le_max_right _ _

private theorem flatAbsProduct_le_forty_mul_dimension_mul_roundedStageMax_aux
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    (hu : fp.u <= 1) : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) -> exec.Completed ->
    forall i j : Fin n,
      exec.flatAbsProduct i j <= 40 * (n : Real) * exec.roundedStageMax
  | _, _, .nil _ => by
      intro _ i
      exact Fin.elim0 i
  | n + 1, _, .noAction A hA hbranch tail => by
      intro hcompleted I J
      let whole := Higham11RoundedBunchKaufmanExecution.noAction
        A hA hbranch tail
      let M := whole.roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg whole
      have hcur : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax whole
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_noAction A hA hbranch tail
      have ih := flatAbsProduct_le_forty_mul_dimension_mul_roundedStageMax_aux
        hval9 hsmall9 huSmall hu tail hcompleted
      change higham11_4_bunchKaufmanProductEntry (n + 1)
        (higham11_2_blockOneL (fun _ : Fin n => 0) tail.flatL)
        (higham11_2_blockOneD (A 0 0) tail.flatD) I J <=
          40 * (n + 1 : Nat) * M
      exact higham11_4_blockOne_absProduct_global_budget
        (fun _ : Fin n => 0) tail.flatL (A 0 0) tail.flatD M hM
        ((higham11_4_entry_le_roundedActiveMax A 0 0).trans hcur)
        (fun i => by simpa using hM)
        (fun i j => by
          rw [higham11_2_blockOne_absProduct_ss']
          simp only [abs_zero, zero_mul, zero_add]
          calc
            tail.flatAbsProduct i j <=
                40 * (n : Real) * tail.roundedStageMax := ih i j
            _ <= 40 * (n : Real) * M :=
              mul_le_mul_of_nonneg_left htailM (by positivity)
            _ <= 8 * M + 40 * (n : Real) * M := by linarith)
        I J
  | n + 2, _, .case1 A hA hbranch tail => by
      intro hcompleted I J
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      let W : Fin (n + 1) -> Real := fun k =>
        higham11_2_bunchKaufmanFlMultOne fp A (tau k)
      let whole := Higham11RoundedBunchKaufmanExecution.case1
        A hA hbranch tail
      let M := whole.roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg whole
      have hcur : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax whole
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_case1 A hA hbranch tail
      have hpivot := roundedActive_pivot_ne_zero_case1 A hbranch
      have ih := flatAbsProduct_le_forty_mul_dimension_mul_roundedStageMax_aux
        hval9 hsmall9 huSmall hu tail hcompleted
      change higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockOneL W tail.flatL)
        (higham11_2_blockOneD (B 0 0) tail.flatD) I J <=
          40 * (n + 2 : Nat) * M
      exact higham11_4_blockOne_absProduct_global_budget
        W tail.flatL (B 0 0) tail.flatD M hM
        ((higham11_4_roundedActive_entry_le_currentMax A 0 0).trans hcur)
        (fun k => by
          have hlocal := higham11_4_scalar_pivot_cross_le_two
            fp A hA hpivot hu (tau k)
          simpa [B, W] using (hlocal.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))))
        (fun i j => by
          rw [higham11_2_blockOne_absProduct_ss']
          have hp := higham11_4_pivotPathOneAbs_le_eight_case1
            fp A hbranch (tau i) (tau j) hu
          have hpM :
              higham11_2_bunchKaufmanPivotPathOneAbs fp A (tau i) (tau j) <=
                8 * M := hp.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))
          have hcoef : 0 <= (40 : Real) * ((n + 1 : Nat) : Real) :=
            mul_nonneg (by norm_num) (Nat.cast_nonneg (n + 1))
          have iht : tail.flatAbsProduct i j <=
              40 * ((n + 1 : Nat) : Real) * M :=
            (ih i j).trans
              (mul_le_mul_of_nonneg_left htailM hcoef)
          exact add_le_add (by simpa [B, W, tau] using hpM) iht)
        I J
  | n + 2, _, .case2 A hA hbranch tail => by
      intro hcompleted I J
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      let W : Fin (n + 1) -> Real := fun k =>
        higham11_2_bunchKaufmanFlMultOne fp A (tau k)
      let whole := Higham11RoundedBunchKaufmanExecution.case2
        A hA hbranch tail
      let M := whole.roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg whole
      have hcur : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax whole
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_case2 A hA hbranch tail
      have hpivot := roundedActive_pivot_ne_zero_case2 A hbranch
      have ih := flatAbsProduct_le_forty_mul_dimension_mul_roundedStageMax_aux
        hval9 hsmall9 huSmall hu tail hcompleted
      change higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockOneL W tail.flatL)
        (higham11_2_blockOneD (B 0 0) tail.flatD) I J <=
          40 * (n + 2 : Nat) * M
      exact higham11_4_blockOne_absProduct_global_budget
        W tail.flatL (B 0 0) tail.flatD M hM
        ((higham11_4_roundedActive_entry_le_currentMax A 0 0).trans hcur)
        (fun k => by
          have hlocal := higham11_4_scalar_pivot_cross_le_two
            fp A hA hpivot hu (tau k)
          simpa [B, W] using (hlocal.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))))
        (fun i j => by
          rw [higham11_2_blockOne_absProduct_ss']
          have hp := higham11_4_pivotPathOneAbs_le_eight_case2
            fp A hbranch (tau i) (tau j) hu
          have hpM :
              higham11_2_bunchKaufmanPivotPathOneAbs fp A (tau i) (tau j) <=
                8 * M := hp.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))
          have hcoef : 0 <= (40 : Real) * ((n + 1 : Nat) : Real) :=
            mul_nonneg (by norm_num) (Nat.cast_nonneg (n + 1))
          have iht : tail.flatAbsProduct i j <=
              40 * ((n + 1 : Nat) : Real) * M :=
            (ih i j).trans
              (mul_le_mul_of_nonneg_left htailM hcoef)
          exact add_le_add (by simpa [B, W, tau] using hpM) iht)
        I J
  | n + 2, _, .case3 A hA hbranch tail => by
      intro hcompleted I J
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      let W : Fin (n + 1) -> Real := fun k =>
        higham11_2_bunchKaufmanFlMultOne fp A (tau k)
      let whole := Higham11RoundedBunchKaufmanExecution.case3
        A hA hbranch tail
      let M := whole.roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg whole
      have hcur : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax whole
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_case3 A hA hbranch tail
      have hpivot := roundedActive_pivot_ne_zero_case3 A hA hbranch
      have ih := flatAbsProduct_le_forty_mul_dimension_mul_roundedStageMax_aux
        hval9 hsmall9 huSmall hu tail hcompleted
      change higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockOneL W tail.flatL)
        (higham11_2_blockOneD (B 0 0) tail.flatD) I J <=
          40 * (n + 2 : Nat) * M
      exact higham11_4_blockOne_absProduct_global_budget
        W tail.flatL (B 0 0) tail.flatD M hM
        ((higham11_4_roundedActive_entry_le_currentMax A 0 0).trans hcur)
        (fun k => by
          have hlocal := higham11_4_scalar_pivot_cross_le_two
            fp A hA hpivot hu (tau k)
          simpa [B, W] using (hlocal.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))))
        (fun i j => by
          rw [higham11_2_blockOne_absProduct_ss']
          have hp := higham11_4_pivotPathOneAbs_le_eight_case3
            fp A hA hbranch (tau i) (tau j) hu
          have hpM :
              higham11_2_bunchKaufmanPivotPathOneAbs fp A (tau i) (tau j) <=
                8 * M := hp.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))
          have hcoef : 0 <= (40 : Real) * ((n + 1 : Nat) : Real) :=
            mul_nonneg (by norm_num) (Nat.cast_nonneg (n + 1))
          have iht : tail.flatAbsProduct i j <=
              40 * ((n + 1 : Nat) : Real) * M :=
            (ih i j).trans
              (mul_le_mul_of_nonneg_left htailM hcoef)
          exact add_le_add (by simpa [B, W, tau] using hpM) iht)
        I J
  | n + 2, _, .case4 A hA hbranch hsecond tail => by
      intro hcompleted I J
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      let W : Fin n -> Fin 2 -> Real := fun k p =>
        higham11_2_bunchKaufmanFlMultTwo fp A (tau k) p
      let E : Fin 2 -> Fin 2 -> Real := fun p q =>
        B (embedTwo n p) (embedTwo n q)
      let whole := Higham11RoundedBunchKaufmanExecution.case4
        A hA hbranch hsecond tail
      let M := whole.roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg whole
      have hcur : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax whole
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_case4 A hA hbranch hsecond tail
      have ih := flatAbsProduct_le_forty_mul_dimension_mul_roundedStageMax_aux
        hval9 hsmall9 huSmall hu tail hcompleted
      change higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W tail.flatL)
        (higham11_2_blockTwoD E tail.flatD) I J <=
          40 * (n + 2 : Nat) * M
      exact higham11_4_blockTwo_absProduct_global_budget
        W tail.flatL E tail.flatD M hM
        (by
          rw [higham11_4_blockTwo_absProduct_00]
          exact (higham11_4_roundedActive_entry_le_currentMax A 0 0).trans hcur)
        (by
          rw [higham11_4_blockTwo_absProduct_01]
          exact (higham11_4_roundedActive_entry_le_currentMax A 0 1).trans hcur)
        (by
          rw [higham11_4_blockTwo_absProduct_10]
          exact (higham11_4_roundedActive_entry_le_currentMax A 1 0).trans hcur)
        (by
          rw [higham11_4_blockTwo_absProduct_11]
          exact (higham11_4_roundedActive_entry_le_currentMax A 1 1).trans hcur)
        (fun j => by
          rw [higham11_2_blockTwo_absProduct_0t']
          have hlocal := higham11_4_pivotRowTwoAbs_le_six_case4
            fp hval9 hsmall9 A hA hbranch hsecond huSmall 0 (tau j)
          simpa [B, W, E, tau,
            higham11_2_bunchKaufmanPivotRowTwoAbs, Fin.sum_univ_two] using (hlocal.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))))
        (fun j => by
          rw [higham11_2_blockTwo_absProduct_1t']
          have hlocal := higham11_4_pivotRowTwoAbs_le_six_case4
            fp hval9 hsmall9 A hA hbranch hsecond huSmall 1 (tau j)
          simpa [B, W, E, tau,
            higham11_2_bunchKaufmanPivotRowTwoAbs, Fin.sum_univ_two] using (hlocal.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))))
        (fun i => by
          rw [higham11_2_blockTwo_absProduct_t0']
          have hlocal := higham11_4_pivotColTwoAbs_le_six_case4
            fp hval9 hsmall9 A hA hbranch hsecond huSmall (tau i) 0
          simpa [B, W, E, tau,
            higham11_2_bunchKaufmanPivotColTwoAbs, Fin.sum_univ_two] using (hlocal.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))))
        (fun i => by
          rw [higham11_2_blockTwo_absProduct_t1']
          have hlocal := higham11_4_pivotColTwoAbs_le_six_case4
            fp hval9 hsmall9 A hA hbranch hsecond huSmall (tau i) 1
          simpa [B, W, E, tau,
            higham11_2_bunchKaufmanPivotColTwoAbs, Fin.sum_univ_two] using (hlocal.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))))
        (fun i j => by
          rw [higham11_2_blockTwo_absProduct_tt']
          have hp := higham11_4_pivotPathTwoAbs_le_thirtyThree_case4
            fp hval9 hsmall9 A hA hbranch hsecond huSmall (tau i) (tau j)
          have hpM :
              higham11_2_bunchKaufmanPivotPathTwoAbs fp A (tau i) (tau j) <=
                33 * M := hp.trans
            (mul_le_mul_of_nonneg_left hcur (by norm_num))
          have iht : tail.flatAbsProduct i j <= 40 * (n : Real) * M :=
            (ih i j).trans
              (mul_le_mul_of_nonneg_left htailM (by positivity))
          exact add_le_add (by simpa [B, W, E, tau] using hpM) iht)
        I J
  | _, _, .case4Breakdown A hA hbranch hsecond => by
      intro hcompleted
      exact False.elim hcompleted

/-- Actual finite-precision growth of the assembled computed factors.  The
constant `40` includes the explicit finite-`u` correction; the exact source
constant `36` is deliberately not asserted for the hatted factors. -/
theorem flatAbsProduct_le_forty_mul_dimension_mul_roundedStageMax
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000) {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (i j : Fin n) :
    exec.flatAbsProduct i j <= 40 * (n : Real) * exec.roundedStageMax := by
  have hu : fp.u <= 1 := by nlinarith [fp.u_nonneg]
  exact flatAbsProduct_le_forty_mul_dimension_mul_roundedStageMax_aux
    hval9 hsmall9 huSmall hu exec hcompleted i j

/-- The source element-growth factor of the literal rounded path, for a
nonzero input scale. -/
noncomputable def roundedGrowthFactor {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) (Amax : Real) : Real :=
  exec.roundedStageMax / Amax

theorem roundedStageMax_eq_growthFactor_mul {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    {Amax : Real} (hAmax : 0 < Amax) :
    exec.roundedStageMax = exec.roundedGrowthFactor Amax * Amax := by
  simp [roundedGrowthFactor, ne_of_gt hAmax]

end Higham11RoundedBunchKaufmanExecution

end NumStability
