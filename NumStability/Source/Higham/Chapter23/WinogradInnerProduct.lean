/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.DotProduct

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 23: Winograd inner products

Winograd's paired inner-product identity and its rounded error bounds from Higham, Chapter 23.
-/

section WinogradInnerProduct

/-- Equation (23.2), written as `m` independent adjacent pairs. -/
theorem higham23_eq23_2_winograd_identity {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ) :
    ∑ i : Fin m,
        ((xOdd i + yEven i) * (xEven i + yOdd i) -
          xOdd i * xEven i - yOdd i * yEven i) =
      ∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i) := by
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The literal rounded Winograd inner-product path: form two rounded pair
sums, accumulate the three rounded dot products, and perform the two printed
subtractions. -/
noncomputable def higham23FlWinogradInnerProduct (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ) : ℝ :=
  let p := fl_dotProduct fp m
    (fun i ↦ fp.fl_add (xOdd i) (yEven i))
    (fun i ↦ fp.fl_add (xEven i) (yOdd i))
  let q := fl_dotProduct fp m xOdd xEven
  let r := fl_dotProduct fp m yOdd yEven
  fp.fl_sub (fp.fl_sub p q) r

/-- Source-shaped analogue of (3.3) used in Theorem 23.1: every term of the
actual computed path has one relative factor bounded by `gamma_(m+4)`. -/
theorem higham23_winograd_factor_expansion (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ)
    (hvalid : gammaValid fp (m + 4)) :
    ∃ ε α β : Fin m → ℝ,
      (∀ i, |ε i| ≤ gamma fp (m + 4)) ∧
      (∀ i, |α i| ≤ gamma fp (m + 4)) ∧
      (∀ i, |β i| ≤ gamma fp (m + 4)) ∧
      higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven =
        (∑ i : Fin m,
          (xOdd i + yEven i) * (xEven i + yOdd i) * (1 + ε i)) -
        (∑ i : Fin m, xOdd i * xEven i * (1 + α i)) -
        (∑ i : Fin m, yOdd i * yEven i * (1 + β i)) := by
  let sx : Fin m → ℝ := fun i ↦ fp.fl_add (xOdd i) (yEven i)
  let sy : Fin m → ℝ := fun i ↦ fp.fl_add (xEven i) (yOdd i)
  let p := fl_dotProduct fp m sx sy
  let q := fl_dotProduct fp m xOdd xEven
  let r := fl_dotProduct fp m yOdd yEven
  let δx : Fin m → ℝ := fun i ↦
    Classical.choose (fp.model_add (xOdd i) (yEven i))
  let δy : Fin m → ℝ := fun i ↦
    Classical.choose (fp.model_add (xEven i) (yOdd i))
  have hδx : ∀ i, |δx i| ≤ fp.u ∧
      sx i = (xOdd i + yEven i) * (1 + δx i) := by
    intro i
    exact Classical.choose_spec (fp.model_add (xOdd i) (yEven i))
  have hδy : ∀ i, |δy i| ≤ fp.u ∧
      sy i = (xEven i + yOdd i) * (1 + δy i) := by
    intro i
    exact Classical.choose_spec (fp.model_add (xEven i) (yOdd i))
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hvalid
  obtain ⟨ηp, hηp, hp⟩ := dotProduct_backward_error fp m sx sy hm
  obtain ⟨ηq, hηq, hq⟩ := dotProduct_backward_error fp m xOdd xEven hm
  obtain ⟨ηr, hηr, hr⟩ := dotProduct_backward_error fp m yOdd yEven hm
  change p = _ at hp
  change q = _ at hq
  change r = _ at hr
  let δ1 := Classical.choose (fp.model_sub p q)
  have hδ1 : |δ1| ≤ fp.u ∧ fp.fl_sub p q = (p - q) * (1 + δ1) :=
    Classical.choose_spec (fp.model_sub p q)
  let δ2 := Classical.choose (fp.model_sub (fp.fl_sub p q) r)
  have hδ2 : |δ2| ≤ fp.u ∧
      fp.fl_sub (fp.fl_sub p q) r = (fp.fl_sub p q - r) * (1 + δ2) :=
    Classical.choose_spec (fp.model_sub (fp.fl_sub p q) r)
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hvalid
  have hm2 : gammaValid fp (m + 2) := gammaValid_mono fp (by omega) hvalid
  have hm3 : gammaValid fp (m + 3) := gammaValid_mono fp (by omega) hvalid
  have hu1 : fp.u ≤ gamma fp 1 := u_le_gamma fp one_pos h1
  have hδx1 : ∀ i, |δx i| ≤ gamma fp 1 := fun i ↦ le_trans (hδx i).1 hu1
  have hδy1 : ∀ i, |δy i| ≤ gamma fp 1 := fun i ↦ le_trans (hδy i).1 hu1
  have hδ11 : |δ1| ≤ gamma fp 1 := le_trans hδ1.1 hu1
  have hδ21 : |δ2| ≤ gamma fp 1 := le_trans hδ2.1 hu1
  have hepsExists : ∀ i : Fin m, ∃ e : ℝ,
      |e| ≤ gamma fp (m + 4) ∧
      (1 + δx i) * (1 + δy i) * (1 + ηp i) * (1 + δ1) * (1 + δ2) =
        1 + e := by
    intro i
    obtain ⟨e2, he2, heq2⟩ :=
      gamma_mul fp 1 1 (δx i) (δy i) (hδx1 i) (hδy1 i) h2
    obtain ⟨em2, hem2, heqm2⟩ :=
      gamma_mul fp 2 m e2 (ηp i) he2 (hηp i) (by simpa [Nat.add_comm] using hm2)
    have hem2' : |em2| ≤ gamma fp (m + 2) := by
      simpa [Nat.add_comm] using hem2
    obtain ⟨em3, hem3, heqm3⟩ :=
      gamma_mul fp (m + 2) 1 em2 δ1 hem2' hδ11 (by simpa [Nat.add_assoc] using hm3)
    obtain ⟨em4, hem4, heqm4⟩ :=
      gamma_mul fp (m + 3) 1 em3 δ2 hem3 hδ21 (by simpa [Nat.add_assoc] using hvalid)
    refine ⟨em4, ?_, ?_⟩
    · simpa [Nat.add_assoc] using hem4
    · rw [← heqm4, ← heqm3, ← heqm2, ← heq2]
  choose ε hε hεeq using hepsExists
  have halphaExists : ∀ i : Fin m, ∃ a : ℝ,
      |a| ≤ gamma fp (m + 4) ∧
      (1 + ηq i) * (1 + δ1) * (1 + δ2) = 1 + a := by
    intro i
    obtain ⟨am1, ham1, heqam1⟩ :=
      gamma_mul fp m 1 (ηq i) δ1 (hηq i) hδ11
        (gammaValid_mono fp (by omega) hvalid)
    obtain ⟨am2, ham2, heqam2⟩ :=
      gamma_mul fp (m + 1) 1 am1 δ2 ham1 hδ21
        (gammaValid_mono fp (by omega) hvalid)
    refine ⟨am2, le_trans ham2 (gamma_mono fp (by omega) hvalid), ?_⟩
    rw [← heqam2, ← heqam1]
  choose α hα hαeq using halphaExists
  have hbetaExists : ∀ i : Fin m, ∃ b : ℝ,
      |b| ≤ gamma fp (m + 4) ∧
      (1 + ηr i) * (1 + δ2) = 1 + b := by
    intro i
    obtain ⟨bm1, hbm1, heqbm1⟩ :=
      gamma_mul fp m 1 (ηr i) δ2 (hηr i) hδ21
        (gammaValid_mono fp (by omega) hvalid)
    exact ⟨bm1, le_trans hbm1 (gamma_mono fp (by omega) hvalid), heqbm1⟩
  choose β hβ hβeq using hbetaExists
  refine ⟨ε, α, β, hε, hα, hβ, ?_⟩
  simp only [higham23FlWinogradInnerProduct]
  change fp.fl_sub (fp.fl_sub p q) r = _
  rw [hδ2.2, hδ1.2, hp, hq, hr]
  have hP :
      (∑ i : Fin m, sx i * sy i * (1 + ηp i)) * (1 + δ1) * (1 + δ2) =
        ∑ i : Fin m,
          (xOdd i + yEven i) * (xEven i + yOdd i) * (1 + ε i) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hδx i).2, (hδy i).2]
    calc
      (xOdd i + yEven i) * (1 + δx i) *
          ((xEven i + yOdd i) * (1 + δy i)) * (1 + ηp i) *
          (1 + δ1) * (1 + δ2) =
        (xOdd i + yEven i) * (xEven i + yOdd i) *
          ((1 + δx i) * (1 + δy i) * (1 + ηp i) *
            (1 + δ1) * (1 + δ2)) := by ring
      _ = _ := by rw [hεeq i]
  have hQ :
      (∑ i : Fin m, xOdd i * xEven i * (1 + ηq i)) * (1 + δ1) * (1 + δ2) =
        ∑ i : Fin m, xOdd i * xEven i * (1 + α i) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      xOdd i * xEven i * (1 + ηq i) * (1 + δ1) * (1 + δ2) =
        xOdd i * xEven i * ((1 + ηq i) * (1 + δ1) * (1 + δ2)) := by ring
      _ = _ := by rw [hαeq i]
  have hR :
      (∑ i : Fin m, yOdd i * yEven i * (1 + ηr i)) * (1 + δ2) =
        ∑ i : Fin m, yOdd i * yEven i * (1 + β i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      yOdd i * yEven i * (1 + ηr i) * (1 + δ2) =
        yOdd i * yEven i * ((1 + ηr i) * (1 + δ2)) := by ring
      _ = _ := by rw [hβeq i]
  calc
    (((∑ i : Fin m, sx i * sy i * (1 + ηp i)) -
        ∑ i : Fin m, xOdd i * xEven i * (1 + ηq i)) * (1 + δ1) -
        ∑ i : Fin m, yOdd i * yEven i * (1 + ηr i)) * (1 + δ2) =
      (∑ i : Fin m, sx i * sy i * (1 + ηp i)) * (1 + δ1) * (1 + δ2) -
        (∑ i : Fin m, xOdd i * xEven i * (1 + ηq i)) * (1 + δ1) * (1 + δ2) -
        (∑ i : Fin m, yOdd i * yEven i * (1 + ηr i)) * (1 + δ2) := by ring
    _ = _ := by rw [hP, hQ, hR]

/-- Theorem 23.1 / equation (23.12), for an even vector length `n = 2m`.
`X` and `Y` are source-facing infinity-norm upper bounds for the odd/even
halves of the two vectors. -/
theorem higham23_theorem23_1_winograd_error (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ) (X Y : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hxOdd : ∀ i, |xOdd i| ≤ X) (hxEven : ∀ i, |xEven i| ≤ X)
    (hyOdd : ∀ i, |yOdd i| ≤ Y) (hyEven : ∀ i, |yEven i| ≤ Y)
    (hvalid : gammaValid fp (m + 4)) :
    |(∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
        higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven| ≤
      ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) * (X + Y) ^ 2 := by
  obtain ⟨ε, α, β, hε, hα, hβ, hfl⟩ :=
    higham23_winograd_factor_expansion fp xOdd xEven yOdd yEven hvalid
  let P : Fin m → ℝ := fun i ↦ (xOdd i + yEven i) * (xEven i + yOdd i)
  let Q : Fin m → ℝ := fun i ↦ xOdd i * xEven i
  let R : Fin m → ℝ := fun i ↦ yOdd i * yEven i
  have hid := higham23_eq23_2_winograd_identity xOdd xEven yOdd yEven
  change (∑ i : Fin m, (P i - Q i - R i)) = _ at hid
  have hPe : (∑ i : Fin m, P i * (1 + ε i)) =
      (∑ i : Fin m, P i) + ∑ i : Fin m, P i * ε i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hQa : (∑ i : Fin m, Q i * (1 + α i)) =
      (∑ i : Fin m, Q i) + ∑ i : Fin m, Q i * α i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hRb : (∑ i : Fin m, R i * (1 + β i)) =
      (∑ i : Fin m, R i) + ∑ i : Fin m, R i * β i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hplain : (∑ i : Fin m, (P i - Q i - R i)) =
      (∑ i : Fin m, P i) - (∑ i : Fin m, Q i) - (∑ i : Fin m, R i) := by
    simp only [Finset.sum_sub_distrib]
  have hNeg : (∑ i : Fin m, -P i * ε i) = -(∑ i : Fin m, P i * ε i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have herr :
      (∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
          higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven =
        ∑ i : Fin m, (-P i * ε i + Q i * α i + R i * β i) := by
    rw [← hid, hplain, hfl, hPe, hQa, hRb]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hNeg]
    ring
  rw [herr]
  have hG : 0 ≤ gamma fp (m + 4) := gamma_nonneg fp hvalid
  have hXY : 0 ≤ X + Y := add_nonneg hX hY
  calc
    |∑ i : Fin m, (-P i * ε i + Q i * α i + R i * β i)| ≤
        ∑ i : Fin m, |(-P i * ε i + Q i * α i + R i * β i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, gamma fp (m + 4) * (2 * (X + Y) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hP1 : |xOdd i + yEven i| ≤ X + Y :=
        le_trans (abs_add_le _ _) (add_le_add (hxOdd i) (hyEven i))
      have hP2 : |xEven i + yOdd i| ≤ X + Y :=
        le_trans (abs_add_le _ _) (add_le_add (hxEven i) (hyOdd i))
      have hPbound : |P i| ≤ (X + Y) ^ 2 := by
        rw [show P i = (xOdd i + yEven i) * (xEven i + yOdd i) from rfl,
          abs_mul, pow_two]
        exact mul_le_mul hP1 hP2 (abs_nonneg _) hXY
      have hQbound : |Q i| ≤ X ^ 2 := by
        rw [show Q i = xOdd i * xEven i from rfl, abs_mul, pow_two]
        exact mul_le_mul (hxOdd i) (hxEven i) (abs_nonneg _) hX
      have hRbound : |R i| ≤ Y ^ 2 := by
        rw [show R i = yOdd i * yEven i from rfl, abs_mul, pow_two]
        exact mul_le_mul (hyOdd i) (hyEven i) (abs_nonneg _) hY
      calc
        |(-P i * ε i + Q i * α i + R i * β i)| ≤
            |P i| * |ε i| + |Q i| * |α i| + |R i| * |β i| := by
          calc
            |(-P i * ε i + Q i * α i + R i * β i)| ≤
                |(-P i * ε i + Q i * α i)| + |R i * β i| := abs_add_le _ _
            _ ≤ (|-P i * ε i| + |Q i * α i|) + |R i * β i| := by
              linarith [abs_add_le (-P i * ε i) (Q i * α i)]
            _ = _ := by simp only [abs_mul, abs_neg]
        _ ≤ |P i| * gamma fp (m + 4) +
              |Q i| * gamma fp (m + 4) + |R i| * gamma fp (m + 4) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (hε i) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (hα i) (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left (hβ i) (abs_nonneg _))
        _ = gamma fp (m + 4) * (|P i| + |Q i| + |R i|) := by ring
        _ ≤ gamma fp (m + 4) * ((X + Y) ^ 2 + X ^ 2 + Y ^ 2) := by
          gcongr
        _ ≤ gamma fp (m + 4) * (2 * (X + Y) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hG
          nlinarith [mul_nonneg hX hY]
    _ = ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) * (X + Y) ^ 2 := by
      simp
      ring

/-- Componentwise form retained before replacing every input by its infinity
norm.  This is the exact-gamma form used again for the 3M bound (23.22). -/
theorem higham23_winograd_componentwise_error (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ)
    (hvalid : gammaValid fp (m + 4)) :
    |(∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
        higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven| ≤
      gamma fp (m + 4) *
        ∑ i : Fin m,
          (|xOdd i + yEven i| * |xEven i + yOdd i| +
            |xOdd i| * |xEven i| + |yOdd i| * |yEven i|) := by
  obtain ⟨ε, α, β, hε, hα, hβ, hfl⟩ :=
    higham23_winograd_factor_expansion fp xOdd xEven yOdd yEven hvalid
  let P : Fin m → ℝ := fun i ↦ (xOdd i + yEven i) * (xEven i + yOdd i)
  let Q : Fin m → ℝ := fun i ↦ xOdd i * xEven i
  let R : Fin m → ℝ := fun i ↦ yOdd i * yEven i
  have hid := higham23_eq23_2_winograd_identity xOdd xEven yOdd yEven
  change (∑ i : Fin m, (P i - Q i - R i)) = _ at hid
  have hPe : (∑ i : Fin m, P i * (1 + ε i)) =
      (∑ i : Fin m, P i) + ∑ i : Fin m, P i * ε i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hQa : (∑ i : Fin m, Q i * (1 + α i)) =
      (∑ i : Fin m, Q i) + ∑ i : Fin m, Q i * α i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hRb : (∑ i : Fin m, R i * (1 + β i)) =
      (∑ i : Fin m, R i) + ∑ i : Fin m, R i * β i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hplain : (∑ i : Fin m, (P i - Q i - R i)) =
      (∑ i : Fin m, P i) - (∑ i : Fin m, Q i) - (∑ i : Fin m, R i) := by
    simp only [Finset.sum_sub_distrib]
  have hNeg : (∑ i : Fin m, -P i * ε i) = -(∑ i : Fin m, P i * ε i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have herr :
      (∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
          higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven =
        ∑ i : Fin m, (-P i * ε i + Q i * α i + R i * β i) := by
    rw [← hid, hplain, hfl, hPe, hQa, hRb]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hNeg]
    ring
  rw [herr]
  calc
    |∑ i : Fin m, (-P i * ε i + Q i * α i + R i * β i)| ≤
        ∑ i : Fin m, |(-P i * ε i + Q i * α i + R i * β i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m,
        gamma fp (m + 4) * (|P i| + |Q i| + |R i|) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |(-P i * ε i + Q i * α i + R i * β i)| ≤
            |P i| * |ε i| + |Q i| * |α i| + |R i| * |β i| := by
          calc
            |(-P i * ε i + Q i * α i + R i * β i)| ≤
                |(-P i * ε i + Q i * α i)| + |R i * β i| := abs_add_le _ _
            _ ≤ (|-P i * ε i| + |Q i * α i|) + |R i * β i| := by
              linarith [abs_add_le (-P i * ε i) (Q i * α i)]
            _ = _ := by simp only [abs_mul, abs_neg]
        _ ≤ |P i| * gamma fp (m + 4) +
              |Q i| * gamma fp (m + 4) + |R i| * gamma fp (m + 4) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (hε i) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (hα i) (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left (hβ i) (abs_nonneg _))
        _ = _ := by ring
    _ = gamma fp (m + 4) *
        ∑ i : Fin m,
          (|xOdd i + yEven i| * |xEven i + yOdd i| +
            |xOdd i| * |xEven i| + |yOdd i| * |yEven i|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [P, Q, R, abs_mul]

end WinogradInnerProduct

end NumStability
