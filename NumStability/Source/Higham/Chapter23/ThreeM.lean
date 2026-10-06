/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Tactic.NoncommRing
import NumStability.Analysis.Norms
import NumStability.Source.Higham.Chapter23.GammaAsymptotics
import NumStability.Source.Higham.Chapter23.WinogradInnerProduct

namespace NumStability

open scoped BigOperators Topology
open Filter

/-!
# Higham Chapter 23: Three-multiplication complex arithmetic

The 3M complex product, rounded evaluator, and Chapter 23 error bounds.
-/

section ThreeM

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- Equations (23.8)--(23.9): the 3M method returns the real and imaginary
parts using three multiplications in `R`. -/
def higham23ThreeM (a1 a2 b1 b2 : R) : R × R :=
  let t1 := a1 * b1
  let t2 := a2 * b2
  (t1 - t2, (a1 + a2) * (b1 + b2) - t1 - t2)

/-- Exact correctness of the 3M identity; the proof does not use
commutativity, so it applies to real matrix blocks. -/
theorem higham23_eq23_9_threeM_correct (a1 a2 b1 b2 : R) :
    higham23ThreeM a1 a2 b1 b2 =
      (a1 * b1 - a2 * b2, a1 * b2 + a2 * b1) := by
  simp [higham23ThreeM]
  noncomm_ring

inductive Higham23TwoDotMode
  | add
  | sub

namespace Higham23TwoDotMode

def sign : Higham23TwoDotMode → ℝ
  | add => 1
  | sub => -1

def rounded (fp : FPModel) : Higham23TwoDotMode → ℝ → ℝ → ℝ
  | add => fp.fl_add
  | sub => fp.fl_sub

theorem model (fp : FPModel) (mode : Higham23TwoDotMode) (x y : ℝ) :
    ∃ δ : ℝ, |δ| ≤ fp.u ∧
      mode.rounded fp x y = (x + mode.sign * y) * (1 + δ) := by
  cases mode with
  | add =>
      obtain ⟨δ, hδ, heq⟩ := fp.model_add x y
      exact ⟨δ, hδ, by simpa [rounded, sign] using heq⟩
  | sub =>
      obtain ⟨δ, hδ, heq⟩ := fp.model_sub x y
      exact ⟨δ, hδ, by simpa [rounded, sign] using heq⟩

end Higham23TwoDotMode

/-- Actual conventional two-dot evaluation used by both the real and
imaginary parts of ordinary complex matrix multiplication. -/
noncomputable def higham23FlTwoDot (fp : FPModel) {n : ℕ}
    (mode : Higham23TwoDotMode)
    (a b c d : Fin n → ℝ) : ℝ :=
  mode.rounded fp (fl_dotProduct fp n a b) (fl_dotProduct fp n c d)

/-- Common exact-gamma bound for a rounded addition or subtraction of two
actual rounded dot products. -/
theorem higham23_flTwoDot_error (fp : FPModel) {n : ℕ}
    (mode : Higham23TwoDotMode) (a b c d : Fin n → ℝ)
    (hvalid : gammaValid fp (n + 1)) :
    |((∑ k : Fin n, a k * b k) +
        mode.sign * (∑ k : Fin n, c k * d k)) -
        higham23FlTwoDot fp mode a b c d| ≤
      gamma fp (n + 1) *
        ∑ k : Fin n, (|a k| * |b k| + |c k| * |d k|) := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hvalid
  obtain ⟨ηp, hηp, hp⟩ := dotProduct_backward_error fp n a b hn
  obtain ⟨ηq, hηq, hq⟩ := dotProduct_backward_error fp n c d hn
  let p := fl_dotProduct fp n a b
  let q := fl_dotProduct fp n c d
  change p = _ at hp
  change q = _ at hq
  obtain ⟨δ, hδ, hrounded⟩ := mode.model fp p q
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have hδ1 : |δ| ≤ gamma fp 1 :=
    le_trans hδ (u_le_gamma fp one_pos h1)
  have hαExists : ∀ i : Fin n, ∃ α : ℝ,
      |α| ≤ gamma fp (n + 1) ∧ (1 + ηp i) * (1 + δ) = 1 + α := by
    intro i
    exact gamma_mul fp n 1 (ηp i) δ (hηp i) hδ1 hvalid
  choose α hα hαeq using hαExists
  have hβExists : ∀ i : Fin n, ∃ β : ℝ,
      |β| ≤ gamma fp (n + 1) ∧ (1 + ηq i) * (1 + δ) = 1 + β := by
    intro i
    exact gamma_mul fp n 1 (ηq i) δ (hηq i) hδ1 hvalid
  choose β hβ hβeq using hβExists
  have hPfactor :
      (∑ i : Fin n, a i * b i * (1 + ηp i)) * (1 + δ) =
        ∑ i : Fin n, a i * b i * (1 + α i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      a i * b i * (1 + ηp i) * (1 + δ) =
          a i * b i * ((1 + ηp i) * (1 + δ)) := by ring
      _ = _ := by rw [hαeq i]
  have hQfactor :
      (∑ i : Fin n, c i * d i * (1 + ηq i)) * (1 + δ) =
        ∑ i : Fin n, c i * d i * (1 + β i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      c i * d i * (1 + ηq i) * (1 + δ) =
          c i * d i * ((1 + ηq i) * (1 + δ)) := by ring
      _ = _ := by rw [hβeq i]
  have hcomputed : higham23FlTwoDot fp mode a b c d =
      (∑ i : Fin n, a i * b i * (1 + α i)) +
        mode.sign * (∑ i : Fin n, c i * d i * (1 + β i)) := by
    simp only [higham23FlTwoDot]
    change mode.rounded fp p q = _
    rw [hrounded, hp, hq, add_mul, hPfactor]
    calc
      (∑ i : Fin n, a i * b i * (1 + α i)) +
          (mode.sign * (∑ i : Fin n, c i * d i * (1 + ηq i))) * (1 + δ) =
        (∑ i : Fin n, a i * b i * (1 + α i)) +
          mode.sign * ((∑ i : Fin n, c i * d i * (1 + ηq i)) * (1 + δ)) := by ring
      _ = _ := by rw [hQfactor]
  rw [hcomputed]
  have hA : (∑ i : Fin n, a i * b i * (1 + α i)) =
      (∑ i : Fin n, a i * b i) + ∑ i : Fin n, a i * b i * α i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hB : (∑ i : Fin n, c i * d i * (1 + β i)) =
      (∑ i : Fin n, c i * d i) + ∑ i : Fin n, c i * d i * β i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hA, hB]
  have herr :
      (∑ i : Fin n, a i * b i) + mode.sign * (∑ i : Fin n, c i * d i) -
          ((∑ i : Fin n, a i * b i) + (∑ i : Fin n, a i * b i * α i) +
            mode.sign * ((∑ i : Fin n, c i * d i) +
              ∑ i : Fin n, c i * d i * β i)) =
        -(∑ i : Fin n, a i * b i * α i) -
          mode.sign * (∑ i : Fin n, c i * d i * β i) := by ring
  rw [herr]
  calc
    |-(∑ i : Fin n, a i * b i * α i) -
        mode.sign * (∑ i : Fin n, c i * d i * β i)| ≤
      |∑ i : Fin n, a i * b i * α i| +
        |mode.sign| * |∑ i : Fin n, c i * d i * β i| := by
      calc
        |-(∑ i : Fin n, a i * b i * α i) -
            mode.sign * (∑ i : Fin n, c i * d i * β i)| ≤
          |-(∑ i : Fin n, a i * b i * α i)| +
            |mode.sign * (∑ i : Fin n, c i * d i * β i)| := by
              simpa [sub_eq_add_neg] using
                abs_add_le (-(∑ i : Fin n, a i * b i * α i))
                  (-(mode.sign * (∑ i : Fin n, c i * d i * β i)))
        _ = _ := by simp only [abs_neg, abs_mul]
    _ = |∑ i : Fin n, a i * b i * α i| +
        |∑ i : Fin n, c i * d i * β i| := by
      cases mode <;> simp [Higham23TwoDotMode.sign]
    _ ≤ (∑ i : Fin n, |a i| * |b i| * |α i|) +
        ∑ i : Fin n, |c i| * |d i| * |β i| := by
      apply add_le_add
      · calc
          |∑ i : Fin n, a i * b i * α i| ≤
              ∑ i : Fin n, |a i * b i * α i| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp only [abs_mul]
      · calc
          |∑ i : Fin n, c i * d i * β i| ≤
              ∑ i : Fin n, |c i * d i * β i| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp only [abs_mul]
    _ ≤ (∑ i : Fin n, |a i| * |b i| * gamma fp (n + 1)) +
        ∑ i : Fin n, |c i| * |d i| * gamma fp (n + 1) := by
      apply add_le_add <;> apply Finset.sum_le_sum <;> intro i _
      · simpa only [abs_mul] using
          mul_le_mul_of_nonneg_left (hα i)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · simpa only [abs_mul] using
          mul_le_mul_of_nonneg_left (hβ i)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = gamma fp (n + 1) *
        ∑ i : Fin n, (|a i| * |b i| + |c i| * |d i|) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Actual conventional real part `A1*B1 - A2*B2`. -/
noncomputable def higham23FlConventionalReal (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) : ℝ :=
  higham23FlTwoDot fp .sub A1 B1 A2 B2

/-- Equation (23.20), exact-gamma form. -/
theorem higham23_eq23_20_conventional_real_error (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 1)) :
    |(∑ k : Fin n, (A1 k * B1 k - A2 k * B2 k)) -
        higham23FlConventionalReal fp A1 A2 B1 B2| ≤
      gamma fp (n + 1) *
        ∑ k : Fin n, (|A1 k| * |B1 k| + |A2 k| * |B2 k|) := by
  simpa [higham23FlConventionalReal, Higham23TwoDotMode.sign,
    Finset.sum_sub_distrib] using
    higham23_flTwoDot_error fp .sub A1 B1 A2 B2 hvalid

/-- Equation (23.20) with its first-order term and explicit `O(u²)`
remainder separated. -/
theorem higham23_eq23_20_conventional_real_firstOrder (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 1)) :
    |(∑ k : Fin n, (A1 k * B1 k - A2 k * B2 k)) -
        higham23FlConventionalReal fp A1 A2 B1 B2| ≤
      ((n + 1 : ℕ) : ℝ) * fp.u *
          (∑ k : Fin n, (|A1 k| * |B1 k| + |A2 k| * |B2 k|)) +
        higham23GammaRemainder (n + 1) fp.u *
          (∑ k : Fin n, (|A1 k| * |B1 k| + |A2 k| * |B2 k|)) :=
  higham23_error_bound_gamma_split fp (n + 1) _ _ hvalid
    (higham23_eq23_20_conventional_real_error fp A1 A2 B1 B2 hvalid)

/-- Actual conventional imaginary part `A1*B2 + A2*B1`. -/
noncomputable def higham23FlConventionalImaginary (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) : ℝ :=
  higham23FlTwoDot fp .add A1 B2 A2 B1

/-- Equation (23.21), exact-gamma form. -/
theorem higham23_eq23_21_conventional_imaginary_error (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 1)) :
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlConventionalImaginary fp A1 A2 B1 B2| ≤
      gamma fp (n + 1) *
        ∑ k : Fin n, (|A1 k| * |B2 k| + |A2 k| * |B1 k|) := by
  simpa [higham23FlConventionalImaginary, Higham23TwoDotMode.sign,
    Finset.sum_add_distrib] using
    higham23_flTwoDot_error fp .add A1 B2 A2 B1 hvalid

/-- Equation (23.21) with explicit quadratic remainder. -/
theorem higham23_eq23_21_conventional_imaginary_firstOrder (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 1)) :
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlConventionalImaginary fp A1 A2 B1 B2| ≤
      ((n + 1 : ℕ) : ℝ) * fp.u *
          (∑ k : Fin n, (|A1 k| * |B2 k| + |A2 k| * |B1 k|)) +
        higham23GammaRemainder (n + 1) fp.u *
          (∑ k : Fin n, (|A1 k| * |B2 k| + |A2 k| * |B1 k|)) :=
  higham23_error_bound_gamma_split fp (n + 1) _ _ hvalid
    (higham23_eq23_21_conventional_imaginary_error fp A1 A2 B1 B2 hvalid)

/-- Actual rounded imaginary-part path of the 3M method for one matrix-product
entry.  It is the same arithmetic graph as the Winograd cancellation identity
after the indicated permutation of the four real input vectors. -/
noncomputable def higham23FlThreeMImaginary (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) : ℝ :=
  higham23FlWinogradInnerProduct fp A1 B1 B2 A2

/-- Exact-gamma version of equation (23.22) for one output entry of the actual
rounded 3M path.  Expanding `gamma_(n+4)` gives the printed first-order
coefficient `(n+4)u`. -/
theorem higham23_eq23_22_threeM_imaginary_error (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 4)) :
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlThreeMImaginary fp A1 A2 B1 B2| ≤
      gamma fp (n + 4) *
        ∑ k : Fin n,
          ((|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) +
            |A1 k| * |B1 k| + |A2 k| * |B2 k|) := by
  have hcore := higham23_winograd_componentwise_error fp A1 B1 B2 A2 hvalid
  change
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlWinogradInnerProduct fp A1 B1 B2 A2| ≤ _
  have hleft :
      (∑ k : Fin n, (A1 k * B2 k + B1 k * A2 k)) =
        ∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hleft] at hcore
  refine le_trans hcore ?_
  apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hvalid)
  apply Finset.sum_le_sum
  intro k _
  have hsumA : |A1 k + A2 k| ≤ |A1 k| + |A2 k| := abs_add_le _ _
  have hsumB : |B1 k + B2 k| ≤ |B1 k| + |B2 k| := abs_add_le _ _
  have hprod : |A1 k + A2 k| * |B1 k + B2 k| ≤
      (|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) :=
    mul_le_mul hsumA hsumB (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  nlinarith [abs_nonneg (A1 k), abs_nonneg (A2 k),
    abs_nonneg (B1 k), abs_nonneg (B2 k)]

/-- Equation (23.22) with the printed `(n+4)u` term and a genuine explicit
quadratic remainder. -/
theorem higham23_eq23_22_threeM_imaginary_firstOrder (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 4)) :
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlThreeMImaginary fp A1 A2 B1 B2| ≤
      ((n + 4 : ℕ) : ℝ) * fp.u *
          (∑ k : Fin n,
            ((|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) +
              |A1 k| * |B1 k| + |A2 k| * |B2 k|)) +
        higham23GammaRemainder (n + 4) fp.u *
          (∑ k : Fin n,
            ((|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) +
              |A1 k| * |B1 k| + |A2 k| * |B2 k|)) :=
  higham23_error_bound_gamma_split fp (n + 4) _ _ hvalid
    (higham23_eq23_22_threeM_imaginary_error fp A1 A2 B1 B2 hvalid)

/-- The componentwise budget in (23.22). -/
noncomputable def higham23ThreeMImaginaryBudget {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n,
    ((|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) +
      |A1 k| * |B1 k| + |A2 k| * |B2 k|)

/-- One product term is invariant under cancellation of a positive middle
diagonal scaling and acquires only the outside row/column scale. -/
theorem higham23_abs_product_diagonal_scaling
    {l r s a b : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r) (hs : 0 < s) :
    |l * a * s| * |s⁻¹ * b * r| = l * r * (|a| * |b|) := by
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hl,
    abs_of_nonneg hr, abs_of_pos hs, abs_inv, abs_of_pos hs]
  field_simp [ne_of_gt hs]

/-- Precise prose after (23.22): the complete leading 3M budget scales as
`D1 * budget * D3`; since the explicit gamma remainder multiplies the same
budget, the hidden second-order family has the identical invariance. -/
theorem higham23_threeM_budget_diagonal_scaling {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (l r : ℝ) (s : Fin n → ℝ)
    (hl : 0 ≤ l) (hr : 0 ≤ r) (hs : ∀ k, 0 < s k) :
    higham23ThreeMImaginaryBudget
        (fun k ↦ l * A1 k * s k) (fun k ↦ l * A2 k * s k)
        (fun k ↦ (s k)⁻¹ * B1 k * r) (fun k ↦ (s k)⁻¹ * B2 k * r) =
      l * r * higham23ThreeMImaginaryBudget A1 A2 B1 B2 := by
  unfold higham23ThreeMImaginaryBudget
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h11 := higham23_abs_product_diagonal_scaling hl hr (hs k)
    (a := A1 k) (b := B1 k)
  have h12 := higham23_abs_product_diagonal_scaling hl hr (hs k)
    (a := A1 k) (b := B2 k)
  have h21 := higham23_abs_product_diagonal_scaling hl hr (hs k)
    (a := A2 k) (b := B1 k)
  have h22 := higham23_abs_product_diagonal_scaling hl hr (hs k)
    (a := A2 k) (b := B2 k)
  rw [mul_add, add_mul]
  nlinarith

/-! ### Normwise complex-multiplication consequences -/

/-- The exact imaginary part of the complex matrix product `A * B`. -/
noncomputable def higham23ComplexProductImaginary {n : ℕ}
    (A B : CMatrix n n) (i j : Fin n) : ℝ :=
  ∑ k : Fin n,
    ((A i k).re * (B k j).im + (A i k).im * (B k j).re)

/-- The conventional rounded path for every entry of the imaginary part. -/
noncomputable def higham23FlConventionalImaginaryMatrix (fp : FPModel) {n : ℕ}
    (A B : CMatrix n n) (i j : Fin n) : ℝ :=
  higham23FlConventionalImaginary fp
    (fun k ↦ (A i k).re) (fun k ↦ (A i k).im)
    (fun k ↦ (B k j).re) (fun k ↦ (B k j).im)

/-- The rounded 3M path for every entry of the imaginary part. -/
noncomputable def higham23FlThreeMImaginaryMatrix (fp : FPModel) {n : ℕ}
    (A B : CMatrix n n) (i j : Fin n) : ℝ :=
  higham23FlThreeMImaginary fp
    (fun k ↦ (A i k).re) (fun k ↦ (A i k).im)
    (fun k ↦ (B k j).re) (fun k ↦ (B k j).im)

/-- A row of the conventional componentwise budget is bounded by twice the
product of the two induced infinity norms. -/
theorem higham23_conventional_imaginary_budget_row_le {n : ℕ}
    (A B : CMatrix n n) (i : Fin n) :
    (∑ j : Fin n, ∑ k : Fin n,
        (|(A i k).re| * |(B k j).im| +
          |(A i k).im| * |(B k j).re|)) ≤
      2 * complexMatrixInfNorm A * complexMatrixInfNorm B := by
  have hBnonneg : 0 ≤ complexMatrixInfNorm B := complexMatrixInfNorm_nonneg B
  have hBre : ∀ k : Fin n,
      (∑ j : Fin n, |(B k j).re|) ≤ complexMatrixInfNorm B := by
    intro k
    exact le_trans (Finset.sum_le_sum (fun j _ ↦ Complex.abs_re_le_norm (B k j)))
      (complexMatrixInfNorm_row_sum_le B k)
  have hBim : ∀ k : Fin n,
      (∑ j : Fin n, |(B k j).im|) ≤ complexMatrixInfNorm B := by
    intro k
    exact le_trans (Finset.sum_le_sum (fun j _ ↦ Complex.abs_im_le_norm (B k j)))
      (complexMatrixInfNorm_row_sum_le B k)
  have hAre : (∑ k : Fin n, |(A i k).re|) ≤ complexMatrixInfNorm A :=
    le_trans (Finset.sum_le_sum (fun k _ ↦ Complex.abs_re_le_norm (A i k)))
      (complexMatrixInfNorm_row_sum_le A i)
  have hAim : (∑ k : Fin n, |(A i k).im|) ≤ complexMatrixInfNorm A :=
    le_trans (Finset.sum_le_sum (fun k _ ↦ Complex.abs_im_le_norm (A i k)))
      (complexMatrixInfNorm_row_sum_le A i)
  calc
    (∑ j : Fin n, ∑ k : Fin n,
        (|(A i k).re| * |(B k j).im| + |(A i k).im| * |(B k j).re|)) =
        ∑ k : Fin n,
          (|(A i k).re| * (∑ j : Fin n, |(B k j).im|) +
            |(A i k).im| * (∑ j : Fin n, |(B k j).re|)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ k : Fin n,
        (|(A i k).re| * complexMatrixInfNorm B +
          |(A i k).im| * complexMatrixInfNorm B) := by
      apply Finset.sum_le_sum
      intro k _
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hBim k) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hBre k) (abs_nonneg _))
    _ = ((∑ k : Fin n, |(A i k).re|) +
          ∑ k : Fin n, |(A i k).im|) * complexMatrixInfNorm B := by
      rw [add_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    _ ≤ (complexMatrixInfNorm A + complexMatrixInfNorm A) *
        complexMatrixInfNorm B :=
      mul_le_mul_of_nonneg_right (add_le_add hAre hAim) hBnonneg
    _ = 2 * complexMatrixInfNorm A * complexMatrixInfNorm B := by ring

/-- The elementary `√2` weakening used between (23.22) and (23.24). -/
theorem higham23_abs_re_add_abs_im_le_sqrt_two_mul_norm (z : ℂ) :
    |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := by
  have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hnorm : 0 ≤ ‖z‖ := norm_nonneg _
  have hxy : |z.re| ^ 2 + |z.im| ^ 2 = ‖z‖ ^ 2 := by
    simpa [Complex.normSq, pow_two] using Complex.normSq_eq_norm_sq z
  have hsq : (|z.re| + |z.im|) ^ 2 ≤
      (Real.sqrt 2 * ‖z‖) ^ 2 := by
    rw [mul_pow, hsqrtSq, ← hxy]
    nlinarith [sq_nonneg (|z.re| - |z.im|)]
  exact (sq_le_sq₀
    (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg hsqrt hnorm)).mp hsq

/-- A row of the 3M budget is bounded by four times the product of the induced
infinity norms, exactly the weakening used for equation (23.24). -/
theorem higham23_threeM_imaginary_budget_row_le {n : ℕ}
    (A B : CMatrix n n) (i : Fin n) :
    (∑ j : Fin n, ∑ k : Fin n,
      ((|(A i k).re| + |(A i k).im|) *
          (|(B k j).re| + |(B k j).im|) +
        |(A i k).re| * |(B k j).re| +
        |(A i k).im| * |(B k j).im|)) ≤
      4 * complexMatrixInfNorm A * complexMatrixInfNorm B := by
  let s : ℝ := Real.sqrt 2
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = 2 := by dsimp [s]; norm_num
  have hAn : 0 ≤ complexMatrixInfNorm A := complexMatrixInfNorm_nonneg A
  have hBn : 0 ≤ complexMatrixInfNorm B := complexMatrixInfNorm_nonneg B
  have hAri : (∑ k : Fin n, (|(A i k).re| + |(A i k).im|)) ≤
      s * complexMatrixInfNorm A := by
    calc
      _ ≤ ∑ k : Fin n, s * ‖A i k‖ := by
        apply Finset.sum_le_sum
        intro k _
        exact higham23_abs_re_add_abs_im_le_sqrt_two_mul_norm (A i k)
      _ = s * (∑ k : Fin n, ‖A i k‖) := by rw [Finset.mul_sum]
      _ ≤ s * complexMatrixInfNorm A :=
        mul_le_mul_of_nonneg_left (complexMatrixInfNorm_row_sum_le A i) hs
  have hBri : ∀ k : Fin n,
      (∑ j : Fin n, (|(B k j).re| + |(B k j).im|)) ≤
        s * complexMatrixInfNorm B := by
    intro k
    calc
      _ ≤ ∑ j : Fin n, s * ‖B k j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact higham23_abs_re_add_abs_im_le_sqrt_two_mul_norm (B k j)
      _ = s * (∑ j : Fin n, ‖B k j‖) := by rw [Finset.mul_sum]
      _ ≤ s * complexMatrixInfNorm B :=
        mul_le_mul_of_nonneg_left (complexMatrixInfNorm_row_sum_le B k) hs
  have hAre : (∑ k : Fin n, |(A i k).re|) ≤ complexMatrixInfNorm A :=
    le_trans (Finset.sum_le_sum (fun k _ ↦ Complex.abs_re_le_norm (A i k)))
      (complexMatrixInfNorm_row_sum_le A i)
  have hAim : (∑ k : Fin n, |(A i k).im|) ≤ complexMatrixInfNorm A :=
    le_trans (Finset.sum_le_sum (fun k _ ↦ Complex.abs_im_le_norm (A i k)))
      (complexMatrixInfNorm_row_sum_le A i)
  have hBre : ∀ k : Fin n,
      (∑ j : Fin n, |(B k j).re|) ≤ complexMatrixInfNorm B := by
    intro k
    exact le_trans (Finset.sum_le_sum (fun j _ ↦ Complex.abs_re_le_norm (B k j)))
      (complexMatrixInfNorm_row_sum_le B k)
  have hBim : ∀ k : Fin n,
      (∑ j : Fin n, |(B k j).im|) ≤ complexMatrixInfNorm B := by
    intro k
    exact le_trans (Finset.sum_le_sum (fun j _ ↦ Complex.abs_im_le_norm (B k j)))
      (complexMatrixInfNorm_row_sum_le B k)
  have hsplit :
      (∑ j : Fin n, ∑ k : Fin n,
        ((|(A i k).re| + |(A i k).im|) *
            (|(B k j).re| + |(B k j).im|) +
          |(A i k).re| * |(B k j).re| +
          |(A i k).im| * |(B k j).im|)) =
        ∑ k : Fin n,
          ((|(A i k).re| + |(A i k).im|) *
              (∑ j : Fin n, (|(B k j).re| + |(B k j).im|)) +
            |(A i k).re| * (∑ j : Fin n, |(B k j).re|) +
            |(A i k).im| * (∑ j : Fin n, |(B k j).im|)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hsplit]
  calc
    _ ≤ ∑ k : Fin n,
        ((|(A i k).re| + |(A i k).im|) * (s * complexMatrixInfNorm B) +
          |(A i k).re| * complexMatrixInfNorm B +
          |(A i k).im| * complexMatrixInfNorm B) := by
      apply Finset.sum_le_sum
      intro k _
      gcongr
      · exact hBri k
      · exact hBre k
      · exact hBim k
    _ = ((∑ k : Fin n, (|(A i k).re| + |(A i k).im|)) *
          (s * complexMatrixInfNorm B) +
        (∑ k : Fin n, |(A i k).re|) * complexMatrixInfNorm B +
        (∑ k : Fin n, |(A i k).im|) * complexMatrixInfNorm B) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    _ ≤ (s * complexMatrixInfNorm A) * (s * complexMatrixInfNorm B) +
        complexMatrixInfNorm A * complexMatrixInfNorm B +
        complexMatrixInfNorm A * complexMatrixInfNorm B := by
      gcongr
    _ = 4 * complexMatrixInfNorm A * complexMatrixInfNorm B := by
      calc
        _ = (s * s + 2) * complexMatrixInfNorm A * complexMatrixInfNorm B := by ring
        _ = _ := by rw [hs2]; ring

/-- Equation (23.23), in an exact-gamma form for the actual rounded
conventional imaginary-part matrix. -/
theorem higham23_eq23_23_conventional_imaginary_normwise (fp : FPModel) {n : ℕ}
    (A B : CMatrix n n) (hvalid : gammaValid fp (n + 1)) :
    complexMatrixInfNorm (fun i j ↦
        ((higham23ComplexProductImaginary A B i j -
          higham23FlConventionalImaginaryMatrix fp A B i j : ℝ) : ℂ)) ≤
      2 * gamma fp (n + 1) *
        complexMatrixInfNorm A * complexMatrixInfNorm B := by
  apply complexMatrixInfNorm_le_of_row_sum_le
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (gamma_nonneg fp hvalid))
        (complexMatrixInfNorm_nonneg A))
      (complexMatrixInfNorm_nonneg B)
  intro i
  calc
    (∑ j : Fin n, ‖((higham23ComplexProductImaginary A B i j -
        higham23FlConventionalImaginaryMatrix fp A B i j : ℝ) : ℂ)‖) =
        ∑ j : Fin n, |higham23ComplexProductImaginary A B i j -
          higham23FlConventionalImaginaryMatrix fp A B i j| := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin n, gamma fp (n + 1) *
        (∑ k : Fin n,
          (|(A i k).re| * |(B k j).im| +
            |(A i k).im| * |(B k j).re|)) := by
      apply Finset.sum_le_sum
      intro j _
      simpa [higham23ComplexProductImaginary,
        higham23FlConventionalImaginaryMatrix] using
        higham23_eq23_21_conventional_imaginary_error fp
          (fun k ↦ (A i k).re) (fun k ↦ (A i k).im)
          (fun k ↦ (B k j).re) (fun k ↦ (B k j).im) hvalid
    _ = gamma fp (n + 1) *
        (∑ j : Fin n, ∑ k : Fin n,
          (|(A i k).re| * |(B k j).im| +
            |(A i k).im| * |(B k j).re|)) := by rw [Finset.mul_sum]
    _ ≤ gamma fp (n + 1) *
        (2 * complexMatrixInfNorm A * complexMatrixInfNorm B) :=
      mul_le_mul_of_nonneg_left
        (higham23_conventional_imaginary_budget_row_le A B i)
        (gamma_nonneg fp hvalid)
    _ = 2 * gamma fp (n + 1) *
        complexMatrixInfNorm A * complexMatrixInfNorm B := by ring

/-- Equation (23.24), in an exact-gamma form for the actual rounded 3M
imaginary-part matrix. -/
theorem higham23_eq23_24_threeM_imaginary_normwise (fp : FPModel) {n : ℕ}
    (A B : CMatrix n n) (hvalid : gammaValid fp (n + 4)) :
    complexMatrixInfNorm (fun i j ↦
        ((higham23ComplexProductImaginary A B i j -
          higham23FlThreeMImaginaryMatrix fp A B i j : ℝ) : ℂ)) ≤
      4 * gamma fp (n + 4) *
        complexMatrixInfNorm A * complexMatrixInfNorm B := by
  apply complexMatrixInfNorm_le_of_row_sum_le
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (gamma_nonneg fp hvalid))
        (complexMatrixInfNorm_nonneg A))
      (complexMatrixInfNorm_nonneg B)
  intro i
  calc
    (∑ j : Fin n, ‖((higham23ComplexProductImaginary A B i j -
        higham23FlThreeMImaginaryMatrix fp A B i j : ℝ) : ℂ)‖) =
        ∑ j : Fin n, |higham23ComplexProductImaginary A B i j -
          higham23FlThreeMImaginaryMatrix fp A B i j| := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin n, gamma fp (n + 4) *
        (∑ k : Fin n,
          ((|(A i k).re| + |(A i k).im|) *
              (|(B k j).re| + |(B k j).im|) +
            |(A i k).re| * |(B k j).re| +
            |(A i k).im| * |(B k j).im|)) := by
      apply Finset.sum_le_sum
      intro j _
      simpa [higham23ComplexProductImaginary,
        higham23FlThreeMImaginaryMatrix] using
        higham23_eq23_22_threeM_imaginary_error fp
          (fun k ↦ (A i k).re) (fun k ↦ (A i k).im)
          (fun k ↦ (B k j).re) (fun k ↦ (B k j).im) hvalid
    _ = gamma fp (n + 4) *
        (∑ j : Fin n, ∑ k : Fin n,
          ((|(A i k).re| + |(A i k).im|) *
              (|(B k j).re| + |(B k j).im|) +
            |(A i k).re| * |(B k j).re| +
            |(A i k).im| * |(B k j).im|)) := by rw [Finset.mul_sum]
    _ ≤ gamma fp (n + 4) *
        (4 * complexMatrixInfNorm A * complexMatrixInfNorm B) :=
      mul_le_mul_of_nonneg_left
        (higham23_threeM_imaginary_budget_row_le A B i)
        (gamma_nonneg fp hvalid)
    _ = 4 * gamma fp (n + 4) *
        complexMatrixInfNorm A * complexMatrixInfNorm B := by ring

/-- Equation (23.23) with the printed first-order coefficient and an explicit
quadratic remainder. -/
theorem higham23_eq23_23_conventional_imaginary_normwise_firstOrder
    (fp : FPModel) {n : ℕ} (A B : CMatrix n n)
    (hvalid : gammaValid fp (n + 1)) :
    complexMatrixInfNorm (fun i j ↦
        ((higham23ComplexProductImaginary A B i j -
          higham23FlConventionalImaginaryMatrix fp A B i j : ℝ) : ℂ)) ≤
      2 * ((n + 1 : ℕ) : ℝ) * fp.u *
          complexMatrixInfNorm A * complexMatrixInfNorm B +
        2 * higham23GammaRemainder (n + 1) fp.u *
          complexMatrixInfNorm A * complexMatrixInfNorm B := by
  calc
    _ ≤ 2 * gamma fp (n + 1) *
        complexMatrixInfNorm A * complexMatrixInfNorm B :=
      higham23_eq23_23_conventional_imaginary_normwise fp A B hvalid
    _ = _ := by rw [higham23_gamma_split fp (n + 1) hvalid]; ring

/-- Equation (23.24) with the printed first-order coefficient and explicit
quadratic remainder. -/
theorem higham23_eq23_24_threeM_imaginary_normwise_firstOrder
    (fp : FPModel) {n : ℕ} (A B : CMatrix n n)
    (hvalid : gammaValid fp (n + 4)) :
    complexMatrixInfNorm (fun i j ↦
        ((higham23ComplexProductImaginary A B i j -
          higham23FlThreeMImaginaryMatrix fp A B i j : ℝ) : ℂ)) ≤
      4 * ((n + 4 : ℕ) : ℝ) * fp.u *
          complexMatrixInfNorm A * complexMatrixInfNorm B +
        4 * higham23GammaRemainder (n + 4) fp.u *
          complexMatrixInfNorm A * complexMatrixInfNorm B := by
  calc
    _ ≤ 4 * gamma fp (n + 4) *
        complexMatrixInfNorm A * complexMatrixInfNorm B :=
      higham23_eq23_24_threeM_imaginary_normwise fp A B hvalid
    _ = _ := by rw [higham23_gamma_split fp (n + 4) hvalid]; ring

end ThreeM

end NumStability
