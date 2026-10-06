-- NumStability/Source/Higham/Chapter07/LinearSystemsConditioning/Theorem03/RectangularResults.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.HighamChapter7Rectangular`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import NumStability.Analysis.PerturbationTheory
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.RectangularTheorems

/-!
# RectangularResults

Relocated from `NumStability.Analysis.HighamChapter7Rectangular` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/




namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 7: rectangular source statements

The printed statements of Theorems 7.1 and 7.3 allow an `m × n` data
matrix.  The older public wrappers used one dimension for both the residual
and solution spaces.  This file restores the two independent dimensions.
-/






private lemma higham7_rect_div_abs_le_of_bound {r s ε : ℝ}
    (hε : 0 ≤ ε) (hs : 0 ≤ s) (hbound : |r| ≤ ε * s) :
    |if s = 0 then 0 else r / s| ≤ ε := by
  split_ifs with hs0
  · simpa using hε
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    rw [abs_div, abs_of_pos hspos]
    exact (div_le_iff₀ hspos).2 (by simpa [mul_comm] using hbound)


















































/-- **Theorem 7.3 (Oettli--Prager), sufficient direction, rectangular form.**

The proof is constructive, row by row.  It builds perturbations with the
printed componentwise budgets and proves the perturbed `m × n` system exactly.
-/
theorem higham7_3_rectangular_sufficient {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b f : Fin m → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hbound : ∀ i, |higham7RectResidual A y b i| ≤
      ε * (∑ j : Fin n, E i j * |y j| + f i)) :
    ∃ (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      (∀ i j, |ΔA i j| ≤ ε * E i j) ∧
      (∀ i, |Δb i| ≤ ε * f i) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) := by
  let r : Fin m → ℝ := higham7RectResidual A y b
  let s : Fin m → ℝ := fun i => ∑ j : Fin n, E i j * |y j| + f i
  let t : Fin m → ℝ := fun i => if s i = 0 then 0 else r i / s i
  let ΔA : Fin m → Fin n → ℝ :=
    fun i j => t i * E i j * signInd (y j)
  let Δb : Fin m → ℝ := fun i => -(t i * f i)
  have hs : ∀ i, 0 ≤ s i := by
    intro i
    exact add_nonneg
      (Finset.sum_nonneg fun j _ => mul_nonneg (hE i j) (abs_nonneg _))
      (hf i)
  have ht : ∀ i, |t i| ≤ ε := by
    intro i
    exact higham7_rect_div_abs_le_of_bound hε (hs i) (hbound i)
  refine ⟨ΔA, Δb, ?_, ?_, ?_⟩
  · intro i j
    show |t i * E i j * signInd (y j)| ≤ ε * E i j
    rw [abs_mul, abs_mul, abs_signInd, mul_one, abs_of_nonneg (hE i j)]
    exact mul_le_mul_of_nonneg_right (ht i) (hE i j)
  · intro i
    show |-(t i * f i)| ≤ ε * f i
    rw [abs_neg, abs_mul, abs_of_nonneg (hf i)]
    exact mul_le_mul_of_nonneg_right (ht i) (hf i)
  · intro i
    have hΔAy : ∀ j, ΔA i j * y j = t i * E i j * |y j| := by
      intro j
      show t i * E i j * signInd (y j) * y j = t i * E i j * |y j|
      rw [mul_assoc (t i * E i j), signInd_mul_eq_abs]
    have hsum : ∑ j : Fin n, t i * E i j * |y j| =
        t i * ∑ j : Fin n, E i j * |y j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hts : t i * s i = r i := by
      dsimp [t]
      split_ifs with hs0
      · have hr0 : r i = 0 := by
          apply abs_eq_zero.mp
          apply le_antisymm
          · calc
              |r i| ≤ ε * s i := hbound i
              _ = 0 := by rw [hs0, mul_zero]
          · exact abs_nonneg _
        simp [hs0, hr0]
      · exact div_mul_cancel₀ (r i) hs0
    simp_rw [add_mul, hΔAy, Finset.sum_add_distrib]
    rw [hsum]
    change (∑ j : Fin n, A i j * y j) +
        t i * (∑ j : Fin n, E i j * |y j|) = b i - t i * f i
    have hr : r i = b i - ∑ j : Fin n, A i j * y j := rfl
    have hsdef : s i = ∑ j : Fin n, E i j * |y j| + f i := rfl
    rw [hsdef] at hts
    linarith

/-- **Theorem 7.3 (Oettli--Prager), full rectangular characterization.**

This is the literal `m × n` equivalence printed in the chapter. -/
theorem higham7_3_rectangular {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b f : Fin m → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i) :
    (∀ i, |higham7RectResidual A y b i| ≤
      ε * (∑ j : Fin n, E i j * |y j| + f i)) ↔
    ∃ (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      (∀ i j, |ΔA i j| ≤ ε * E i j) ∧
      (∀ i, |Δb i| ≤ ε * f i) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) := by
  constructor
  · exact higham7_3_rectangular_sufficient A E y b f ε hε hE hf
  · rintro ⟨ΔA, Δb, hΔA, hΔb, hperturbed⟩
    exact higham7_3_rectangular_necessary A ΔA E y b Δb f ε
      hΔA hΔb hperturbed

/-! ## Theorem 7.1 (Rigal--Gaches), rectangular subordinate-norm form -/





















































































































































































































































































end NumStability
