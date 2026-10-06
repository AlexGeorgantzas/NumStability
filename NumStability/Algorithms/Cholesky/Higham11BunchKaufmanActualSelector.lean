/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Algorithm 11.2: actual finite first-pivot selector

The chapter-level predicate `BunchKaufmanPartialPivotCase` records the four
printed scalar tests but, by itself, does not compute the column maxima, the
maximizing row, or the symmetric interchange.  This module constructs those
objects from a finite matrix.  It is the matrix-level front end needed by a
permutation-aware recursive Bunch--Kaufman executor.
-/

import NumStability.Algorithms.HighamChapter11
import NumStability.Algorithms.Sylvester.Higham16QuasiRoundedSolve

namespace NumStability

open Wave15

/-- The leading index of a nonempty finite matrix. -/
def higham11_2_firstIndex {n : ℕ} (hn : 0 < n) : Fin n := ⟨0, hn⟩

/-- All rows attaining the first-column off-diagonal maximum.  The leading
diagonal entry is replaced by zero, exactly as in Algorithm 11.2's definition
of the first subdiagonal maximum. -/
noncomputable def higham11_2_bunchKaufmanFirstColumnMaximizers {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j =>
    |if j = higham11_2_firstIndex hn then 0
      else A j (higham11_2_firstIndex hn)| =
        higham11_5_rookColumnMax A (higham11_2_firstIndex hn)

theorem higham11_2_bunchKaufmanFirstColumnMaximizers_nonempty {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    (higham11_2_bunchKaufmanFirstColumnMaximizers hn A).Nonempty := by
  let i₀ := higham11_2_firstIndex hn
  let r₀ := higham11_5_rookColumnArgmax A i₀
  refine ⟨r₀, ?_⟩
  simp only [higham11_2_bunchKaufmanFirstColumnMaximizers,
    Finset.mem_filter, Finset.mem_univ, true_and]
  change |if r₀ = i₀ then 0 else A r₀ i₀| =
    higham11_5_rookColumnMax A i₀
  rfl

/-- The row `r` printed in Algorithm 11.2: the *first* (least-indexed) row
attaining the first-column off-diagonal maximum. -/
noncomputable def higham11_2_bunchKaufmanMaxRow {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : Fin n :=
  (higham11_2_bunchKaufmanFirstColumnMaximizers hn A).min'
    (higham11_2_bunchKaufmanFirstColumnMaximizers_nonempty hn A)

theorem higham11_2_bunchKaufmanMaxRow_mem_firstColumnMaximizers {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    higham11_2_bunchKaufmanMaxRow hn A ∈
      higham11_2_bunchKaufmanFirstColumnMaximizers hn A := by
  exact Finset.min'_mem _ _

/-- `ω₁`, the largest subdiagonal magnitude in the first column. -/
noncomputable def higham11_2_bunchKaufmanOmegaOne {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  higham11_5_rookColumnMax A (higham11_2_firstIndex hn)

/-- `ωᵣ`, the largest off-diagonal magnitude in the selected column `r`. -/
noncomputable def higham11_2_bunchKaufmanOmegaRow {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  higham11_5_rookColumnMax A (higham11_2_bunchKaufmanMaxRow hn A)

/-- The finite matrix-level branch selected by the tests printed in
Algorithm 11.2. -/
noncomputable def higham11_2_bunchKaufmanFirstBranch {n : ℕ} (hn : 0 < n)
    (α : ℝ) (A : Fin n → Fin n → ℝ) : BunchKaufmanCase :=
  let i₀ := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  let ω₁ := higham11_2_bunchKaufmanOmegaOne hn A
  let ωr := higham11_2_bunchKaufmanOmegaRow hn A
  if ω₁ = 0 then BunchKaufmanCase.noAction
  else if |A i₀ i₀| ≥ α * ω₁ then BunchKaufmanCase.case1
  else if |A i₀ i₀| * ωr ≥ α * ω₁ ^ 2 then BunchKaufmanCase.case2
  else if |A r r| ≥ α * ωr then BunchKaufmanCase.case3
  else BunchKaufmanCase.case4

/-- The selected row really maximizes the off-diagonal magnitudes in the
first column. -/
theorem higham11_2_bunchKaufmanOmegaOne_spec {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (j : Fin n) :
    |if j = higham11_2_firstIndex hn then 0
      else A j (higham11_2_firstIndex hn)| ≤
        higham11_2_bunchKaufmanOmegaOne hn A := by
  exact higham11_5_rookColumnMax_spec A (higham11_2_firstIndex hn) j

/-- `ω₁` is nonnegative. -/
theorem higham11_2_bunchKaufmanOmegaOne_nonneg {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    0 ≤ higham11_2_bunchKaufmanOmegaOne hn A := by
  unfold higham11_2_bunchKaufmanOmegaOne higham11_5_rookColumnMax
  exact abs_nonneg _

/-- The selected row attains the off-diagonal maximum, including in the
zero-column case where the selected row may be the leading row. -/
theorem higham11_2_bunchKaufmanMaxRow_attains_omegaOne_if {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    |if higham11_2_bunchKaufmanMaxRow hn A = higham11_2_firstIndex hn then 0
      else A (higham11_2_bunchKaufmanMaxRow hn A)
        (higham11_2_firstIndex hn)| =
      higham11_2_bunchKaufmanOmegaOne hn A := by
  have hmem :=
    higham11_2_bunchKaufmanMaxRow_mem_firstColumnMaximizers hn A
  exact (Finset.mem_filter.mp hmem).2

/-- Source tie rule: every row attaining `ω₁` has index at least the selected
row. -/
theorem higham11_2_bunchKaufmanMaxRow_le_of_attains_omegaOne {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (j : Fin n)
    (hj : |if j = higham11_2_firstIndex hn then 0
      else A j (higham11_2_firstIndex hn)| =
        higham11_2_bunchKaufmanOmegaOne hn A) :
    higham11_2_bunchKaufmanMaxRow hn A ≤ j := by
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩

/-- A nonzero first-column maximum forces the maximizing row to be genuinely
subdiagonal. -/
theorem higham11_2_bunchKaufmanMaxRow_ne_first_of_omegaOne_ne_zero
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hω : higham11_2_bunchKaufmanOmegaOne hn A ≠ 0) :
    higham11_2_bunchKaufmanMaxRow hn A ≠ higham11_2_firstIndex hn := by
  intro hr
  apply hω
  have hattain := higham11_2_bunchKaufmanMaxRow_attains_omegaOne_if hn A
  rw [hr] at hattain
  simpa using hattain.symm

/-- At a nonzero column, the chosen matrix entry attains `ω₁`. -/
theorem higham11_2_bunchKaufmanMaxRow_attains_omegaOne
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hω : higham11_2_bunchKaufmanOmegaOne hn A ≠ 0) :
    |A (higham11_2_bunchKaufmanMaxRow hn A)
        (higham11_2_firstIndex hn)| =
      higham11_2_bunchKaufmanOmegaOne hn A := by
  have hr := higham11_2_bunchKaufmanMaxRow_ne_first_of_omegaOne_ne_zero
    hn A hω
  simpa [hr] using higham11_2_bunchKaufmanMaxRow_attains_omegaOne_if hn A

/-- **Algorithm 11.2 actual branch correctness.**  The branch computed from
the finite argmax data satisfies exactly the existing source decision
predicate.  No branch condition is supplied as a hypothesis. -/
theorem higham11_2_bunchKaufmanFirstBranch_spec {n : ℕ} (hn : 0 < n)
    (α : ℝ) (A : Fin n → Fin n → ℝ) :
    higham11_2_BunchKaufmanPartialPivotCase α
      (A (higham11_2_firstIndex hn) (higham11_2_firstIndex hn))
      (A (higham11_2_bunchKaufmanMaxRow hn A)
        (higham11_2_bunchKaufmanMaxRow hn A))
      (higham11_2_bunchKaufmanOmegaOne hn A)
      (higham11_2_bunchKaufmanOmegaRow hn A)
      (higham11_2_bunchKaufmanFirstBranch hn α A) := by
  classical
  unfold higham11_2_bunchKaufmanFirstBranch
  dsimp only
  split_ifs with hzero hcase1 hcase2 hcase3
  · simpa [higham11_2_BunchKaufmanPartialPivotCase,
      BunchKaufmanPartialPivotCase] using hzero
  · exact ⟨hzero, hcase1⟩
  · exact ⟨hzero, lt_of_not_ge hcase1, hcase2⟩
  · exact ⟨hzero, lt_of_not_ge hcase1, lt_of_not_ge hcase2, hcase3⟩
  · exact ⟨hzero, lt_of_not_ge hcase1, lt_of_not_ge hcase2,
      lt_of_not_ge hcase3⟩

/-- Pivot width returned by the actual first-stage selector.  The no-action
case is represented by width one only as a total default; callers stop rather
than eliminate in that branch. -/
def higham11_2_bunchKaufmanBranchPivotSize : BunchKaufmanCase → PivotSize
  | BunchKaufmanCase.case4 => PivotSize.two
  | _ => PivotSize.one

/-- The symmetric interchange prescribed by Algorithm 11.2 for a matrix of
size at least two.  Cases (1) and (2) use the identity, case (3) moves `r` to
the leading position, and case (4) moves `r` to the second position. -/
noncomputable def higham11_2_bunchKaufmanFirstPerm {n : ℕ} (hn2 : 2 ≤ n)
    (α : ℝ) (A : Fin n → Fin n → ℝ) : Equiv.Perm (Fin n) :=
  let i₀ : Fin n := ⟨0, lt_of_lt_of_le (by omega) hn2⟩
  let i₁ : Fin n := ⟨1, lt_of_lt_of_le (by omega) hn2⟩
  let r := higham11_2_bunchKaufmanMaxRow (lt_of_lt_of_le (by omega) hn2) A
  match higham11_2_bunchKaufmanFirstBranch
      (lt_of_lt_of_le (by omega) hn2) α A with
  | BunchKaufmanCase.case3 => Equiv.swap i₀ r
  | BunchKaufmanCase.case4 => Equiv.swap i₁ r
  | _ => Equiv.refl (Fin n)

/-- Symmetric row/column permutation returned by the actual first-stage
selector. -/
noncomputable def higham11_2_bunchKaufmanFirstPermutedMatrix {n : ℕ}
    (hn2 : 2 ≤ n) (α : ℝ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    A (higham11_2_bunchKaufmanFirstPerm hn2 α A i)
      (higham11_2_bunchKaufmanFirstPerm hn2 α A j)

/-- The returned map is a genuine permutation, so the matrix transformation
cannot silently identify two rows or columns. -/
theorem higham11_2_bunchKaufmanFirstPerm_injective {n : ℕ} (hn2 : 2 ≤ n)
    (α : ℝ) (A : Fin n → Fin n → ℝ) :
    Function.Injective (higham11_2_bunchKaufmanFirstPerm hn2 α A) :=
  (higham11_2_bunchKaufmanFirstPerm hn2 α A).injective

/-- Symmetry is preserved by the actual Algorithm 11.2 interchange. -/
theorem higham11_2_bunchKaufmanFirstPermutedMatrix_symmetric {n : ℕ}
    (hn2 : 2 ≤ n) (α : ℝ) (A : Fin n → Fin n → ℝ)
    (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix
      (higham11_2_bunchKaufmanFirstPermutedMatrix hn2 α A) := by
  intro i j
  exact hA _ _

/-! ## An actual GEPP solve for a selected case-(4) pivot -/

/-- The selected case-(4) pivot block, in the source variable order
`(first,r)`. -/
noncomputable def higham11_2_bunchKaufmanSelectedTwoBlock {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) : Fin 2 → Fin 2 → ℝ :=
  let i₀ := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  fun i j =>
    Fin.cases (Fin.cases (A i₀ i₀) (fun _ => A i₀ r) j)
      (fun _ => Fin.cases (A r i₀) (fun _ => A r r) j) i

/-- The actual two-step GEPP solve used for a selected case-(4) pivot.  The
two equations are swapped so the maximum-magnitude off-diagonal entry is the
first scalar pivot; the unknowns remain ordered `(first,r)`. -/
noncomputable def higham11_2_flSelectedTwoByTwoSolve (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) (z : Fin n → ℝ) :
    Fin 2 → ℝ :=
  let i₀ := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  let xy := fl_solve2x2 fp
    (A r i₀) (A r r) (A i₀ i₀) (A i₀ r) (z r) (z i₀)
  fun p => Fin.cases xy.1 (fun _ => xy.2) p

/-- The computed second GEPP pivot for the actual selected case-(4) solve. -/
noncomputable def higham11_2_flSelectedTwoByTwoSecondPivot (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) : ℝ :=
  let i₀ := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  flSolve2x2SecondPivot fp
    (A r i₀) (A r r) (A i₀ i₀) (A i₀ r)

/-- A selected case-(4) pivot satisfies the growth condition required by the
actual two-step GEPP kernel.  This is derived from the two failed Algorithm
11.2 diagonal tests and the finite argmax equality. -/
theorem higham11_2_case4_selected_fill_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4) :
    let i₀ := higham11_2_firstIndex hn
    let r := higham11_2_bunchKaufmanMaxRow hn A
    |A i₀ i₀| * |A r r| ≤ |A r i₀| * |A i₀ r| := by
  let i₀ := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  let ω₁ := higham11_2_bunchKaufmanOmegaOne hn A
  let ωr := higham11_2_bunchKaufmanOmegaRow hn A
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    hn higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  rcases hcase with ⟨hωne, _hfirst, hprod, hdiag⟩
  have hω0 : 0 ≤ ω₁ := by
    exact higham11_2_bunchKaufmanOmegaOne_nonneg hn A
  have hα0 : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hα1 : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  have hattain : |A r i₀| = ω₁ := by
    exact higham11_2_bunchKaufmanMaxRow_attains_omegaOne hn A hωne
  have hdiag_le : |A r r| ≤ higham11_1_bunchParlettAlpha * ωr :=
    le_of_lt hdiag
  have hfirst_nonneg : 0 ≤ |A i₀ i₀| := abs_nonneg _
  have hstep1 :
      |A i₀ i₀| * |A r r| ≤
        |A i₀ i₀| * (higham11_1_bunchParlettAlpha * ωr) :=
    mul_le_mul_of_nonneg_left hdiag_le hfirst_nonneg
  have hstep2 :
      |A i₀ i₀| * (higham11_1_bunchParlettAlpha * ωr) <
        higham11_1_bunchParlettAlpha ^ 2 * ω₁ ^ 2 := by
    have hm := mul_lt_mul_of_pos_left hprod hα0
    nlinarith
  have hαsq : higham11_1_bunchParlettAlpha ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (higham11_1_bunchParlettAlpha - 1)]
  have hstep3 :
      higham11_1_bunchParlettAlpha ^ 2 * ω₁ ^ 2 ≤ ω₁ ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_right hαsq (sq_nonneg ω₁)
  dsimp only
  calc
    |A i₀ i₀| * |A r r| ≤
        |A i₀ i₀| * (higham11_1_bunchParlettAlpha * ωr) := hstep1
    _ ≤ higham11_1_bunchParlettAlpha ^ 2 * ω₁ ^ 2 := le_of_lt hstep2
    _ ≤ ω₁ ^ 2 := hstep3
    _ = |A r i₀| * |A i₀ r| := by
      rw [hA i₀ r, hattain]
      ring

/-- **Algorithm 11.2 case (4), actual equation-(11.5) producer.**  For the
matrix-selected pivot, an actual rounded two-step GEPP solve returns a
componentwise perturbation `|Delta E| <= 36 u |E|`.  The only run-domain
hypothesis is that the computed second scalar pivot is nonzero.  No solve
residual or perturbation conclusion is assumed. -/
theorem higham11_2_flSelectedTwoByTwoSolve_higham115 (fp : FPModel)
    (hval9 : gammaValid fp 9) (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2)
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hA : IsSymmetricFiniteMatrix A) (z : Fin n → ℝ)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp hn A ≠ 0) :
    ∃ ΔE : Fin 2 → Fin 2 → ℝ,
      higham11_5_twoByTwoPivotSolveStable fp.u 36
        (higham11_2_bunchKaufmanSelectedTwoBlock hn A) ΔE ∧
      ∀ p : Fin 2,
        ∑ q : Fin 2,
          (higham11_2_bunchKaufmanSelectedTwoBlock hn A p q + ΔE p q) *
            higham11_2_flSelectedTwoByTwoSolve fp hn A z q =
          z (Fin.cases (higham11_2_firstIndex hn)
            (fun _ => higham11_2_bunchKaufmanMaxRow hn A) p) := by
  let i₀ := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    hn higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hpivot_abs :=
    higham11_2_bunchKaufmanMaxRow_attains_omegaOne hn A hcase.1
  have hpivot : A r i₀ ≠ 0 := by
    intro hz
    have : higham11_2_bunchKaufmanOmegaOne hn A = 0 := by
      rw [← hpivot_abs, hz, abs_zero]
    exact hcase.1 this
  have hfill : |A i₀ i₀| * |A r r| ≤ |A r i₀| * |A i₀ r| :=
    higham11_2_case4_selected_fill_bound hn A hA hbranch
  obtain ⟨Δ10, Δ11, Δ00, Δ01, hΔ10, hΔ11, hΔ00, hΔ01,
      hrowR, hrow0⟩ :=
    fl_solve2x2_backward_error_componentwise fp
      (A r i₀) (A r r) (A i₀ i₀) (A i₀ r) (z r) (z i₀) 1
      hpivot hsecond (by norm_num) (by simpa using hfill) hval9
  let ΔE : Fin 2 → Fin 2 → ℝ := fun i j =>
    Fin.cases (Fin.cases Δ00 (fun _ => Δ01) j)
      (fun _ => Fin.cases Δ10 (fun _ => Δ11) j) i
  have hgamma : (1 + (1 : ℝ)) * gamma fp 9 ≤ 36 * fp.u := by
    have hg := gamma_le_two_mul_n_u_of_nu_le_half fp 9 hsmall9
    norm_num at hg ⊢
    linarith
  refine ⟨ΔE, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact le_trans hΔ00
        (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
    · exact le_trans hΔ01
        (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
    · exact le_trans hΔ10
        (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
    · exact le_trans hΔ11
        (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
  · intro p
    fin_cases p
    · rw [Fin.sum_univ_two]
      simpa [ΔE, higham11_2_bunchKaufmanSelectedTwoBlock,
        higham11_2_flSelectedTwoByTwoSolve, i₀, r] using hrow0
    · rw [Fin.sum_univ_two]
      simpa [ΔE, higham11_2_bunchKaufmanSelectedTwoBlock,
        higham11_2_flSelectedTwoByTwoSolve, i₀, r] using hrowR

end NumStability
