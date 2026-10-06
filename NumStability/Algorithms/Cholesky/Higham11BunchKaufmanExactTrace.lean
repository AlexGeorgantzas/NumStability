/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Algorithm 11.2: recursive exact active-submatrix trace

Higham states Algorithm 11.2 for the first active stage; the block LDL^T
construction preceding (11.2)--(11.3) then repeats the same choice on the
Schur complement.  This module performs that recursion.  Every constructor
records the branch computed by the finite argmax selector, applies the printed
symmetric interchange, and consumes exactly one or two active indices.

The `noAction` branch is not divided by a possibly zero diagonal.  Its zero
off-diagonal leading column is removed unchanged, which is the exact meaning
of "there is nothing to do on this stage" in the source.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanActualSelector
import NumStability.Algorithms.Cholesky.Higham11BunchExactTrace
import NumStability.Algorithms.Cholesky.BlockLDLTMixedPivotCh11Closure

namespace NumStability

open Ch11Closure.Mixed

abbrev Higham11BunchKaufmanMatrix (n : ℕ) := Fin n → Fin n → ℝ

/-- The trailing principal block used when Algorithm 11.2 reports that the
leading off-diagonal column is zero. -/
def higham11_2_bunchKaufmanNoActionTail {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 1)) :
    Higham11BunchKaufmanMatrix n :=
  fun i j => A i.succ j.succ

theorem higham11_2_bunchKaufmanNoActionTail_symmetric {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 1))
    (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_2_bunchKaufmanNoActionTail A) := by
  intro i j
  exact hA i.succ j.succ

/-- The active matrix after the symmetric interchange selected by Algorithm
11.2.  This definition is used only at dimensions at least two. -/
noncomputable def higham11_2_bunchKaufmanExactActive {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 2)) :
    Higham11BunchKaufmanMatrix (n + 2) :=
  higham11_2_bunchKaufmanFirstPermutedMatrix (by omega)
    higham11_1_bunchParlettAlpha A

theorem higham11_2_bunchKaufmanExactActive_symmetric {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_2_bunchKaufmanExactActive A) := by
  exact higham11_2_bunchKaufmanFirstPermutedMatrix_symmetric
    (by omega) higham11_1_bunchParlettAlpha A hA

/-- Exact one-by-one Schur complement of the matrix after the selected
symmetric interchange. -/
noncomputable def higham11_2_bunchKaufmanExactSchurOne {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 2)) :
    Higham11BunchKaufmanMatrix (n + 1) :=
  higham11_1_bunchSchurOne (higham11_2_bunchKaufmanExactActive A)

theorem higham11_2_bunchKaufmanExactSchurOne_symmetric {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_2_bunchKaufmanExactSchurOne A) := by
  exact higham11_1_bunchSchurOne_symmetric _
    (higham11_2_bunchKaufmanExactActive_symmetric A hA)

/-- Exact two-by-two Schur complement of the matrix after the selected
symmetric interchange. -/
noncomputable def higham11_2_bunchKaufmanExactSchurTwo {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 2)) :
    Higham11BunchKaufmanMatrix n :=
  higham11_1_bunchSchurTwo (higham11_2_bunchKaufmanExactActive A)

theorem higham11_2_bunchKaufmanExactSchurTwo_symmetric {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_2_bunchKaufmanExactSchurTwo A) := by
  exact higham11_1_bunchSchurTwo_symmetric _
    (higham11_2_bunchKaufmanExactActive_symmetric A hA)

/-- On a one-dimensional active matrix the finite selector necessarily takes
the source `noAction` branch. -/
theorem higham11_2_bunchKaufmanFirstBranch_finOne
    (A : Higham11BunchKaufmanMatrix 1) :
    higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.noAction := by
  have harg : higham11_5_rookColumnArgmax A
      (higham11_2_firstIndex (by omega)) =
      higham11_2_firstIndex (by omega) := Subsingleton.elim _ _
  have hω : higham11_2_bunchKaufmanOmegaOne (by omega) A = 0 := by
    simp [higham11_2_bunchKaufmanOmegaOne,
      higham11_5_rookColumnMax, harg]
  simp [higham11_2_bunchKaufmanFirstBranch, hω]

private theorem higham11_2_bunchKaufmanOmegaOne_pos_of_branch
    {n : ℕ} (hn : 0 < n) (A : Higham11BunchKaufmanMatrix n)
    {branch : BunchKaufmanCase}
    (hbranch : branch ≠ BunchKaufmanCase.noAction)
    (hsel : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = branch) :
    0 < higham11_2_bunchKaufmanOmegaOne hn A := by
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    hn higham11_1_bunchParlettAlpha A
  rw [hsel] at hcase
  cases branch <;> simp_all [higham11_2_BunchKaufmanPartialPivotCase,
    BunchKaufmanPartialPivotCase]
  all_goals
    exact lt_of_le_of_ne
      (higham11_2_bunchKaufmanOmegaOne_nonneg hn A) (Ne.symm hcase.1)

/-- At every non-no-action stage, the row/column maximum in the selected row
is positive.  This is the symmetry bridge from the attained first-column
maximum to `omega_r`. -/
theorem higham11_2_bunchKaufmanOmegaRow_pos_of_branch {n : ℕ}
    (hn : 0 < n) (A : Higham11BunchKaufmanMatrix n)
    (hA : IsSymmetricFiniteMatrix A) {branch : BunchKaufmanCase}
    (hbranch : branch ≠ BunchKaufmanCase.noAction)
    (hsel : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = branch) :
    0 < higham11_2_bunchKaufmanOmegaRow hn A := by
  let i₀ := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  let ω₁ := higham11_2_bunchKaufmanOmegaOne hn A
  have hω₁ : 0 < ω₁ :=
    higham11_2_bunchKaufmanOmegaOne_pos_of_branch hn A hbranch hsel
  have hω₁ne : higham11_2_bunchKaufmanOmegaOne hn A ≠ 0 :=
    ne_of_gt hω₁
  have hr : r ≠ i₀ :=
    higham11_2_bunchKaufmanMaxRow_ne_first_of_omegaOne_ne_zero
      hn A hω₁ne
  have hattain : |A r i₀| = ω₁ :=
    higham11_2_bunchKaufmanMaxRow_attains_omegaOne hn A hω₁ne
  have hmax := higham11_5_rookColumnMax_spec A r i₀
  have hle : ω₁ ≤ higham11_2_bunchKaufmanOmegaRow hn A := by
    calc
      ω₁ = |A r i₀| := hattain.symm
      _ = |A i₀ r| := by rw [hA i₀ r]
      _ ≤ higham11_2_bunchKaufmanOmegaRow hn A := by
        simpa [higham11_2_bunchKaufmanOmegaRow, r, i₀, Ne.symm hr] using hmax
  exact lt_of_lt_of_le hω₁ hle

/-- Cases (1) and (2) select a nonzero leading scalar pivot. -/
theorem higham11_2_bunchKaufmanCase1_pivot_ne_zero {n : ℕ}
    (hn : 0 < n) (A : Higham11BunchKaufmanMatrix n)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case1) :
    A (higham11_2_firstIndex hn) (higham11_2_firstIndex hn) ≠ 0 := by
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    hn higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  apply higham11_2_bunch_kaufman_case1_pivot_ne_zero
    higham11_1_bunchParlettAlpha
    (A (higham11_2_firstIndex hn) (higham11_2_firstIndex hn))
    (A (higham11_2_bunchKaufmanMaxRow hn A)
      (higham11_2_bunchKaufmanMaxRow hn A))
    (higham11_2_bunchKaufmanOmegaOne hn A)
    (higham11_2_bunchKaufmanOmegaRow hn A)
  · simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  · exact higham11_2_bunchKaufmanOmegaOne_pos_of_branch hn A (by simp) hbranch
  · exact hcase

theorem higham11_2_bunchKaufmanCase2_pivot_ne_zero {n : ℕ}
    (hn : 0 < n) (A : Higham11BunchKaufmanMatrix n)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case2) :
    A (higham11_2_firstIndex hn) (higham11_2_firstIndex hn) ≠ 0 := by
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    hn higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  apply higham11_2_bunch_kaufman_case2_pivot_ne_zero
    higham11_1_bunchParlettAlpha
    (A (higham11_2_firstIndex hn) (higham11_2_firstIndex hn))
    (A (higham11_2_bunchKaufmanMaxRow hn A)
      (higham11_2_bunchKaufmanMaxRow hn A))
    (higham11_2_bunchKaufmanOmegaOne hn A)
    (higham11_2_bunchKaufmanOmegaRow hn A)
  · simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  · exact higham11_2_bunchKaufmanOmegaOne_pos_of_branch hn A (by simp) hbranch
  · exact hcase

/-- Case (3) selects a nonzero `a_rr` after its symmetric interchange. -/
theorem higham11_2_bunchKaufmanCase3_pivot_ne_zero {n : ℕ}
    (hn : 0 < n) (A : Higham11BunchKaufmanMatrix n)
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case3) :
    A (higham11_2_bunchKaufmanMaxRow hn A)
      (higham11_2_bunchKaufmanMaxRow hn A) ≠ 0 := by
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    hn higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  apply higham11_2_bunch_kaufman_case3_pivot_ne_zero
    higham11_1_bunchParlettAlpha
    (A (higham11_2_firstIndex hn) (higham11_2_firstIndex hn))
    (A (higham11_2_bunchKaufmanMaxRow hn A)
      (higham11_2_bunchKaufmanMaxRow hn A))
    (higham11_2_bunchKaufmanOmegaOne hn A)
    (higham11_2_bunchKaufmanOmegaRow hn A)
  · simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  · exact higham11_2_bunchKaufmanOmegaRow_pos_of_branch hn A hA (by simp) hbranch
  · exact hcase

/-- Case (4) selects a genuinely nonsingular two-by-two pivot block. -/
theorem higham11_2_bunchKaufmanCase4_det_ne_zero {n : ℕ}
    (hn : 0 < n) (A : Higham11BunchKaufmanMatrix n)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4) :
    let i₀ := higham11_2_firstIndex hn
    let r := higham11_2_bunchKaufmanMaxRow hn A
    A i₀ i₀ * A r r - A r i₀ ^ 2 ≠ 0 := by
  let i₀ := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  let ω₁ := higham11_2_bunchKaufmanOmegaOne hn A
  let ωr := higham11_2_bunchKaufmanOmegaRow hn A
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    hn higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hω₁ : 0 < ω₁ :=
    higham11_2_bunchKaufmanOmegaOne_pos_of_branch hn A (by simp) hbranch
  have hattain : |A r i₀| = ω₁ :=
    higham11_2_bunchKaufmanMaxRow_attains_omegaOne hn A (ne_of_gt hω₁)
  exact higham11_4_bunch_kaufman_case4_twoByTwo_det_ne_zero
    (A i₀ i₀) (A r i₀) (A r r) ω₁ ωr hω₁ hcase hattain

/-- Cases (1) and (2) prescribe the identity interchange. -/
theorem higham11_2_bunchKaufmanExactActive_eq_of_case1_or_case2 {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 2))
    (hbranch :
      higham11_2_bunchKaufmanFirstBranch (by omega)
          higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case1 ∨
        higham11_2_bunchKaufmanFirstBranch (by omega)
          higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case2) :
    higham11_2_bunchKaufmanExactActive A = A := by
  rcases hbranch with hbranch | hbranch
  · funext i j
    simp [higham11_2_bunchKaufmanExactActive,
      higham11_2_bunchKaufmanFirstPermutedMatrix,
      higham11_2_bunchKaufmanFirstPerm, hbranch]
  · funext i j
    simp [higham11_2_bunchKaufmanExactActive,
      higham11_2_bunchKaufmanFirstPermutedMatrix,
      higham11_2_bunchKaufmanFirstPerm, hbranch]

/-- In case (3), the selected `a_rr` is the leading scalar pivot after the
printed symmetric interchange. -/
theorem higham11_2_bunchKaufmanExactActive_case3_pivot {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case3) :
    higham11_2_bunchKaufmanExactActive A 0 0 =
      A (higham11_2_bunchKaufmanMaxRow (by omega) A)
        (higham11_2_bunchKaufmanMaxRow (by omega) A) := by
  simp [higham11_2_bunchKaufmanExactActive,
    higham11_2_bunchKaufmanFirstPermutedMatrix,
    higham11_2_bunchKaufmanFirstPerm, hbranch]

/-- In case (4), the source-order selected block `(first,r)` is exactly the
leading block of the symmetrically permuted active matrix used by the recursive
Schur complement. -/
theorem higham11_2_bunchKaufmanSelectedTwoBlock_eq_activeLeading {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4) :
    ∀ p q : Fin 2,
      higham11_2_bunchKaufmanSelectedTwoBlock (by omega) A p q =
        higham11_2_bunchKaufmanExactActive A (embedTwo n p) (embedTwo n q) := by
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hr := higham11_2_bunchKaufmanMaxRow_ne_first_of_omegaOne_ne_zero
    (by omega) A hcase.1
  have hr0 : higham11_2_bunchKaufmanMaxRow (by omega) A ≠
      (0 : Fin (n + 2)) := by
    simpa [higham11_2_firstIndex] using hr
  have hswap0 :
      Equiv.swap (1 : Fin (n + 2))
          (higham11_2_bunchKaufmanMaxRow (by omega) A) 0 = 0 := by
    exact Equiv.swap_apply_of_ne_of_ne (x := (0 : Fin (n + 2)))
      (show (0 : Fin (n + 2)) ≠ (1 : Fin (n + 2)) by
        apply Fin.ne_of_val_ne
        norm_num)
      (Ne.symm hr0)
  intro p q
  fin_cases p <;> fin_cases q <;>
    simp [higham11_2_bunchKaufmanSelectedTwoBlock,
      higham11_2_bunchKaufmanExactActive,
      higham11_2_bunchKaufmanFirstPermutedMatrix,
      higham11_2_bunchKaufmanFirstPerm, hbranch,
      higham11_2_firstIndex, hswap0]
  all_goals rfl

/-- A literal recursive execution trace for Algorithm 11.2.  Branch evidence
is an equality to the computed finite selector, never an assumed schedule.
The index in each constructor makes termination structural. -/
inductive Higham11ExactBunchKaufmanTrace :
    {n : ℕ} → (A : Higham11BunchKaufmanMatrix n) → Type
  | nil (A : Higham11BunchKaufmanMatrix 0) :
      Higham11ExactBunchKaufmanTrace A
  | noAction {n : ℕ} (A : Higham11BunchKaufmanMatrix (n + 1))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.noAction)
      (tail : Higham11ExactBunchKaufmanTrace
        (higham11_2_bunchKaufmanNoActionTail A)) :
      Higham11ExactBunchKaufmanTrace A
  | case1 {n : ℕ} (A : Higham11BunchKaufmanMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case1)
      (tail : Higham11ExactBunchKaufmanTrace
        (higham11_2_bunchKaufmanExactSchurOne A)) :
      Higham11ExactBunchKaufmanTrace A
  | case2 {n : ℕ} (A : Higham11BunchKaufmanMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case2)
      (tail : Higham11ExactBunchKaufmanTrace
        (higham11_2_bunchKaufmanExactSchurOne A)) :
      Higham11ExactBunchKaufmanTrace A
  | case3 {n : ℕ} (A : Higham11BunchKaufmanMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case3)
      (tail : Higham11ExactBunchKaufmanTrace
        (higham11_2_bunchKaufmanExactSchurOne A)) :
      Higham11ExactBunchKaufmanTrace A
  | case4 {n : ℕ} (A : Higham11BunchKaufmanMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
      (tail : Higham11ExactBunchKaufmanTrace
        (higham11_2_bunchKaufmanExactSchurTwo A)) :
      Higham11ExactBunchKaufmanTrace A

namespace Higham11ExactBunchKaufmanTrace

/-- The actual block-width schedule extracted from the recursive execution. -/
noncomputable def schedule : {n : ℕ} →
    {A : Higham11BunchKaufmanMatrix n} →
    Higham11ExactBunchKaufmanTrace A → PivotSchedule n
  | _, _, .nil _ => .nil
  | _, _, .noAction _ _ _ tail => tail.schedule.consOne
  | _, _, .case1 _ _ _ tail => tail.schedule.consOne
  | _, _, .case2 _ _ _ tail => tail.schedule.consOne
  | _, _, .case3 _ _ _ tail => tail.schedule.consOne
  | _, _, .case4 _ _ _ tail => tail.schedule.consTwo

/-- Block widths in execution order. -/
noncomputable def widths : {n : ℕ} →
    {A : Higham11BunchKaufmanMatrix n} →
    Higham11ExactBunchKaufmanTrace A → List ℕ
  | _, _, .nil _ => []
  | _, _, .noAction _ _ _ tail => 1 :: tail.widths
  | _, _, .case1 _ _ _ tail => 1 :: tail.widths
  | _, _, .case2 _ _ _ tail => 1 :: tail.widths
  | _, _, .case3 _ _ _ tail => 1 :: tail.widths
  | _, _, .case4 _ _ _ tail => 2 :: tail.widths

/-- Termination/accounting theorem: the recursively selected widths consume
exactly the dimension of the original active matrix. -/
@[simp] theorem widths_sum : {n : ℕ} →
    {A : Higham11BunchKaufmanMatrix n} →
    (trace : Higham11ExactBunchKaufmanTrace A) → trace.widths.sum = n
  | _, _, .nil _ => by simp [widths]
  | _, _, .noAction _ _ _ tail => by
      simp [widths, widths_sum tail]
      omega
  | _, _, .case1 _ _ _ tail => by
      simp [widths, widths_sum tail]
      omega
  | _, _, .case2 _ _ _ tail => by
      simp [widths, widths_sum tail]
      omega
  | _, _, .case3 _ _ _ tail => by
      simp [widths, widths_sum tail]
      omega
  | _, _, .case4 _ _ _ tail => by
      simp [widths, widths_sum tail]
      omega

/-- Every active matrix carried by the trace is symmetric. -/
theorem symmetric : {n : ℕ} → {A : Higham11BunchKaufmanMatrix n} →
    Higham11ExactBunchKaufmanTrace A → IsSymmetricFiniteMatrix A
  | _, _, .nil A => by intro i; exact Fin.elim0 i
  | _, _, .noAction _ hA _ _ => hA
  | _, _, .case1 _ hA _ _ => hA
  | _, _, .case2 _ hA _ _ => hA
  | _, _, .case3 _ hA _ _ => hA
  | _, _, .case4 _ hA _ _ => hA

/-- The first-stage map recorded by a trace is always a genuine permutation.
The no-action branch uses the identity; all other branches use precisely the
interchange computed by Algorithm 11.2. -/
noncomputable def firstPerm : {n : ℕ} →
    {A : Higham11BunchKaufmanMatrix n} →
    Higham11ExactBunchKaufmanTrace A → Equiv.Perm (Fin n)
  | _, _, .nil _ => Equiv.refl _
  | _, _, .noAction _ _ _ _ => Equiv.refl _
  | _, _, .case1 A _ _ _ =>
      higham11_2_bunchKaufmanFirstPerm (by omega)
        higham11_1_bunchParlettAlpha A
  | _, _, .case2 A _ _ _ =>
      higham11_2_bunchKaufmanFirstPerm (by omega)
        higham11_1_bunchParlettAlpha A
  | _, _, .case3 A _ _ _ =>
      higham11_2_bunchKaufmanFirstPerm (by omega)
        higham11_1_bunchParlettAlpha A
  | _, _, .case4 A _ _ _ =>
      higham11_2_bunchKaufmanFirstPerm (by omega)
        higham11_1_bunchParlettAlpha A

theorem firstPerm_injective {n : ℕ} {A : Higham11BunchKaufmanMatrix n}
    (trace : Higham11ExactBunchKaufmanTrace A) :
    Function.Injective trace.firstPerm :=
  trace.firstPerm.injective

/-- Symmetric permutation at the current stage preserves symmetry. -/
theorem firstPermuted_symmetric {n : ℕ}
    {A : Higham11BunchKaufmanMatrix n}
    (trace : Higham11ExactBunchKaufmanTrace A) :
    IsSymmetricFiniteMatrix (fun i j => A (trace.firstPerm i) (trace.firstPerm j)) := by
  intro i j
  exact trace.symmetric _ _

/-- The source no-action branch really has a zero leading off-diagonal column
and, by symmetry, a zero leading off-diagonal row. -/
theorem noAction_offDiagonal_zero {n : ℕ}
    (A : Higham11BunchKaufmanMatrix (n + 1))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.noAction) :
    ∀ j : Fin (n + 1),
      j ≠ higham11_2_firstIndex (by omega) →
      A j (higham11_2_firstIndex (by omega)) = 0 ∧
        A (higham11_2_firstIndex (by omega)) j = 0 := by
  intro j hj
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hω : higham11_2_bunchKaufmanOmegaOne (by omega) A = 0 := hcase
  have hbound := higham11_2_bunchKaufmanOmegaOne_spec (by omega) A j
  rw [hω] at hbound
  simp [hj] at hbound
  have hcol : A j (higham11_2_firstIndex (by omega)) = 0 := hbound
  exact ⟨hcol, by rw [hA _ _, hcol]⟩

end Higham11ExactBunchKaufmanTrace

/-- **Algorithm 11.2 recursive existence.**  Every finite symmetric matrix has
a structurally terminating trace whose branches are computed from the actual
active Schur complements. -/
theorem higham11_2_nonempty_exactBunchKaufmanTrace :
    ∀ {n : ℕ} (A : Higham11BunchKaufmanMatrix n),
      IsSymmetricFiniteMatrix A →
        Nonempty (Higham11ExactBunchKaufmanTrace A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro A hA
      cases n with
      | zero => exact ⟨.nil A⟩
      | succ m =>
          cases hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
              higham11_1_bunchParlettAlpha A with
          | noAction =>
              let S := higham11_2_bunchKaufmanNoActionTail A
              have hS : IsSymmetricFiniteMatrix S :=
                higham11_2_bunchKaufmanNoActionTail_symmetric A hA
              let tail : Higham11ExactBunchKaufmanTrace S :=
                Classical.choice (ih m (by omega) S hS)
              exact ⟨.noAction A hA hbranch tail⟩
          | case1 =>
              cases m with
              | zero =>
                  have hnone := higham11_2_bunchKaufmanFirstBranch_finOne A
                  rw [hnone] at hbranch
                  contradiction
              | succ k =>
                  let S := higham11_2_bunchKaufmanExactSchurOne A
                  have hS : IsSymmetricFiniteMatrix S :=
                    higham11_2_bunchKaufmanExactSchurOne_symmetric A hA
                  let tail : Higham11ExactBunchKaufmanTrace S :=
                    Classical.choice (ih (k + 1) (by omega) S hS)
                  exact ⟨.case1 A hA hbranch tail⟩
          | case2 =>
              cases m with
              | zero =>
                  have hnone := higham11_2_bunchKaufmanFirstBranch_finOne A
                  rw [hnone] at hbranch
                  contradiction
              | succ k =>
                  let S := higham11_2_bunchKaufmanExactSchurOne A
                  have hS : IsSymmetricFiniteMatrix S :=
                    higham11_2_bunchKaufmanExactSchurOne_symmetric A hA
                  let tail : Higham11ExactBunchKaufmanTrace S :=
                    Classical.choice (ih (k + 1) (by omega) S hS)
                  exact ⟨.case2 A hA hbranch tail⟩
          | case3 =>
              cases m with
              | zero =>
                  have hnone := higham11_2_bunchKaufmanFirstBranch_finOne A
                  rw [hnone] at hbranch
                  contradiction
              | succ k =>
                  let S := higham11_2_bunchKaufmanExactSchurOne A
                  have hS : IsSymmetricFiniteMatrix S :=
                    higham11_2_bunchKaufmanExactSchurOne_symmetric A hA
                  let tail : Higham11ExactBunchKaufmanTrace S :=
                    Classical.choice (ih (k + 1) (by omega) S hS)
                  exact ⟨.case3 A hA hbranch tail⟩
          | case4 =>
              cases m with
              | zero =>
                  have hnone := higham11_2_bunchKaufmanFirstBranch_finOne A
                  rw [hnone] at hbranch
                  contradiction
              | succ k =>
                  let S := higham11_2_bunchKaufmanExactSchurTwo A
                  have hS : IsSymmetricFiniteMatrix S :=
                    higham11_2_bunchKaufmanExactSchurTwo_symmetric A hA
                  let tail : Higham11ExactBunchKaufmanTrace S :=
                    Classical.choice (ih k (by omega) S hS)
                  exact ⟨.case4 A hA hbranch tail⟩

/-- Canonical (choice-fixed) exact recursive Algorithm 11.2 execution. -/
noncomputable def higham11_2_exactBunchKaufmanTrace {n : ℕ}
    (A : Higham11BunchKaufmanMatrix n) (hA : IsSymmetricFiniteMatrix A) :
    Higham11ExactBunchKaufmanTrace A :=
  Classical.choice (higham11_2_nonempty_exactBunchKaufmanTrace A hA)

/-- A stage-local certificate for the actual rounded two-step GEPP solve used
for a selected case-(4) pivot. -/
def higham11_2_SelectedTwoSolveCertificate (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Higham11BunchKaufmanMatrix n) : Prop :=
  ∀ z : Fin n → ℝ,
    ∃ ΔE : Fin 2 → Fin 2 → ℝ,
      higham11_5_twoByTwoPivotSolveStable fp.u 36
        (higham11_2_bunchKaufmanSelectedTwoBlock hn A) ΔE ∧
      ∀ p : Fin 2,
        ∑ q : Fin 2,
          (higham11_2_bunchKaufmanSelectedTwoBlock hn A p q + ΔE p q) *
            higham11_2_flSelectedTwoByTwoSolve fp hn A z q =
          z (Fin.cases (higham11_2_firstIndex hn)
            (fun _ => higham11_2_bunchKaufmanMaxRow hn A) p)

namespace Higham11ExactBunchKaufmanTrace

/-- Honest rounded run domain for all selected two-by-two stages: only the
computed second GEPP pivot is required to be nonzero. -/
noncomputable def twoSolveRunDomain (fp : FPModel) : {n : ℕ} →
    {A : Higham11BunchKaufmanMatrix n} →
    Higham11ExactBunchKaufmanTrace A → Prop
  | _, _, .nil _ => True
  | _, _, .noAction _ _ _ tail => tail.twoSolveRunDomain fp
  | _, _, .case1 _ _ _ tail => tail.twoSolveRunDomain fp
  | _, _, .case2 _ _ _ tail => tail.twoSolveRunDomain fp
  | _, _, .case3 _ _ _ tail => tail.twoSolveRunDomain fp
  | _, _, .case4 A _ _ tail =>
      higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0 ∧
        tail.twoSolveRunDomain fp

/-- Every case-(4) node in a trace carries the actual equation-(11.5)
certificate, recursively. -/
noncomputable def allSelectedTwoSolvesCertified (fp : FPModel) : {n : ℕ} →
    {A : Higham11BunchKaufmanMatrix n} →
    Higham11ExactBunchKaufmanTrace A → Prop
  | _, _, .nil _ => True
  | _, _, .noAction _ _ _ tail => tail.allSelectedTwoSolvesCertified fp
  | _, _, .case1 _ _ _ tail => tail.allSelectedTwoSolvesCertified fp
  | _, _, .case2 _ _ _ tail => tail.allSelectedTwoSolvesCertified fp
  | _, _, .case3 _ _ _ tail => tail.allSelectedTwoSolvesCertified fp
  | _, _, .case4 A _ _ tail =>
      higham11_2_SelectedTwoSolveCertificate fp (by omega) A ∧
        tail.allSelectedTwoSolvesCertified fp

/-- **Algorithm 11.2 / equation (11.5), recursive producer.**  Under the
standard floating-point smallness assumptions and the genuine non-breakdown
domain, every two-by-two pivot selected anywhere in the actual recursive trace
has the locally produced componentwise perturbation certificate.  No schedule,
branch choice, solve residual, or perturbation conclusion is assumed. -/
theorem allSelectedTwoSolvesCertified_of_runDomain (fp : FPModel)
    (hval9 : gammaValid fp 9) (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2) :
    ∀ {n : ℕ} {A : Higham11BunchKaufmanMatrix n}
      (trace : Higham11ExactBunchKaufmanTrace A),
      trace.twoSolveRunDomain fp → trace.allSelectedTwoSolvesCertified fp := by
  intro n A trace
  induction trace with
  | nil => simp [twoSolveRunDomain, allSelectedTwoSolvesCertified]
  | noAction A hA hbranch tail ih =>
      simpa [twoSolveRunDomain, allSelectedTwoSolvesCertified] using ih
  | case1 A hA hbranch tail ih =>
      simpa [twoSolveRunDomain, allSelectedTwoSolvesCertified] using ih
  | case2 A hA hbranch tail ih =>
      simpa [twoSolveRunDomain, allSelectedTwoSolvesCertified] using ih
  | case3 A hA hbranch tail ih =>
      simpa [twoSolveRunDomain, allSelectedTwoSolvesCertified] using ih
  | case4 A hA hbranch tail ih =>
      intro hrun
      rcases hrun with ⟨hsecond, htail⟩
      refine ⟨?_, ih htail⟩
      intro z
      exact higham11_2_flSelectedTwoByTwoSolve_higham115 fp hval9 hsmall9
        (by omega) A hA z hbranch hsecond

end Higham11ExactBunchKaufmanTrace

end NumStability
