/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
-/

import NumStability.Source.Higham.Chapter12.IterativeRefinement
import NumStability.Algorithms.HighamChapter9DoolittleClosure

/-!
# LU-factorization solver weights

Higham Theorem 9.4 to Chapter 12 solver-weight results for generic, row-pivoted,
and completely pivoted LU backward-error certificates.
-/

namespace NumStability

open scoped BigOperators

/-! All source references are to N. J. Higham, *Accuracy and Stability of
Numerical Algorithms*, 2nd ed. (SIAM, 2002), Theorem 9.4 and Chapter 12,
equations (12.1) and (12.6), printed p. 234. -/

/-- **Equation (12.6)** for arbitrary computed LU factors. -/
noncomputable def higham12_6_luW {n : ℕ} (fp : FPModel)
    (L_hat U_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    (((3 * n : ℕ) : ℝ) /
        (1 - ((3 * n : ℕ) : ℝ) * fp.u)) *
      ∑ k : Fin n, |L_hat i k| * |U_hat k j|

/-- Multiplication by unit roundoff turns the generic equation-(12.6) weight
into the `gamma_(3n) |L_hat| |U_hat|` envelope of Theorem 9.4. -/
theorem higham12_6_u_mul_luW_eq {n : ℕ} (fp : FPModel)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (hn3 : gammaValid fp (3 * n)) (i j : Fin n) :
    fp.u * higham12_6_luW fp L_hat U_hat i j =
      gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
  have hden : 1 - ((3 * n : ℕ) : ℝ) * fp.u ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr hn3
  simp only [higham12_6_luW, gamma]
  field_simp [hden]

/-- **Theorem 9.4 -> equations (12.6) and (12.1), generic LU form.** -/
theorem higham12_6_lu_solve_SolverWBound
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    higham12_1_SolverWBound n A (higham12_6_luW fp L_hat U_hat)
      fp.u b x_hat := by
  dsimp only
  obtain ⟨DeltaA, hDeltaA, hsolve⟩ :=
    higham9_4_lu_solve_backward_error fp n A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
  refine ⟨DeltaA, ?_, hsolve⟩
  intro i j
  calc
    |DeltaA i j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hDeltaA i j
    _ = fp.u * higham12_6_luW fp L_hat U_hat i j :=
      (higham12_6_u_mul_luW_eq fp L_hat U_hat hn3 i j).symm

/-- Equation-(12.6) weight in the original row ordering for a row-pivoted
factorization. -/
noncomputable def higham12_6_rowPermutedLUW {n : ℕ} (fp : FPModel)
    (L_hat U_hat : Fin n → Fin n → ℝ) (eSigma : Fin n ≃ Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j => higham12_6_luW fp L_hat U_hat (eSigma.symm i) j

/-- **Problem 9.4 -> equations (12.6) and (12.1), row-pivoted form.**
The right-hand side is permuted for the triangular solves, while both the
returned perturbation and its weight are expressed in the original row
ordering. -/
theorem higham12_6_rowPermuted_lu_solve_SolverWBound
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n) (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma
      (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.perm
    higham12_1_SolverWBound n A
      (higham12_6_rowPermutedLUW fp L_hat U_hat eSigma) fp.u b x_hat := by
  dsimp only
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.perm
  obtain ⟨DeltaA, hDeltaA, hsolve⟩ :=
    higham_problem9_4_permuted_lu_solve_backward_error
      fp n A L_hat U_hat sigma b hL_diag hU_diag hLU hn hn3
  refine ⟨DeltaA, ?_, hsolve⟩
  intro i j
  have hsigma : sigma (eSigma.symm i) = i := by
    change eSigma (eSigma.symm i) = i
    exact Equiv.apply_symm_apply eSigma i
  calc
    |DeltaA i j| = |DeltaA (sigma (eSigma.symm i)) j| := by rw [hsigma]
    _ ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat (eSigma.symm i) k| * |U_hat k j| :=
      hDeltaA (eSigma.symm i) j
    _ = fp.u * higham12_6_rowPermutedLUW fp L_hat U_hat eSigma i j := by
      simpa [higham12_6_rowPermutedLUW] using
        (higham12_6_u_mul_luW_eq fp L_hat U_hat hn3 (eSigma.symm i) j).symm

/-- Equation-(12.6) weight in the original row and column orderings for a
complete-pivoted factorization. -/
noncomputable def higham12_6_completePermutedLUW {n : ℕ} (fp : FPModel)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (eSigma eTau : Fin n ≃ Fin n) : Fin n → Fin n → ℝ :=
  fun i j =>
    higham12_6_luW fp L_hat U_hat (eSigma.symm i) (eTau.symm j)

/-- **Problem 9.4 -> equations (12.6) and (12.1), complete-pivoted form.**
The theorem returns the solution, perturbation, and componentwise solver
weight in the original row and column orderings. -/
theorem higham12_6_completePermuted_lu_solve_SolverWBound
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma tau : Fin n → Fin n) (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat
      sigma tau (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let z_hat := fl_backSub fp n U_hat y_hat
    let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.2.perm
    let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau hLU.1
    let x_hat : Fin n → ℝ := fun j => z_hat (eTau.symm j)
    higham12_1_SolverWBound n A
      (higham12_6_completePermutedLUW fp L_hat U_hat eSigma eTau)
      fp.u b x_hat := by
  dsimp only
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.2.perm
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau hLU.1
  obtain ⟨DeltaA, hDeltaA, hsolve⟩ :=
    higham_problem9_4_complete_permuted_lu_solve_backward_error
      fp n A L_hat U_hat sigma tau b hL_diag hU_diag hLU hn hn3
  refine ⟨DeltaA, ?_, hsolve⟩
  intro i j
  have hsigma : sigma (eSigma.symm i) = i := by
    change eSigma (eSigma.symm i) = i
    exact Equiv.apply_symm_apply eSigma i
  have htau : tau (eTau.symm j) = j := by
    change eTau (eTau.symm j) = j
    exact Equiv.apply_symm_apply eTau j
  calc
    |DeltaA i j| =
        |DeltaA (sigma (eSigma.symm i)) (tau (eTau.symm j))| := by
          rw [hsigma, htau]
    _ ≤ gamma fp (3 * n) *
        ∑ k : Fin n,
          |L_hat (eSigma.symm i) k| * |U_hat k (eTau.symm j)| :=
      hDeltaA (eSigma.symm i) (eTau.symm j)
    _ = fp.u *
        higham12_6_completePermutedLUW fp L_hat U_hat eSigma eTau i j := by
      simpa [higham12_6_completePermutedLUW] using
        (higham12_6_u_mul_luW_eq fp L_hat U_hat hn3
          (eSigma.symm i) (eTau.symm j)).symm

end NumStability
