/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import NumStability.Algorithms.QR.Higham19Alg12MGSRounded
import NumStability.Algorithms.LeastSquares.Higham20CrossProductExample

namespace NumStability

open scoped BigOperators Matrix

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-!
# Higham Problem 19.10: the Lauchli CGS/MGS example

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Problem 19.10 (p. 379) and its Appendix-A solution (p. 564), applies
classical and modified Gram--Schmidt to the `4 x 3` Lauchli matrix under the
rounding event `fl(1 + epsilon^2) = 1`.

The displayed `Q` factors are recorded literally below.  We prove their exact
Gram defects, realize them with the repository's literal rounded CGS/MGS
executors in an explicit standard-model trace, and separately record why the
single rounding event does not determine an executor trace for an arbitrary
`FPModel` (the other primitive roundings are unconstrained).
-/

/-- The `4 x 3` Lauchli matrix printed in Problem 19.10. -/
def higham19Problem19_10Lauchli (epsilon : Real) :
    Fin 4 -> Fin 3 -> Real :=
  !![(1 : Real), 1, 1;
     epsilon, 0, 0;
     0, epsilon, 0;
     0, 0, epsilon]

/-- The CGS factor displayed in the Appendix-A solution to Problem 19.10. -/
def higham19Problem19_10QCGS (epsilon : Real) :
    Fin 4 -> Fin 3 -> Real :=
  !![(1 : Real), 0, 0;
     epsilon, -(1 / Real.sqrt 2), -(1 / Real.sqrt 2);
     0, 1 / Real.sqrt 2, 0;
     0, 0, 1 / Real.sqrt 2]

/-- The MGS factor displayed in the Appendix-A solution to Problem 19.10. -/
def higham19Problem19_10QMGS (epsilon : Real) :
    Fin 4 -> Fin 3 -> Real :=
  !![(1 : Real), 0, 0;
     epsilon, -(1 / Real.sqrt 2), -(1 / Real.sqrt 6);
     0, 1 / Real.sqrt 2, -(1 / Real.sqrt 6);
     0, 0, Real.sqrt (2 / 3)]

/-- Euclidean inner product of two columns of a four-row matrix. -/
def higham19Problem19_10ColumnDot
    (Q : Fin 4 -> Fin 3 -> Real) (j k : Fin 3) : Real :=
  Finset.univ.sum fun i : Fin 4 => Q i j * Q i k

/-- Exact Gram matrix of the Lauchli family: `A^T A = epsilon^2 I + 11^T`.
This is the finite-dimensional spectral calculation behind the condition
number formula in the Appendix-A solution. -/
theorem higham19_problem19_10_lauchli_gram (epsilon : Real) (i j : Fin 3) :
    rectangularGram (higham19Problem19_10Lauchli epsilon) i j =
      epsilon ^ 2 * idMatrix 3 i j + 1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rectangularGram, matMulRect, finiteTranspose,
      higham19Problem19_10Lauchli, idMatrix, Fin.sum_univ_four] <;>
    ring

/-- The all-ones direction is the largest Gram eigendirection, with
eigenvalue `epsilon^2 + 3`. -/
theorem higham19_problem19_10_lauchli_gram_max_eigenpair
    (epsilon : Real) :
    matMulVec 3 (rectangularGram (higham19Problem19_10Lauchli epsilon))
        (fun _ : Fin 3 => (1 : Real)) =
      fun _ : Fin 3 => epsilon ^ 2 + 3 := by
  funext i
  fin_cases i <;>
    simp [matMulVec, higham19_problem19_10_lauchli_gram,
      idMatrix, Fin.sum_univ_three] <;>
    ring

/-- A sum-zero direction is a smallest Gram eigendirection, with eigenvalue
`epsilon^2`. -/
theorem higham19_problem19_10_lauchli_gram_min_eigenpair
    (epsilon : Real) :
    matMulVec 3 (rectangularGram (higham19Problem19_10Lauchli epsilon))
        ![(1 : Real), -1, 0] =
      fun i : Fin 3 => epsilon ^ 2 * ![(1 : Real), -1, 0] i := by
  funext i
  fin_cases i <;>
    simp [matMulVec, higham19_problem19_10_lauchli_gram,
      idMatrix, Fin.sum_univ_three]

/-- Coordinate action of the rank-one Gram perturbation. -/
theorem higham19_problem19_10_lauchli_gram_action
    (epsilon : Real) (x : Fin 3 -> Real) (i : Fin 3) :
    matMulVec 3 (rectangularGram (higham19Problem19_10Lauchli epsilon)) x i =
      epsilon ^ 2 * x i + Finset.univ.sum x := by
  fin_cases i <;>
    simp [matMulVec, higham19_problem19_10_lauchli_gram,
      idMatrix, Fin.sum_univ_three] <;>
    ring

/-- Complete Gram-spectrum classification.  Every real eigenvalue of the
Lauchli Gram matrix is either `epsilon^2` (the two-dimensional sum-zero
space) or `epsilon^2+3` (the all-ones direction). -/
theorem higham19_problem19_10_lauchli_gram_eigenvalue_cases
    (epsilon lambda : Real) (x : Fin 3 -> Real) (hx : x ≠ 0)
    (heigen :
      matMulVec 3 (rectangularGram (higham19Problem19_10Lauchli epsilon)) x =
        fun i => lambda * x i) :
    lambda = epsilon ^ 2 ∨ lambda = epsilon ^ 2 + 3 := by
  let s : Real := Finset.univ.sum x
  have hcoord : ∀ i : Fin 3,
      epsilon ^ 2 * x i + s = lambda * x i := by
    intro i
    have hi := congrFun heigen i
    simpa [s, higham19_problem19_10_lauchli_gram_action] using hi
  have hsum : (epsilon ^ 2 + 3) * s = lambda * s := by
    calc
      (epsilon ^ 2 + 3) * s =
          (epsilon ^ 2 * x 0 + s) +
            (epsilon ^ 2 * x 1 + s) +
              (epsilon ^ 2 * x 2 + s) := by
            simp [s, Fin.sum_univ_three]
            ring
      _ = lambda * x 0 + lambda * x 1 + lambda * x 2 := by
            rw [hcoord 0, hcoord 1, hcoord 2]
      _ = lambda * s := by
            simp [s, Fin.sum_univ_three]
            ring
  by_cases hs : s = 0
  · left
    have hexists : ∃ i : Fin 3, x i ≠ 0 := by
      by_contra hnot
      push_neg at hnot
      apply hx
      funext i
      exact hnot i
    obtain ⟨i, hi⟩ := hexists
    have hprod : (epsilon ^ 2 - lambda) * x i = 0 := by
      have := hcoord i
      rw [hs] at this
      nlinarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hi)).symm
  · right
    have hprod : (epsilon ^ 2 + 3 - lambda) * s = 0 := by
      nlinarith [hsum]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hs)).symm

/-- The two last CGS columns have the source's order-one defect `1/2`. -/
theorem higham19_problem19_10_cgs_q2_dot_q3 (epsilon : Real) :
    higham19Problem19_10ColumnDot
        (higham19Problem19_10QCGS epsilon) (1 : Fin 3) (2 : Fin 3) =
      1 / 2 := by
  have hsqrt2 : Real.sqrt (2 : Real) ≠ 0 := by positivity
  have hsqrt2_sq : Real.sqrt (2 : Real) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [higham19Problem19_10ColumnDot, Fin.sum_univ_four]
  simp [higham19Problem19_10QCGS]
  field_simp [hsqrt2]
  nlinarith

/-- The first and second MGS columns have inner product `-epsilon/sqrt 2`. -/
theorem higham19_problem19_10_mgs_q1_dot_q2 (epsilon : Real) :
    higham19Problem19_10ColumnDot
        (higham19Problem19_10QMGS epsilon) (0 : Fin 3) (1 : Fin 3) =
      -(epsilon / Real.sqrt 2) := by
  rw [higham19Problem19_10ColumnDot, Fin.sum_univ_four]
  simp [higham19Problem19_10QMGS]
  ring

/-- The first and third MGS columns have inner product `-epsilon/sqrt 6`. -/
theorem higham19_problem19_10_mgs_q1_dot_q3 (epsilon : Real) :
    higham19Problem19_10ColumnDot
        (higham19Problem19_10QMGS epsilon) (0 : Fin 3) (2 : Fin 3) =
      -(epsilon / Real.sqrt 6) := by
  rw [higham19Problem19_10ColumnDot, Fin.sum_univ_four]
  simp [higham19Problem19_10QMGS]
  ring

/-- The second and third MGS columns remain exactly orthogonal. -/
theorem higham19_problem19_10_mgs_q2_dot_q3 (epsilon : Real) :
    higham19Problem19_10ColumnDot
        (higham19Problem19_10QMGS epsilon) (1 : Fin 3) (2 : Fin 3) = 0 := by
  rw [higham19Problem19_10ColumnDot, Fin.sum_univ_four]
  simp [higham19Problem19_10QMGS]

/-- The three distinct MGS column pairs satisfy the precise Appendix-A
orthogonality estimate.  Stating the three unordered pairs avoids hiding the
two different sharp values (`epsilon/sqrt 2`, `epsilon/sqrt 6`, and zero)
behind a matrix norm. -/
theorem higham19_problem19_10_mgs_pairwise_bounds
    (epsilon : Real) (hepsilon : 0 ≤ epsilon) :
    |higham19Problem19_10ColumnDot
        (higham19Problem19_10QMGS epsilon) (0 : Fin 3) (1 : Fin 3)| =
        epsilon / Real.sqrt 2 ∧
    |higham19Problem19_10ColumnDot
        (higham19Problem19_10QMGS epsilon) (0 : Fin 3) (2 : Fin 3)| ≤
        epsilon / Real.sqrt 2 ∧
    |higham19Problem19_10ColumnDot
        (higham19Problem19_10QMGS epsilon) (1 : Fin 3) (2 : Fin 3)| = 0 := by
  have hsqrt2 : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt6 : 0 < Real.sqrt (6 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_le : Real.sqrt (2 : Real) ≤ Real.sqrt 6 :=
    Real.sqrt_le_sqrt (by norm_num)
  constructor
  · rw [higham19_problem19_10_mgs_q1_dot_q2]
    rw [abs_neg, abs_div, abs_of_nonneg hepsilon, abs_of_pos hsqrt2]
  constructor
  · rw [higham19_problem19_10_mgs_q1_dot_q3]
    rw [abs_neg, abs_div, abs_of_nonneg hepsilon, abs_of_pos hsqrt6]
    rw [div_le_div_iff₀ hsqrt6 hsqrt2]
    exact mul_le_mul_of_nonneg_left hsqrt_le hepsilon
  · rw [higham19_problem19_10_mgs_q2_dot_q3, abs_zero]

/-- Source formula for the condition number of the Lauchli matrix.  The
spectral calculation is encoded as its closed form so that the asymptotic
counterexample below does not silently replace `kappa_2(A)` by `1/epsilon`. -/
noncomputable def higham19Problem19_10SourceKappa (epsilon : Real) : Real :=
  Real.sqrt (3 + epsilon ^ 2) / epsilon

/-- The closed-form condition number is exactly the square-root ratio of the
two Gram eigenvalues proved above. -/
theorem higham19_problem19_10_sourceKappa_eq_gram_eigenvalue_ratio
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    higham19Problem19_10SourceKappa epsilon =
      Real.sqrt (epsilon ^ 2 + 3) / Real.sqrt (epsilon ^ 2) := by
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hepsilon]
  simp only [higham19Problem19_10SourceKappa]
  rw [show 3 + epsilon ^ 2 = epsilon ^ 2 + 3 by ring]

/-!
## An executable source trace

The rounding model is the symbolic model already used for Higham's analogous
cross-product example: only the sensitive addition `1 + epsilon^2` rounds to
`1`; all other primitive operations are exact.  Taking `u = 2 epsilon^2`
provides the required strict model budget for every positive `epsilon`.
-/

/-- The explicit standard-model trace used to execute Problem 19.10. -/
noncomputable def higham19Problem19_10FP (epsilon : Real)
    (hepsilon : 0 < epsilon) : FPModel :=
  higham20CrossProductExampleFP epsilon (2 * epsilon ^ 2) (by
    nlinarith [sq_pos_of_pos hepsilon])

theorem higham19_problem19_10_fp_u (epsilon : Real)
    (hepsilon : 0 < epsilon) :
    (higham19Problem19_10FP epsilon hepsilon).u = 2 * epsilon ^ 2 := rfl

/-- The source implication `epsilon ≤ sqrt u` holds for the explicit trace. -/
theorem higham19_problem19_10_epsilon_le_sqrt_u (epsilon : Real)
    (hepsilon : 0 < epsilon) :
    epsilon ≤ Real.sqrt (higham19Problem19_10FP epsilon hepsilon).u := by
  rw [higham19_problem19_10_fp_u]
  rw [Real.le_sqrt (le_of_lt hepsilon) (by positivity)]
  nlinarith [sq_nonneg epsilon]

/-- With `u = 2 epsilon^2`, the source product `kappa_2(A)u` is exactly
`2 epsilon sqrt(3+epsilon^2)` and therefore tends to zero with `epsilon`. -/
theorem higham19_problem19_10_kappa_mul_u (epsilon : Real)
    (hepsilon : 0 < epsilon) :
    higham19Problem19_10SourceKappa epsilon *
        (higham19Problem19_10FP epsilon hepsilon).u =
      2 * epsilon * Real.sqrt (3 + epsilon ^ 2) := by
  rw [higham19_problem19_10_fp_u]
  unfold higham19Problem19_10SourceKappa
  field_simp [ne_of_gt hepsilon]

/-- On the small-parameter range used by the example, the condition product
has the elementary upper bound `kappa_2(A)u ≤ 4 epsilon`. -/
theorem higham19_problem19_10_kappa_mul_u_le
    (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) :
    higham19Problem19_10SourceKappa epsilon *
        (higham19Problem19_10FP epsilon hepsilon).u ≤ 4 * epsilon := by
  rw [higham19_problem19_10_kappa_mul_u epsilon hepsilon]
  have hsqrt : Real.sqrt (3 + epsilon ^ 2) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [sq_nonneg epsilon]
  nlinarith [Real.sqrt_nonneg (3 + epsilon ^ 2)]

/-- Formal no-constant consequence used by the Chapter-19 prose: for every
fixed nonnegative coefficient `C`, the order-one CGS defect `1/2` exceeds
`C * kappa_2(A) * u` for a positive member of the executable Lauchli family. -/
theorem higham19_problem19_10_no_uniform_linear_cgs_bound
    (C : Real) (hC : 0 ≤ C) :
    ∃ epsilon : Real, ∃ hepsilon : 0 < epsilon,
      epsilon < 1 ∧
      C * (higham19Problem19_10SourceKappa epsilon *
          (higham19Problem19_10FP epsilon hepsilon).u) < 1 / 2 := by
  let epsilon : Real := 1 / (8 * (C + 1))
  have hden : 0 < 8 * (C + 1) := by positivity
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hepsilon_one : epsilon < 1 := by
    dsimp [epsilon]
    rw [div_lt_one hden]
    nlinarith
  refine ⟨epsilon, hepsilon, hepsilon_one, ?_⟩
  have hkappa := higham19_problem19_10_kappa_mul_u_le
    epsilon hepsilon hepsilon_one.le
  have hscaled :
      C * (higham19Problem19_10SourceKappa epsilon *
        (higham19Problem19_10FP epsilon hepsilon).u) ≤ C * (4 * epsilon) :=
    mul_le_mul_of_nonneg_left hkappa hC
  have hstrict : C * (4 * epsilon) < 1 / 2 := by
    have hCp : 0 < C + 1 := by linarith
    calc
      C * (4 * epsilon) = C / (2 * (C + 1)) := by
        dsimp [epsilon]
        field_simp [ne_of_gt hCp]
        ring_nf
      _ < 1 / 2 := by
        rw [div_lt_div_iff₀ (by positivity : 0 < 2 * (C + 1))
          (by norm_num : (0 : Real) < 2)]
        nlinarith
  exact lt_of_le_of_lt hscaled hstrict

/-- The source rounding event holds in the executable trace. -/
theorem higham19_problem19_10_rounding_event (epsilon : Real)
    (hepsilon : 0 < epsilon) :
    (higham19Problem19_10FP epsilon hepsilon).fl_add 1
        ((higham19Problem19_10FP epsilon hepsilon).fl_mul epsilon epsilon) = 1 := by
  simp [higham19Problem19_10FP, higham20CrossProductExampleFP, pow_two]

/-- Expected rounded CGS state after the first column.  Naming the three
finite states keeps the executable certificate small enough for the kernel to
check without normalizing the whole recursion independently at every entry. -/
private def higham19Problem19_10CGSStage1Q (epsilon : Real) :
    Fin 4 -> Fin 3 -> Real :=
  !![(1 : Real), 0, 0;
     epsilon, 0, 0;
     0, 0, 0;
     0, 0, 0]

private def higham19Problem19_10CGSStage1R : Fin 3 -> Fin 3 -> Real :=
  !![(1 : Real), 0, 0;
     0, 0, 0;
     0, 0, 0]

/-- Expected rounded CGS state after the second column. -/
private def higham19Problem19_10CGSStage2Q (epsilon : Real) :
    Fin 4 -> Fin 3 -> Real :=
  !![(1 : Real), 0, 0;
     epsilon, -(1 / Real.sqrt 2), 0;
     0, 1 / Real.sqrt 2, 0;
     0, 0, 0]

private def higham19Problem19_10CGSStage2R (epsilon : Real) :
    Fin 3 -> Fin 3 -> Real :=
  !![(1 : Real), 1, 0;
     0, epsilon * Real.sqrt 2, 0;
     0, 0, 0]

/-- Expected final rounded CGS triangular factor. -/
private def higham19Problem19_10CGSStage3R (epsilon : Real) :
    Fin 3 -> Fin 3 -> Real :=
  !![(1 : Real), 1, 1;
     0, epsilon * Real.sqrt 2, 0;
     0, 0, epsilon * Real.sqrt 2]

private def higham19Problem19_10CGSStage2Roff :
    Fin 3 -> Fin 3 -> Real :=
  !![(1 : Real), 1, 0;
     0, 0, 0;
     0, 0, 0]

private def higham19Problem19_10CGSStage2Residual (epsilon : Real) :
    Fin 4 -> Real :=
  ![(0 : Real), -epsilon, epsilon, 0]

private def higham19Problem19_10CGSStage3Roff (epsilon : Real) :
    Fin 3 -> Fin 3 -> Real :=
  !![(1 : Real), 1, 1;
     0, epsilon * Real.sqrt 2, 0;
     0, 0, 0]

private def higham19Problem19_10CGSStage3Residual (epsilon : Real) :
    Fin 4 -> Real :=
  ![(0 : Real), -epsilon, 0, epsilon]

private theorem higham19_problem19_10_cgs_residual_entry_zero
    (epsilon : Real) (hepsilon : 0 < epsilon) (i : Fin 4) :
    flCGSResidualEntry (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (fun _ _ => 0) (fun _ _ => 0) i (0 : Fin 3) =
      higham19Problem19_10Lauchli epsilon i (0 : Fin 3) := by
  fin_cases i <;>
    norm_num [flCGSResidualEntry, flCGSCoeff, flCGSRow,
      fl_dotProduct, Fin.foldl_succ, higham19Problem19_10FP,
      higham20CrossProductExampleFP, higham19Problem19_10Lauchli]

private theorem higham19_problem19_10_cgs_norm_zero
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    fl_norm2 (higham19Problem19_10FP epsilon hepsilon) 4
        (flCGSResidual (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon)
          (fun _ _ => 0) (fun _ _ => 0) (0 : Fin 3)) = 1 := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hres :
      flCGSResidual (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon)
          (fun _ _ => 0) (fun _ _ => 0) (0 : Fin 3) =
        fun i => higham19Problem19_10Lauchli epsilon i (0 : Fin 3) := by
    funext i
    exact higham19_problem19_10_cgs_residual_entry_zero epsilon hepsilon i
  rw [hres]
  norm_num [fl_norm2, fl_norm2Sq, fl_dotProduct, Fin.foldl_succ,
    higham19Problem19_10FP, higham20CrossProductExampleFP,
    higham19Problem19_10Lauchli, pow_two, hepsilon_ne]

private theorem higham19_problem19_10_cgs_roff_zero
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flCGSRoff (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (fun _ _ => 0) (fun _ _ => 0) (0 : Fin 3) =
      fun _ _ => 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flCGSRoff]

private theorem higham19_problem19_10_cgs_step_zero
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flCGSStep (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        ((fun _ _ => 0), (fun _ _ => 0)) (0 : Fin 3) =
      (higham19Problem19_10CGSStage1Q epsilon,
        higham19Problem19_10CGSStage1R) := by
  simp only [flCGSStep]
  rw [higham19_problem19_10_cgs_roff_zero epsilon hepsilon]
  rw [higham19_problem19_10_cgs_norm_zero epsilon hepsilon]
  apply Prod.ext
  · funext i j
    change
      (if j = (0 : Fin 3) then
          (higham19Problem19_10FP epsilon hepsilon).fl_div
            (flCGSResidualEntry
              (higham19Problem19_10FP epsilon hepsilon)
              (higham19Problem19_10Lauchli epsilon)
              (fun _ _ => 0) (fun _ _ => 0) i (0 : Fin 3)) 1
        else 0) = higham19Problem19_10CGSStage1Q epsilon i j
    rw [higham19_problem19_10_cgs_residual_entry_zero epsilon hepsilon i]
    fin_cases i <;> fin_cases j <;>
      norm_num [higham19Problem19_10FP,
        higham20CrossProductExampleFP, higham19Problem19_10Lauchli,
        higham19Problem19_10CGSStage1Q]
    all_goals rfl
  · funext i j
    change
      (if j = (0 : Fin 3) then
          if i = (0 : Fin 3) then 1 else 0
        else 0) = higham19Problem19_10CGSStage1R i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham19Problem19_10CGSStage1R]

private theorem higham19_problem19_10_cgs_stage2_roff
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flCGSRoff (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (higham19Problem19_10CGSStage1Q epsilon)
        higham19Problem19_10CGSStage1R (1 : Fin 3) =
      higham19Problem19_10CGSStage2Roff := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flCGSRoff, fl_dotProduct, Fin.foldl_succ,
      higham19Problem19_10FP, higham20CrossProductExampleFP,
      higham19Problem19_10Lauchli,
      higham19Problem19_10CGSStage1Q,
      higham19Problem19_10CGSStage1R,
      higham19Problem19_10CGSStage2Roff]

private theorem higham19_problem19_10_cgs_stage2_residual_entry
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) (i : Fin 4) :
    flCGSResidualEntry (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (higham19Problem19_10CGSStage1Q epsilon)
        higham19Problem19_10CGSStage2Roff i (1 : Fin 3) =
      higham19Problem19_10CGSStage2Residual epsilon i := by
  have hepsilon_sq_ne_one : epsilon ^ 2 ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hneg_one_ne_sq : (-1 : Real) ≠ epsilon ^ 2 := by
    nlinarith [sq_nonneg epsilon]
  fin_cases i <;>
    norm_num [flCGSResidualEntry, flCGSCoeff, flCGSRow,
      fl_dotProduct, Fin.foldl_succ, higham19Problem19_10FP,
      higham20CrossProductExampleFP, higham19Problem19_10Lauchli,
      higham19Problem19_10CGSStage1Q,
      higham19Problem19_10CGSStage2Roff,
      higham19Problem19_10CGSStage2Residual, hepsilon_sq_ne_one,
      hneg_one_ne_sq]
  case «0» => rfl
  case «2» =>
    simp [ne_of_lt hepsilon_one]
    rfl
  case «3» => rfl

private theorem higham19_problem19_10_cgs_stage2_norm
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    fl_norm2 (higham19Problem19_10FP epsilon hepsilon) 4
        (flCGSResidual (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon)
          (higham19Problem19_10CGSStage1Q epsilon)
          higham19Problem19_10CGSStage2Roff (1 : Fin 3)) =
      epsilon * Real.sqrt 2 := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hepsilon_sq_ne_one : epsilon ^ 2 ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hepsilon_mul_self_ne_one : epsilon * epsilon ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hres :
      flCGSResidual (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon)
          (higham19Problem19_10CGSStage1Q epsilon)
          higham19Problem19_10CGSStage2Roff (1 : Fin 3) =
        higham19Problem19_10CGSStage2Residual epsilon := by
    funext i
    exact higham19_problem19_10_cgs_stage2_residual_entry
      epsilon hepsilon hepsilon_one i
  rw [hres]
  have hsqrt : Real.sqrt (2 * epsilon ^ 2) =
      epsilon * Real.sqrt 2 := by
    rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2),
      Real.sqrt_sq_eq_abs, abs_of_pos hepsilon]
    ring
  have hsq :
      fl_norm2Sq (higham19Problem19_10FP epsilon hepsilon) 4
          (higham19Problem19_10CGSStage2Residual epsilon) =
        2 * epsilon ^ 2 := by
    norm_num [fl_norm2Sq, fl_dotProduct, Fin.foldl_succ,
      higham19Problem19_10FP, higham20CrossProductExampleFP,
      higham19Problem19_10CGSStage2Residual, pow_two,
      hepsilon_ne, hepsilon_sq_ne_one, hepsilon_mul_self_ne_one]
    ring
  rw [fl_norm2, hsq]
  exact hsqrt

private theorem higham19_problem19_10_cgs_step_one
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flCGSStep (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (higham19Problem19_10CGSStage1Q epsilon,
          higham19Problem19_10CGSStage1R) (1 : Fin 3) =
      (higham19Problem19_10CGSStage2Q epsilon,
        higham19Problem19_10CGSStage2R epsilon) := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hsqrt_two_ne : Real.sqrt (2 : Real) ≠ 0 := by positivity
  simp only [flCGSStep]
  rw [higham19_problem19_10_cgs_stage2_roff epsilon hepsilon]
  rw [higham19_problem19_10_cgs_stage2_norm
    epsilon hepsilon hepsilon_one]
  apply Prod.ext
  · funext i j
    change
      (if j = (1 : Fin 3) then
          (higham19Problem19_10FP epsilon hepsilon).fl_div
            (flCGSResidualEntry
              (higham19Problem19_10FP epsilon hepsilon)
              (higham19Problem19_10Lauchli epsilon)
              (higham19Problem19_10CGSStage1Q epsilon)
              higham19Problem19_10CGSStage2Roff i (1 : Fin 3))
            (epsilon * Real.sqrt 2)
        else higham19Problem19_10CGSStage1Q epsilon i j) =
          higham19Problem19_10CGSStage2Q epsilon i j
    rw [higham19_problem19_10_cgs_stage2_residual_entry
      epsilon hepsilon hepsilon_one i]
    fin_cases i <;> fin_cases j <;>
      norm_num [higham19Problem19_10FP,
        higham20CrossProductExampleFP,
        higham19Problem19_10CGSStage1Q,
        higham19Problem19_10CGSStage2Q,
        higham19Problem19_10CGSStage2Residual]
    all_goals field_simp [hepsilon_ne, hsqrt_two_ne]
  · funext i j
    change
      (if j = (1 : Fin 3) then
          if i = (1 : Fin 3) then epsilon * Real.sqrt 2
          else higham19Problem19_10CGSStage2Roff i j
        else higham19Problem19_10CGSStage1R i j) =
          higham19Problem19_10CGSStage2R epsilon i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham19Problem19_10CGSStage1R,
        higham19Problem19_10CGSStage2Roff,
        higham19Problem19_10CGSStage2R]

private theorem higham19_problem19_10_cgs_stage3_roff
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flCGSRoff (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (higham19Problem19_10CGSStage2Q epsilon)
        (higham19Problem19_10CGSStage2R epsilon) (2 : Fin 3) =
      higham19Problem19_10CGSStage3Roff epsilon := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flCGSRoff, fl_dotProduct, Fin.foldl_succ,
      higham19Problem19_10FP, higham20CrossProductExampleFP,
      higham19Problem19_10Lauchli,
      higham19Problem19_10CGSStage2Q,
      higham19Problem19_10CGSStage2R,
      higham19Problem19_10CGSStage3Roff]
  all_goals simp_all

private theorem higham19_problem19_10_cgs_stage3_residual_entry
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) (i : Fin 4) :
    flCGSResidualEntry (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (higham19Problem19_10CGSStage2Q epsilon)
        (higham19Problem19_10CGSStage3Roff epsilon) i (2 : Fin 3) =
      higham19Problem19_10CGSStage3Residual epsilon i := by
  have hepsilon_sq_ne_one : epsilon ^ 2 ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hneg_one_ne_sq : (-1 : Real) ≠ epsilon ^ 2 := by
    nlinarith [sq_nonneg epsilon]
  fin_cases i <;>
    norm_num [flCGSResidualEntry, flCGSCoeff, flCGSRow,
      fl_dotProduct, Fin.foldl_succ, higham19Problem19_10FP,
      higham20CrossProductExampleFP, higham19Problem19_10Lauchli,
      higham19Problem19_10CGSStage2Q,
      higham19Problem19_10CGSStage3Roff,
      higham19Problem19_10CGSStage3Residual, hepsilon_sq_ne_one,
      hneg_one_ne_sq]
  case «1» =>
    intro h _
    exact h.symm
  case «3» =>
    simp [ne_of_lt hepsilon_one]

private theorem higham19_problem19_10_cgs_stage3_norm
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    fl_norm2 (higham19Problem19_10FP epsilon hepsilon) 4
        (flCGSResidual (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon)
          (higham19Problem19_10CGSStage2Q epsilon)
          (higham19Problem19_10CGSStage3Roff epsilon) (2 : Fin 3)) =
      epsilon * Real.sqrt 2 := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hepsilon_sq_ne_one : epsilon ^ 2 ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hepsilon_mul_self_ne_one : epsilon * epsilon ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hres :
      flCGSResidual (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon)
          (higham19Problem19_10CGSStage2Q epsilon)
          (higham19Problem19_10CGSStage3Roff epsilon) (2 : Fin 3) =
        higham19Problem19_10CGSStage3Residual epsilon := by
    funext i
    exact higham19_problem19_10_cgs_stage3_residual_entry
      epsilon hepsilon hepsilon_one i
  rw [hres]
  have hsqrt : Real.sqrt (2 * epsilon ^ 2) =
      epsilon * Real.sqrt 2 := by
    rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2),
      Real.sqrt_sq_eq_abs, abs_of_pos hepsilon]
    ring
  have hsq :
      fl_norm2Sq (higham19Problem19_10FP epsilon hepsilon) 4
          (higham19Problem19_10CGSStage3Residual epsilon) =
        2 * epsilon ^ 2 := by
    norm_num [fl_norm2Sq, fl_dotProduct, Fin.foldl_succ,
      higham19Problem19_10FP, higham20CrossProductExampleFP,
      higham19Problem19_10CGSStage3Residual, pow_two,
      hepsilon_ne, hepsilon_sq_ne_one, hepsilon_mul_self_ne_one]
    ring
  rw [fl_norm2, hsq]
  exact hsqrt

private theorem higham19_problem19_10_cgs_step_two
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flCGSStep (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (higham19Problem19_10CGSStage2Q epsilon,
          higham19Problem19_10CGSStage2R epsilon) (2 : Fin 3) =
      (higham19Problem19_10QCGS epsilon,
        higham19Problem19_10CGSStage3R epsilon) := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hsqrt_two_ne : Real.sqrt (2 : Real) ≠ 0 := by positivity
  simp only [flCGSStep]
  rw [higham19_problem19_10_cgs_stage3_roff epsilon hepsilon]
  rw [higham19_problem19_10_cgs_stage3_norm
    epsilon hepsilon hepsilon_one]
  apply Prod.ext
  · funext i j
    change
      (if j = (2 : Fin 3) then
          (higham19Problem19_10FP epsilon hepsilon).fl_div
            (flCGSResidualEntry
              (higham19Problem19_10FP epsilon hepsilon)
              (higham19Problem19_10Lauchli epsilon)
              (higham19Problem19_10CGSStage2Q epsilon)
              (higham19Problem19_10CGSStage3Roff epsilon)
              i (2 : Fin 3)) (epsilon * Real.sqrt 2)
        else higham19Problem19_10CGSStage2Q epsilon i j) =
          higham19Problem19_10QCGS epsilon i j
    rw [higham19_problem19_10_cgs_stage3_residual_entry
      epsilon hepsilon hepsilon_one i]
    fin_cases i <;> fin_cases j <;>
      norm_num [higham19Problem19_10FP,
        higham20CrossProductExampleFP,
        higham19Problem19_10CGSStage2Q,
        higham19Problem19_10QCGS,
        higham19Problem19_10CGSStage3Residual]
    all_goals (try field_simp [hepsilon_ne, hsqrt_two_ne])
    all_goals simp_all
  · funext i j
    change
      (if j = (2 : Fin 3) then
          if i = (2 : Fin 3) then epsilon * Real.sqrt 2
          else higham19Problem19_10CGSStage3Roff epsilon i j
        else higham19Problem19_10CGSStage2R epsilon i j) =
          higham19Problem19_10CGSStage3R epsilon i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham19Problem19_10CGSStage2R,
        higham19Problem19_10CGSStage3Roff,
        higham19Problem19_10CGSStage3R]
    all_goals simp_all

private theorem higham19_problem19_10_cgs_stage1
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flCGSAux (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon) 1 =
      (higham19Problem19_10CGSStage1Q epsilon,
        higham19Problem19_10CGSStage1R) := by
  change
    flCGSStep (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        ((fun _ _ => 0), (fun _ _ => 0)) (0 : Fin 3) = _
  exact higham19_problem19_10_cgs_step_zero epsilon hepsilon

private theorem higham19_problem19_10_cgs_stage2
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flCGSAux (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon) 2 =
      (higham19Problem19_10CGSStage2Q epsilon,
        higham19Problem19_10CGSStage2R epsilon) := by
  change
    flCGSStep (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (flCGSAux (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon) 1) (1 : Fin 3) = _
  rw [higham19_problem19_10_cgs_stage1 epsilon hepsilon]
  exact higham19_problem19_10_cgs_step_one
    epsilon hepsilon hepsilon_one

private theorem higham19_problem19_10_cgs_stage3
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flCGSAux (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon) 3 =
      (higham19Problem19_10QCGS epsilon,
        higham19Problem19_10CGSStage3R epsilon) := by
  change
    flCGSStep (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon)
        (flCGSAux (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon) 2) (2 : Fin 3) = _
  rw [higham19_problem19_10_cgs_stage2
    epsilon hepsilon hepsilon_one]
  exact higham19_problem19_10_cgs_step_two
    epsilon hepsilon hepsilon_one

/-- The literal rounded CGS executor produces the Appendix-A matrix. -/
theorem higham19_problem19_10_cgs_executor
    (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    fl_classicalGramSchmidtQ (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon) =
      higham19Problem19_10QCGS epsilon := by
  change
    (flCGSAux (higham19Problem19_10FP epsilon hepsilon)
      (higham19Problem19_10Lauchli epsilon) 3).1 = _
  rw [higham19_problem19_10_cgs_stage3
    epsilon hepsilon hepsilon_one]

/-! Staged certificates for the literal MGS executor. -/

private def higham19Problem19_10MGSStage0 (epsilon : Real) :
    Fin 3 -> Fin 4 -> Real :=
  !![(1 : Real), epsilon, 0, 0;
     1, 0, epsilon, 0;
     1, 0, 0, epsilon]

private def higham19Problem19_10MGSQ0 (epsilon : Real) :
    Fin 4 -> Real :=
  ![(1 : Real), epsilon, 0, 0]

private def higham19Problem19_10MGSStage1 (epsilon : Real) :
    Fin 3 -> Fin 4 -> Real :=
  !![(1 : Real), epsilon, 0, 0;
     0, -epsilon, epsilon, 0;
     0, -epsilon, 0, epsilon]

private def higham19Problem19_10MGSQ1 : Fin 4 -> Real :=
  ![(0 : Real), -(1 / Real.sqrt 2), 1 / Real.sqrt 2, 0]

private def higham19Problem19_10MGSStage2 (epsilon : Real) :
    Fin 3 -> Fin 4 -> Real :=
  !![(1 : Real), epsilon, 0, 0;
     0, -epsilon, epsilon, 0;
     0, -(epsilon / 2), -(epsilon / 2), epsilon]

private def higham19Problem19_10MGSQ2 : Fin 4 -> Real :=
  ![(0 : Real), -(1 / Real.sqrt 6), -(1 / Real.sqrt 6),
    Real.sqrt (2 / 3)]

private theorem higham19_problem19_10_mgs_vectors_zero
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flMGSVectors (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon) 0 =
      higham19Problem19_10MGSStage0 epsilon := by
  funext j i
  fin_cases j <;> fin_cases i <;>
    norm_num [flMGSVectors, gsColumn,
      higham19Problem19_10Lauchli, higham19Problem19_10MGSStage0]

private theorem higham19_problem19_10_mgs_norm_zero
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flMGSColumnNorm (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage0 epsilon) (0 : Fin 3) = 1 := by
  have hcol :
      higham19Problem19_10MGSStage0 epsilon (0 : Fin 3) =
        fun i => higham19Problem19_10Lauchli epsilon i (0 : Fin 3) := by
    funext i
    fin_cases i <;>
      norm_num [higham19Problem19_10MGSStage0,
        higham19Problem19_10Lauchli]
  have hres :
      flCGSResidual (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon)
          (fun _ _ => 0) (fun _ _ => 0) (0 : Fin 3) =
        fun i => higham19Problem19_10Lauchli epsilon i (0 : Fin 3) := by
    funext i
    exact higham19_problem19_10_cgs_residual_entry_zero epsilon hepsilon i
  rw [flMGSColumnNorm, hcol, ← hres]
  exact higham19_problem19_10_cgs_norm_zero epsilon hepsilon

private theorem higham19_problem19_10_mgs_normalized_zero
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flMGSNormalizedColumn (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage0 epsilon) (0 : Fin 3) =
      higham19Problem19_10MGSQ0 epsilon := by
  funext i
  rw [flMGSNormalizedColumn,
    higham19_problem19_10_mgs_norm_zero epsilon hepsilon]
  fin_cases i <;>
    norm_num [higham19Problem19_10FP,
      higham20CrossProductExampleFP,
      higham19Problem19_10MGSStage0, higham19Problem19_10MGSQ0]
  all_goals rfl

private theorem higham19_problem19_10_mgs_projection_zero_one
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flMGSProjection (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage0 epsilon)
        (0 : Fin 3) (1 : Fin 3) = 1 := by
  rw [flMGSProjection,
    higham19_problem19_10_mgs_normalized_zero epsilon hepsilon]
  norm_num [fl_dotProduct, Fin.foldl_succ,
    higham19Problem19_10FP, higham20CrossProductExampleFP,
    higham19Problem19_10MGSStage0, higham19Problem19_10MGSQ0]

private theorem higham19_problem19_10_mgs_projection_zero_two
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flMGSProjection (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage0 epsilon)
        (0 : Fin 3) (2 : Fin 3) = 1 := by
  rw [flMGSProjection,
    higham19_problem19_10_mgs_normalized_zero epsilon hepsilon]
  norm_num [fl_dotProduct, Fin.foldl_succ,
    higham19Problem19_10FP, higham20CrossProductExampleFP,
    higham19Problem19_10MGSStage0, higham19Problem19_10MGSQ0]

private theorem higham19_problem19_10_mgs_projection_zero_of_pos
    (epsilon : Real) (hepsilon : 0 < epsilon) {j : Fin 3}
    (hj : (0 : Fin 3) < j) :
    flMGSProjection (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage0 epsilon) (0 : Fin 3) j = 1 := by
  fin_cases j
  · exact (lt_irrefl (0 : Fin 3) hj).elim
  · exact higham19_problem19_10_mgs_projection_zero_one epsilon hepsilon
  · exact higham19_problem19_10_mgs_projection_zero_two epsilon hepsilon

private theorem higham19_problem19_10_mgs_step_zero
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flMGSStep (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage0 epsilon) (0 : Fin 3) =
      higham19Problem19_10MGSStage1 epsilon := by
  simp only [flMGSStep]
  rw [higham19_problem19_10_mgs_normalized_zero epsilon hepsilon]
  funext j i
  by_cases hj : (0 : Fin 3) < j
  · rw [dif_pos hj,
      higham19_problem19_10_mgs_projection_zero_of_pos
        epsilon hepsilon hj]
    fin_cases j <;> fin_cases i
    all_goals (try norm_num at hj)
    all_goals norm_num [higham19Problem19_10FP,
      higham20CrossProductExampleFP,
      higham19Problem19_10MGSStage0,
      higham19Problem19_10MGSQ0,
      higham19Problem19_10MGSStage1]
    all_goals rfl
  · rw [dif_neg hj]
    fin_cases j <;> fin_cases i
    all_goals (try norm_num at hj)
    all_goals norm_num [higham19Problem19_10MGSStage0,
      higham19Problem19_10MGSStage1]

private theorem higham19_problem19_10_mgs_vectors_one
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    flMGSVectors (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon) 1 =
      higham19Problem19_10MGSStage1 epsilon := by
  change
    flMGSStep (higham19Problem19_10FP epsilon hepsilon)
        (flMGSVectors (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon) 0) (0 : Fin 3) =
      higham19Problem19_10MGSStage1 epsilon
  rw [higham19_problem19_10_mgs_vectors_zero epsilon hepsilon]
  exact higham19_problem19_10_mgs_step_zero epsilon hepsilon

private theorem higham19_problem19_10_mgs_norm_one
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flMGSColumnNorm (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage1 epsilon) (1 : Fin 3) =
      epsilon * Real.sqrt 2 := by
  have hcol :
      higham19Problem19_10MGSStage1 epsilon (1 : Fin 3) =
        higham19Problem19_10CGSStage2Residual epsilon := by
    funext i
    fin_cases i <;>
      norm_num [higham19Problem19_10MGSStage1,
        higham19Problem19_10CGSStage2Residual]
  have hres :
      flCGSResidual (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon)
          (higham19Problem19_10CGSStage1Q epsilon)
          higham19Problem19_10CGSStage2Roff (1 : Fin 3) =
        higham19Problem19_10CGSStage2Residual epsilon := by
    funext i
    exact higham19_problem19_10_cgs_stage2_residual_entry
      epsilon hepsilon hepsilon_one i
  rw [flMGSColumnNorm, hcol, ← hres]
  exact higham19_problem19_10_cgs_stage2_norm
    epsilon hepsilon hepsilon_one

private theorem higham19_problem19_10_mgs_normalized_one
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flMGSNormalizedColumn (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage1 epsilon) (1 : Fin 3) =
      higham19Problem19_10MGSQ1 := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hsqrt_two_ne : Real.sqrt (2 : Real) ≠ 0 := by positivity
  funext i
  rw [flMGSNormalizedColumn,
    higham19_problem19_10_mgs_norm_one
      epsilon hepsilon hepsilon_one]
  fin_cases i <;>
    norm_num [higham19Problem19_10FP,
      higham20CrossProductExampleFP,
      higham19Problem19_10MGSStage1,
      higham19Problem19_10MGSQ1]
  all_goals field_simp [hepsilon_ne, hsqrt_two_ne]

private theorem higham19_problem19_10_mgs_projection_one_two
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flMGSProjection (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage1 epsilon)
        (1 : Fin 3) (2 : Fin 3) = epsilon / Real.sqrt 2 := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hepsilon_sq_ne : epsilon ^ 2 ≠ 0 := pow_ne_zero 2 hepsilon_ne
  have hzero_sq : (0 : Real) ≠ epsilon ^ 2 := hepsilon_sq_ne.symm
  rw [flMGSProjection,
    higham19_problem19_10_mgs_normalized_one
      epsilon hepsilon hepsilon_one]
  norm_num [fl_dotProduct, Fin.foldl_succ,
    higham19Problem19_10FP, higham20CrossProductExampleFP,
    higham19Problem19_10MGSStage1,
    higham19Problem19_10MGSQ1, hepsilon_ne]
  simp [hzero_sq, div_eq_mul_inv, mul_comm]

private theorem higham19_problem19_10_mgs_step_one
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flMGSStep (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage1 epsilon) (1 : Fin 3) =
      higham19Problem19_10MGSStage2 epsilon := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hsqrt_two_ne : Real.sqrt (2 : Real) ≠ 0 := by positivity
  simp only [flMGSStep]
  rw [higham19_problem19_10_mgs_normalized_one
    epsilon hepsilon hepsilon_one]
  funext j i
  by_cases hj : (1 : Fin 3) < j
  · rw [dif_pos hj]
    have hj_two : j = (2 : Fin 3) := by
      fin_cases j
      · norm_num at hj
      · norm_num at hj
      · rfl
    subst j
    rw [higham19_problem19_10_mgs_projection_one_two
      epsilon hepsilon hepsilon_one]
    fin_cases i <;>
      norm_num [higham19Problem19_10FP,
        higham20CrossProductExampleFP,
        higham19Problem19_10MGSStage1,
        higham19Problem19_10MGSQ1,
        higham19Problem19_10MGSStage2]
    all_goals (try field_simp [hsqrt_two_ne])
    all_goals (try nlinarith
      [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)])
    all_goals rfl
  · rw [dif_neg hj]
    have hj_ne_two : j ≠ (2 : Fin 3) := by
      intro hj_two
      subst j
      exact hj (by decide)
    fin_cases j <;> fin_cases i
    all_goals (try simp at hj_ne_two)
    all_goals norm_num [higham19Problem19_10MGSStage1,
      higham19Problem19_10MGSStage2]

private theorem higham19_problem19_10_mgs_vectors_two
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flMGSVectors (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon) 2 =
      higham19Problem19_10MGSStage2 epsilon := by
  change
    flMGSStep (higham19Problem19_10FP epsilon hepsilon)
        (flMGSVectors (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon) 1) (1 : Fin 3) =
      higham19Problem19_10MGSStage2 epsilon
  rw [higham19_problem19_10_mgs_vectors_one epsilon hepsilon]
  exact higham19_problem19_10_mgs_step_one
    epsilon hepsilon hepsilon_one

private theorem higham19_problem19_10_mgs_norm_two
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flMGSColumnNorm (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage2 epsilon) (2 : Fin 3) =
      epsilon * Real.sqrt (3 / 2) := by
  have hepsilon_sq_lt_one : epsilon ^ 2 < 1 := by
    nlinarith [sq_nonneg (epsilon - 1), sq_nonneg epsilon]
  have hquarter_ne_one : epsilon ^ 2 / 4 ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hhalf_ne_one : epsilon ^ 2 / 2 ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hquarter_mul_ne_one : epsilon ^ 2 * (1 / 4 : Real) ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hhalf_mul_ne_one : epsilon ^ 2 * (1 / 2 : Real) ≠ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hsq :
      fl_norm2Sq (higham19Problem19_10FP epsilon hepsilon) 4
          (higham19Problem19_10MGSStage2 epsilon (2 : Fin 3)) =
        (3 / 2 : Real) * epsilon ^ 2 := by
    norm_num [fl_norm2Sq, fl_dotProduct, Fin.foldl_succ,
      higham19Problem19_10FP, higham20CrossProductExampleFP,
      higham19Problem19_10MGSStage2, pow_two,
      hquarter_ne_one, hhalf_ne_one]
    have hantecedent :
        epsilon ^ 2 * (1 / 4 : Real) = 1 →
          ¬ epsilon ^ 2 * (1 / 4 : Real) = epsilon ^ 2 := by
      intro hquarter_eq_one
      exact (hquarter_mul_ne_one hquarter_eq_one).elim
    have houter :
        ¬ ((epsilon ^ 2 * (1 / 4 : Real) = 1 →
              ¬ epsilon ^ 2 * (1 / 4 : Real) = epsilon ^ 2) →
            epsilon ^ 2 * (1 / 2 : Real) = 1) := by
      intro h
      exact hhalf_mul_ne_one (h hantecedent)
    have hinner :
        ¬ (epsilon ^ 2 * (1 / 4 : Real) = 1 ∧
          epsilon ^ 2 * (1 / 4 : Real) = epsilon ^ 2) := by
      intro h
      exact hquarter_mul_ne_one h.1
    ring_nf
    rw [if_neg houter, if_neg hinner]
    ring
  have hsqrt :
      Real.sqrt ((3 / 2 : Real) * epsilon ^ 2) =
        epsilon * Real.sqrt (3 / 2) := by
    rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 3 / 2),
      Real.sqrt_sq_eq_abs, abs_of_pos hepsilon]
    ring
  rw [flMGSColumnNorm, fl_norm2, hsq]
  exact hsqrt

private theorem higham19_problem19_10_mgs_normalized_two
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1) :
    flMGSNormalizedColumn (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10MGSStage2 epsilon) (2 : Fin 3) =
      higham19Problem19_10MGSQ2 := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hsqrt_three_halves_pos :
      0 < Real.sqrt (3 / 2 : Real) := by positivity
  have hsqrt_three_halves_ne :
      Real.sqrt (3 / 2 : Real) ≠ 0 :=
    ne_of_gt hsqrt_three_halves_pos
  have hsqrt_six_eq :
      Real.sqrt (6 : Real) = 2 * Real.sqrt (3 / 2 : Real) := by
    calc
      Real.sqrt (6 : Real) =
          Real.sqrt ((4 : Real) * (3 / 2 : Real)) := by
        congr 1
        norm_num
      _ = Real.sqrt (4 : Real) * Real.sqrt (3 / 2 : Real) := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
      _ = 2 * Real.sqrt (3 / 2 : Real) := by
        rw [show Real.sqrt (4 : Real) = 2 by
          rw [show (4 : Real) = 2 ^ 2 by norm_num,
            Real.sqrt_sq_eq_abs]
          norm_num]
  have hsqrt_two_mul_three_halves :
      Real.sqrt (2 : Real) * Real.sqrt (3 / 2 : Real) =
        Real.sqrt 3 := by
    calc
      Real.sqrt (2 : Real) * Real.sqrt (3 / 2 : Real) =
          Real.sqrt ((2 : Real) * (3 / 2 : Real)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]
      _ = Real.sqrt 3 := by
        congr 1
        norm_num
  have hsqrt_product :
      Real.sqrt (3 / 2 : Real) * Real.sqrt (2 / 3 : Real) = 1 := by
    calc
      Real.sqrt (3 / 2 : Real) * Real.sqrt (2 / 3 : Real) =
          Real.sqrt ((3 / 2 : Real) * (2 / 3 : Real)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 3 / 2)]
      _ = 1 := by
        rw [show (3 / 2 : Real) * (2 / 3 : Real) = 1 by norm_num,
          Real.sqrt_one]
  funext i
  rw [flMGSNormalizedColumn,
    higham19_problem19_10_mgs_norm_two
      epsilon hepsilon hepsilon_one]
  fin_cases i
  · norm_num [higham19Problem19_10FP,
      higham20CrossProductExampleFP,
      higham19Problem19_10MGSStage2,
      higham19Problem19_10MGSQ2]
  · norm_num [higham19Problem19_10FP,
      higham20CrossProductExampleFP,
      higham19Problem19_10MGSStage2,
      higham19Problem19_10MGSQ2]
    rw [hsqrt_six_eq]
    field_simp [hepsilon_ne, hsqrt_three_halves_ne]
    rw [hsqrt_two_mul_three_halves]
  · norm_num [higham19Problem19_10FP,
      higham20CrossProductExampleFP,
      higham19Problem19_10MGSStage2,
      higham19Problem19_10MGSQ2]
    rw [hsqrt_six_eq]
    field_simp [hepsilon_ne, hsqrt_three_halves_ne]
    rw [hsqrt_two_mul_three_halves]
  · norm_num [higham19Problem19_10FP,
      higham20CrossProductExampleFP,
      higham19Problem19_10MGSStage2,
      higham19Problem19_10MGSQ2]
    field_simp [hepsilon_ne, hsqrt_three_halves_ne]

/-- The literal rounded MGS executor produces the second Appendix-A matrix
under the same explicit source trace. -/
theorem higham19_problem19_10_mgs_executor
    (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    fl_modifiedGramSchmidtQ (higham19Problem19_10FP epsilon hepsilon)
        (higham19Problem19_10Lauchli epsilon) =
      higham19Problem19_10QMGS epsilon := by
  funext i j
  fin_cases j
  · change
      flMGSNormalizedColumn (higham19Problem19_10FP epsilon hepsilon)
          (flMGSVectors (higham19Problem19_10FP epsilon hepsilon)
            (higham19Problem19_10Lauchli epsilon) 0) (0 : Fin 3) i =
        higham19Problem19_10QMGS epsilon i (0 : Fin 3)
    rw [higham19_problem19_10_mgs_vectors_zero epsilon hepsilon,
      higham19_problem19_10_mgs_normalized_zero epsilon hepsilon]
    fin_cases i <;>
      norm_num [higham19Problem19_10MGSQ0,
        higham19Problem19_10QMGS]
  · change
      flMGSNormalizedColumn (higham19Problem19_10FP epsilon hepsilon)
          (flMGSVectors (higham19Problem19_10FP epsilon hepsilon)
            (higham19Problem19_10Lauchli epsilon) 1) (1 : Fin 3) i =
        higham19Problem19_10QMGS epsilon i (1 : Fin 3)
    rw [higham19_problem19_10_mgs_vectors_one epsilon hepsilon,
      higham19_problem19_10_mgs_normalized_one
        epsilon hepsilon hepsilon_one]
    fin_cases i <;>
      norm_num [higham19Problem19_10MGSQ1,
        higham19Problem19_10QMGS]
  · change
      flMGSNormalizedColumn (higham19Problem19_10FP epsilon hepsilon)
          (flMGSVectors (higham19Problem19_10FP epsilon hepsilon)
            (higham19Problem19_10Lauchli epsilon) 2) (2 : Fin 3) i =
        higham19Problem19_10QMGS epsilon i (2 : Fin 3)
    rw [higham19_problem19_10_mgs_vectors_two
        epsilon hepsilon hepsilon_one,
      higham19_problem19_10_mgs_normalized_two
        epsilon hepsilon hepsilon_one]
    fin_cases i <;>
      norm_num [higham19Problem19_10MGSQ2,
        higham19Problem19_10QMGS]

/-- Actual-executor form of the Appendix's order-one CGS defect. -/
theorem higham19_problem19_10_cgs_executor_defect
    (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    higham19Problem19_10ColumnDot
        (fl_classicalGramSchmidtQ
          (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon))
        (1 : Fin 3) (2 : Fin 3) = 1 / 2 := by
  rw [higham19_problem19_10_cgs_executor epsilon hepsilon hepsilon_one]
  exact higham19_problem19_10_cgs_q2_dot_q3 epsilon

/-- Actual-executor form of all three MGS orthogonality estimates. -/
theorem higham19_problem19_10_mgs_executor_pairwise_bounds
    (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    |higham19Problem19_10ColumnDot
        (fl_modifiedGramSchmidtQ
          (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon))
        (0 : Fin 3) (1 : Fin 3)| = epsilon / Real.sqrt 2 ∧
    |higham19Problem19_10ColumnDot
        (fl_modifiedGramSchmidtQ
          (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon))
        (0 : Fin 3) (2 : Fin 3)| ≤ epsilon / Real.sqrt 2 ∧
    |higham19Problem19_10ColumnDot
        (fl_modifiedGramSchmidtQ
          (higham19Problem19_10FP epsilon hepsilon)
          (higham19Problem19_10Lauchli epsilon))
        (1 : Fin 3) (2 : Fin 3)| = 0 := by
  rw [higham19_problem19_10_mgs_executor epsilon hepsilon hepsilon_one]
  exact higham19_problem19_10_mgs_pairwise_bounds epsilon hepsilon.le

/-- Fully operational no-uniform-linear-bound endpoint: for every fixed
coefficient, an actual rounded CGS execution has defect larger than that
coefficient times the source `kappa_2(A)u` quantity. -/
theorem higham19_problem19_10_no_uniform_linear_cgs_executor_bound
    (C : Real) (hC : 0 ≤ C) :
    ∃ epsilon : Real, ∃ hepsilon : 0 < epsilon,
      epsilon < 1 ∧
      C * (higham19Problem19_10SourceKappa epsilon *
          (higham19Problem19_10FP epsilon hepsilon).u) <
        |higham19Problem19_10ColumnDot
          (fl_classicalGramSchmidtQ
            (higham19Problem19_10FP epsilon hepsilon)
            (higham19Problem19_10Lauchli epsilon))
          (1 : Fin 3) (2 : Fin 3)| := by
  obtain ⟨epsilon, hepsilon, hepsilon_one, hsmall⟩ :=
    higham19_problem19_10_no_uniform_linear_cgs_bound C hC
  refine ⟨epsilon, hepsilon, hepsilon_one, ?_⟩
  rw [higham19_problem19_10_cgs_executor_defect
    epsilon hepsilon hepsilon_one, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
  exact hsmall

/-!
## Why the single rounding event is not a complete abstract-model premise

The book's hand calculation also treats the divisions used for normalization
as the displayed exact quotients.  `FPModel` permits an independent relative
error in every such division, so `fl(1+epsilon^2)=1` alone cannot imply the
displayed matrix.  The following pair uses the same `u=1`, the same Lauchli
input with `epsilon=1/2`, and the same sensitive-addition event; the second
model changes only division by the admissible relative factor two.
-/

noncomputable def higham19Problem19_10ExactDivWitnessFP : FPModel :=
  higham20CrossProductExampleFP (1 / 2) 1 (by norm_num)

noncomputable def higham19Problem19_10DoubledDivWitnessFP : FPModel where
  u := 1
  u_nonneg := by norm_num
  fl_add := higham19Problem19_10ExactDivWitnessFP.fl_add
  fl_sub := higham19Problem19_10ExactDivWitnessFP.fl_sub
  fl_mul := higham19Problem19_10ExactDivWitnessFP.fl_mul
  fl_div := fun x y => 2 * (x / y)
  fl_sqrt := higham19Problem19_10ExactDivWitnessFP.fl_sqrt
  fl_add_zero := higham19Problem19_10ExactDivWitnessFP.fl_add_zero
  model_add := higham19Problem19_10ExactDivWitnessFP.model_add
  model_sub := higham19Problem19_10ExactDivWitnessFP.model_sub
  model_mul := higham19Problem19_10ExactDivWitnessFP.model_mul
  model_div := by
    intro x y hy
    refine ⟨1, by norm_num, ?_⟩
    field_simp [hy]
    ring
  model_sqrt := higham19Problem19_10ExactDivWitnessFP.model_sqrt

/-- A second model-strength witness for the Appendix sentence
`fl(1+epsilon^2)=1 implies epsilon ≤ sqrt u`.  That implication uses spacing
properties of a round-to-nearest format; it is not a consequence of the
relative-error `FPModel` contract alone. -/
noncomputable def higham19Problem19_10HalfUnitSensitiveAddFP : FPModel where
  u := 1 / 2
  u_nonneg := by norm_num
  fl_add := fun x y => if x = 1 ∧ y = 1 then 1 else x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; simp
  model_add := by
    intro x y
    by_cases h : x = 1 ∧ y = 1
    · refine ⟨-(1 / 2), by norm_num, ?_⟩
      norm_num [h]
      rfl
    · refine ⟨0, by norm_num, ?_⟩
      simp [h]
  model_sub := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_mul := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_div := by
    intro x y _hy
    refine ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, by ring⟩

theorem higham19_problem19_10_epsilon_le_sqrt_u_not_from_abstract_event :
    ∃ fp : FPModel, ∃ epsilon : Real,
      fp.fl_add 1 (fp.fl_mul epsilon epsilon) = 1 ∧
      ¬ epsilon ≤ Real.sqrt fp.u := by
  refine ⟨higham19Problem19_10HalfUnitSensitiveAddFP, 1, ?_, ?_⟩
  · norm_num [higham19Problem19_10HalfUnitSensitiveAddFP]
  · intro h
    have hsqrt_sq : Real.sqrt (1 / 2 : Real) ^ 2 = 1 / 2 :=
      Real.sq_sqrt (by norm_num)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 / 2 : Real) := Real.sqrt_nonneg _
    change (1 : Real) ≤ Real.sqrt (1 / 2) at h
    nlinarith

theorem higham19_problem19_10_witness_rounding_events :
    higham19Problem19_10ExactDivWitnessFP.fl_add 1
        (higham19Problem19_10ExactDivWitnessFP.fl_mul (1 / 2) (1 / 2)) = 1 ∧
    higham19Problem19_10DoubledDivWitnessFP.fl_add 1
        (higham19Problem19_10DoubledDivWitnessFP.fl_mul (1 / 2) (1 / 2)) = 1 := by
  norm_num [higham19Problem19_10ExactDivWitnessFP,
    higham19Problem19_10DoubledDivWitnessFP,
    higham20CrossProductExampleFP]

private theorem higham19_problem19_10_witness_roff_zero
    (fp : FPModel) :
    flCGSRoff fp (higham19Problem19_10Lauchli (1 / 2))
        (fun _ _ => 0) (fun _ _ => 0) (0 : Fin 3) =
      fun _ _ => 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flCGSRoff]

private theorem higham19_problem19_10_exact_witness_residual_entry_zero
    (i : Fin 4) :
    flCGSResidualEntry higham19Problem19_10ExactDivWitnessFP
        (higham19Problem19_10Lauchli (1 / 2))
        (fun _ _ => 0) (fun _ _ => 0) i (0 : Fin 3) =
      higham19Problem19_10Lauchli (1 / 2) i (0 : Fin 3) := by
  fin_cases i <;>
    norm_num [flCGSResidualEntry, flCGSCoeff, flCGSRow,
      fl_dotProduct, Fin.foldl_succ,
      higham19Problem19_10ExactDivWitnessFP,
      higham20CrossProductExampleFP, higham19Problem19_10Lauchli]

private theorem higham19_problem19_10_exact_witness_norm_zero :
    fl_norm2 higham19Problem19_10ExactDivWitnessFP 4
        (flCGSResidual higham19Problem19_10ExactDivWitnessFP
          (higham19Problem19_10Lauchli (1 / 2))
          (fun _ _ => 0) (fun _ _ => 0) (0 : Fin 3)) = 1 := by
  have hres :
      flCGSResidual higham19Problem19_10ExactDivWitnessFP
          (higham19Problem19_10Lauchli (1 / 2))
          (fun _ _ => 0) (fun _ _ => 0) (0 : Fin 3) =
        fun i => higham19Problem19_10Lauchli (1 / 2) i (0 : Fin 3) := by
    funext i
    exact higham19_problem19_10_exact_witness_residual_entry_zero i
  rw [hres]
  norm_num [fl_norm2, fl_norm2Sq, fl_dotProduct, Fin.foldl_succ,
    higham19Problem19_10ExactDivWitnessFP,
    higham20CrossProductExampleFP, higham19Problem19_10Lauchli]

private theorem higham19_problem19_10_doubled_witness_residual_entry_zero
    (i : Fin 4) :
    flCGSResidualEntry higham19Problem19_10DoubledDivWitnessFP
        (higham19Problem19_10Lauchli (1 / 2))
        (fun _ _ => 0) (fun _ _ => 0) i (0 : Fin 3) =
      higham19Problem19_10Lauchli (1 / 2) i (0 : Fin 3) := by
  fin_cases i <;>
    norm_num [flCGSResidualEntry, flCGSCoeff, flCGSRow,
      fl_dotProduct, Fin.foldl_succ,
      higham19Problem19_10DoubledDivWitnessFP,
      higham19Problem19_10ExactDivWitnessFP,
      higham20CrossProductExampleFP, higham19Problem19_10Lauchli]

private theorem higham19_problem19_10_doubled_witness_norm_zero :
    fl_norm2 higham19Problem19_10DoubledDivWitnessFP 4
        (flCGSResidual higham19Problem19_10DoubledDivWitnessFP
          (higham19Problem19_10Lauchli (1 / 2))
          (fun _ _ => 0) (fun _ _ => 0) (0 : Fin 3)) = 1 := by
  have hres :
      flCGSResidual higham19Problem19_10DoubledDivWitnessFP
          (higham19Problem19_10Lauchli (1 / 2))
          (fun _ _ => 0) (fun _ _ => 0) (0 : Fin 3) =
        fun i => higham19Problem19_10Lauchli (1 / 2) i (0 : Fin 3) := by
    funext i
    exact higham19_problem19_10_doubled_witness_residual_entry_zero i
  rw [hres]
  norm_num [fl_norm2, fl_norm2Sq, fl_dotProduct, Fin.foldl_succ,
    higham19Problem19_10DoubledDivWitnessFP,
    higham19Problem19_10ExactDivWitnessFP,
    higham20CrossProductExampleFP, higham19Problem19_10Lauchli]

theorem higham19_problem19_10_exactDivWitness_first_entry :
    fl_classicalGramSchmidtQ higham19Problem19_10ExactDivWitnessFP
        (higham19Problem19_10Lauchli (1 / 2)) (0 : Fin 4) (0 : Fin 3) = 1 := by
  change
    (flCGSAux higham19Problem19_10ExactDivWitnessFP
      (higham19Problem19_10Lauchli (1 / 2)) 3).1
        (0 : Fin 4) (0 : Fin 3) = 1
  rw [flCGSAux_Q_stable higham19Problem19_10ExactDivWitnessFP
    (higham19Problem19_10Lauchli (1 / 2)) 1
    (0 : Fin 4) (0 : Fin 3) (by norm_num) 3 (by norm_num)]
  change
    (flCGSStep higham19Problem19_10ExactDivWitnessFP
      (higham19Problem19_10Lauchli (1 / 2))
      ((fun _ _ => 0), (fun _ _ => 0)) (0 : Fin 3)).1
        (0 : Fin 4) (0 : Fin 3) = 1
  simp only [flCGSStep]
  rw [higham19_problem19_10_witness_roff_zero,
    higham19_problem19_10_exact_witness_norm_zero,
    higham19_problem19_10_exact_witness_residual_entry_zero]
  norm_num [higham19Problem19_10ExactDivWitnessFP,
    higham20CrossProductExampleFP, higham19Problem19_10Lauchli]
  rfl

theorem higham19_problem19_10_doubledDivWitness_first_entry :
    fl_classicalGramSchmidtQ higham19Problem19_10DoubledDivWitnessFP
        (higham19Problem19_10Lauchli (1 / 2)) (0 : Fin 4) (0 : Fin 3) = 2 := by
  change
    (flCGSAux higham19Problem19_10DoubledDivWitnessFP
      (higham19Problem19_10Lauchli (1 / 2)) 3).1
        (0 : Fin 4) (0 : Fin 3) = 2
  rw [flCGSAux_Q_stable higham19Problem19_10DoubledDivWitnessFP
    (higham19Problem19_10Lauchli (1 / 2)) 1
    (0 : Fin 4) (0 : Fin 3) (by norm_num) 3 (by norm_num)]
  change
    (flCGSStep higham19Problem19_10DoubledDivWitnessFP
      (higham19Problem19_10Lauchli (1 / 2))
      ((fun _ _ => 0), (fun _ _ => 0)) (0 : Fin 3)).1
        (0 : Fin 4) (0 : Fin 3) = 2
  simp only [flCGSStep]
  rw [higham19_problem19_10_witness_roff_zero,
    higham19_problem19_10_doubled_witness_norm_zero,
    higham19_problem19_10_doubled_witness_residual_entry_zero]
  norm_num [higham19Problem19_10DoubledDivWitnessFP,
    higham19Problem19_10ExactDivWitnessFP,
    higham20CrossProductExampleFP, higham19Problem19_10Lauchli]
  rfl

/-- Formal source-interface discrepancy: equal unit roundoff and the printed
rounding event do not determine the rounded CGS output in the abstract model. -/
theorem higham19_problem19_10_rounding_event_does_not_determine_cgs :
    ∃ fp fp' : FPModel,
      fp.u = fp'.u ∧
      fp.fl_add 1 (fp.fl_mul (1 / 2) (1 / 2)) = 1 ∧
      fp'.fl_add 1 (fp'.fl_mul (1 / 2) (1 / 2)) = 1 ∧
      fl_classicalGramSchmidtQ fp
          (higham19Problem19_10Lauchli (1 / 2)) ≠
        fl_classicalGramSchmidtQ fp'
          (higham19Problem19_10Lauchli (1 / 2)) := by
  refine ⟨higham19Problem19_10ExactDivWitnessFP,
    higham19Problem19_10DoubledDivWitnessFP, rfl,
    higham19_problem19_10_witness_rounding_events.1,
    higham19_problem19_10_witness_rounding_events.2, ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 4)) (0 : Fin 3)
  rw [higham19_problem19_10_exactDivWitness_first_entry,
    higham19_problem19_10_doubledDivWitness_first_entry] at h00
  norm_num at h00

end

end NumStability
